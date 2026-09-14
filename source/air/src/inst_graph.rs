//! Queries over an instantiation graph: which quantifiers instantiate each
//! other in a cycle, which cost the most, how instantiation grows, and how one
//! instantiation descends from another.
//!
//! The graph comes either from a z3 trace, through smt-scope
//! (`Profiler::parse`), or live from cvc5's `(get-instantiation-graph)`
//! (`InstantiationGraph::from_live`). Nodes are instantiations; an edge runs
//! from the instantiation that introduced a term to each instantiation that
//! matched it. Counts and edges are the solver's; costs and growth labels are
//! summaries derived from them.

use crate::profiler::{InstInfo, InstantiationGraph, NodeId};
use serde::Serialize;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};

/// Which instantiations a query looks at.
#[derive(Clone, Debug, Default)]
pub struct GraphFilter {
    /// Only instantiations of these quantifiers, by name; all when `None`.
    pub quantifiers: Option<HashSet<String>>,
    /// Only instantiations at least this deep.
    pub min_depth: Option<u64>,
}

/// What to ask of the graph.
#[derive(Clone, Debug)]
pub enum GraphOp {
    Cycles,
    TopCost,
    Subgraph,
    /// The shortest chain of parents leading to `to_inst` from an
    /// instantiation of `from_qid`, or from a root when `from_qid` is `None`.
    Path {
        from_qid: Option<String>,
        to_inst: u64,
    },
    Growth,
}

/// One instantiation, as queries report it.
#[derive(Clone, Debug, Serialize)]
pub struct GraphNode {
    pub inst: u64,
    pub qid: String,
    pub depth: u64,
    pub round: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub term_depth: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub strategy: Option<String>,
    /// The function the quantifier belongs to and, if the user wrote it,
    /// where; filled in by a caller that knows.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_span: Option<String>,
}

/// Quantifiers whose instantiations produce each other's triggers.
#[derive(Debug, Serialize)]
pub struct Cycle {
    /// The quantifiers of one strongly connected component, sorted.
    pub quantifiers: Vec<String>,
    /// How many quantifiers take part.
    pub length: usize,
    /// Parent-to-child edges between instantiations of these quantifiers.
    pub repetitions: u64,
    /// Instantiations of these quantifiers.
    pub instantiations: u64,
    /// The longest chain of their instantiations, each a parent of the next.
    pub longest_chain: usize,
    /// That chain from its root side, at most `limit` nodes, and its edges.
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<(u64, u64)>,
}

#[derive(Debug, Serialize)]
pub struct QuantifierCost {
    pub qid: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_span: Option<String>,
    /// Its instantiations.
    pub count: u64,
    /// Instantiations its instantiations were parents of.
    pub children: u64,
    /// The cost of its instantiations, summed: an instantiation costs 1 plus
    /// its children's costs, each split evenly among that child's parents.
    /// As in the z3 profiler, a quantifier whose instantiations descend from
    /// each other (a loop) counts those descendants once per ancestor, which
    /// is what ranks loop members first.
    pub subtree_cost: f64,
    pub max_depth: u64,
}

#[derive(Debug, Serialize)]
pub struct Subgraph {
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<(u64, u64)>,
    /// Instantiations and edges that matched the filter, before `limit`.
    pub matching_nodes: usize,
    pub matching_edges: usize,
    pub truncated: bool,
}

#[derive(Debug, Serialize)]
pub struct PathAnswer {
    /// Ancestor first. `None` when no instantiation of `from_qid` leads to
    /// the target.
    pub nodes: Option<Vec<GraphNode>>,
    /// Instantiations on the whole chain.
    pub length: usize,
    /// Whether the middle of a chain longer than `limit` was left out.
    pub truncated: bool,
}

/// A summary label for a series of per-step instantiation counts.
#[derive(Debug, Serialize)]
pub struct Fit {
    /// `exponential` (each step multiplies the last), `linear` (each step
    /// keeps producing, so the total grows linearly), `bounded` (production
    /// dies away) or `insufficient_data` (fewer than three steps).
    pub label: &'static str,
    /// Least-squares slope of the per-step counts.
    pub slope: f64,
    /// Per-step factor of a log-linear fit, when every step is nonzero.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ratio: Option<f64>,
    /// How well that fit explains the counts (R²).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ratio_r2: Option<f64>,
}

#[derive(Debug, Serialize)]
pub struct QuantifierGrowth {
    pub qid: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_span: Option<String>,
    pub count: u64,
    pub per_step: Vec<u64>,
    pub fit: Fit,
}

#[derive(Debug, Serialize)]
pub struct Growth {
    /// `round` when the solver recorded instantiation rounds, else `depth`.
    pub step: &'static str,
    /// Instantiations per round, from round 1; empty without rounds.
    pub per_round: Vec<u64>,
    /// Instantiations per depth, from depth 0.
    pub per_depth: Vec<u64>,
    /// The fit over the chosen steps.
    pub fit: Fit,
    /// The `limit` most instantiated quantifiers over the same steps.
    pub quantifiers: Vec<QuantifierGrowth>,
}

#[derive(Debug, Serialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum GraphAnswer {
    Cycles { cycles: Vec<Cycle> },
    TopCost { quantifiers: Vec<QuantifierCost> },
    Subgraph(Subgraph),
    Path(PathAnswer),
    Growth(Growth),
}

#[derive(Debug, Serialize)]
pub struct GraphReply {
    #[serde(flatten)]
    pub answer: GraphAnswer,
    /// Instantiations recorded, whatever the filter.
    pub total_instantiations: usize,
    pub total_edges: usize,
    /// Instantiations the solver made but did not record (its node limit).
    pub dropped: u64,
}

/// Where a quantifier comes from: the function it belongs to and, for one the
/// user wrote, its span.
pub struct Site {
    pub function: String,
    pub span: Option<String>,
}

impl GraphAnswer {
    /// Fill in `function` and `source_span` wherever a quantifier is named.
    pub fn annotate(&mut self, site: impl Fn(&str) -> Option<Site>) {
        let fill = |qid: &str, function: &mut Option<String>, span: &mut Option<String>| {
            if let Some(site) = site(qid) {
                *function = Some(site.function);
                *span = site.span;
            }
        };
        let node = |n: &mut GraphNode| fill(&n.qid, &mut n.function, &mut n.source_span);
        match self {
            GraphAnswer::Cycles { cycles } => {
                cycles.iter_mut().flat_map(|c| c.nodes.iter_mut()).for_each(node)
            }
            GraphAnswer::TopCost { quantifiers } => quantifiers
                .iter_mut()
                .for_each(|q| fill(&q.qid, &mut q.function, &mut q.source_span)),
            GraphAnswer::Subgraph(s) => s.nodes.iter_mut().for_each(node),
            GraphAnswer::Path(p) => p.nodes.iter_mut().flatten().for_each(node),
            GraphAnswer::Growth(g) => g
                .quantifiers
                .iter_mut()
                .for_each(|q| fill(&q.qid, &mut q.function, &mut q.source_span)),
        }
    }
}

/// Summary of a graph, reported with each check that records one.
#[derive(Clone, Debug, Serialize)]
pub struct GraphSummary {
    pub instantiations: usize,
    pub edges: usize,
    pub quantifiers: usize,
    pub rounds: u64,
    pub max_depth: u64,
    pub dropped: u64,
}

fn malformed(line: &str) -> String {
    format!("malformed instantiation graph line: {line}")
}

fn number<T: std::str::FromStr>(text: &str, line: &str) -> Result<T, String> {
    text.parse().map_err(|_| malformed(line))
}

impl InstantiationGraph {
    /// Parse cvc5's reply to `(get-instantiation-graph)`, given as lines.
    /// An `(error ...)` reply is returned as the error.
    pub fn from_live(lines: &[String]) -> Result<Self, String> {
        let mut graph = InstantiationGraph {
            edges: HashMap::new(),
            names: HashMap::new(),
            nodes: HashSet::new(),
            info: HashMap::new(),
            dropped: 0,
        };
        let mut quantifiers: Vec<String> = Vec::new();
        let (mut started, mut finished) = (false, false);
        for line in lines.iter().map(|line| line.trim()).filter(|line| !line.is_empty()) {
            if line.starts_with("(error") {
                return Err(line.to_owned());
            }
            if !started {
                if line != "(instantiation-graph" {
                    return Err(malformed(line));
                }
                started = true;
                continue;
            }
            if finished {
                return Err(malformed(line));
            }
            if line == ")" {
                finished = true;
                continue;
            }
            let body = line
                .strip_prefix('(')
                .and_then(|body| body.strip_suffix(')'))
                .ok_or_else(|| malformed(line))?;
            let (head, rest) = body.split_once(' ').ok_or_else(|| malformed(line))?;
            match head {
                "quantifier" => {
                    let (index, name) = rest.split_once(' ').ok_or_else(|| malformed(line))?;
                    if number::<usize>(index, line)? != quantifiers.len() {
                        return Err(malformed(line));
                    }
                    let name = name.strip_prefix('|').and_then(|n| n.strip_suffix('|'));
                    quantifiers.push(name.unwrap_or(rest.split_once(' ').unwrap().1).to_owned());
                }
                "node" => {
                    // <index> <quantifier> <strategy> <round> <depth> <term depth> (<parents>)
                    let (fields, parents) = rest.split_once(" (").ok_or_else(|| malformed(line))?;
                    let parents = parents.strip_suffix(')').ok_or_else(|| malformed(line))?;
                    let fields: Vec<&str> = fields.split(' ').collect();
                    let [index, quantifier, strategy, round, depth, term_depth] = fields[..] else {
                        return Err(malformed(line));
                    };
                    let index: u64 = number(index, line)?;
                    if index as usize != graph.nodes.len() {
                        return Err(malformed(line));
                    }
                    let name = quantifiers
                        .get(number::<usize>(quantifier, line)?)
                        .ok_or_else(|| malformed(line))?;
                    let id = (index, 0);
                    graph.nodes.insert(id);
                    graph.names.insert(id, name.clone());
                    graph.info.insert(
                        id,
                        InstInfo {
                            strategy: Some(strategy.to_owned()),
                            round: number(round, line)?,
                            depth: number(depth, line)?,
                            term_depth: Some(number(term_depth, line)?),
                        },
                    );
                    for parent in parents.split(' ').filter(|parent| !parent.is_empty()) {
                        let parent: u64 = number(parent, line)?;
                        // cvc5 names only earlier instantiations as parents.
                        if parent >= index {
                            return Err(malformed(line));
                        }
                        graph.edges.entry((parent, 0)).or_default().insert(id);
                    }
                }
                "dropped" => graph.dropped = number(rest, line)?,
                _ => return Err(malformed(line)),
            }
        }
        if !finished {
            return Err("incomplete instantiation graph reply".to_owned());
        }
        Ok(graph)
    }

    pub fn summary(&self) -> GraphSummary {
        GraphSummary {
            instantiations: self.nodes.len(),
            edges: self.edges.values().map(HashSet::len).sum(),
            quantifiers: self.names.values().collect::<HashSet<_>>().len(),
            rounds: self.info.values().map(|info| info.round).max().unwrap_or(0),
            max_depth: self.info.values().map(|info| info.depth).max().unwrap_or(0),
            dropped: self.dropped,
        }
    }

    /// Answer `op` over the instantiations `filter` keeps, listing at most
    /// `limit` of whatever the answer lists.
    pub fn query(
        &self,
        op: &GraphOp,
        filter: &GraphFilter,
        limit: usize,
    ) -> Result<GraphReply, String> {
        let answer = match op {
            GraphOp::Cycles => GraphAnswer::Cycles { cycles: self.cycles(filter, limit) },
            GraphOp::TopCost => GraphAnswer::TopCost { quantifiers: self.top_cost(filter, limit) },
            GraphOp::Subgraph => GraphAnswer::Subgraph(self.subgraph(filter, limit)),
            GraphOp::Path { from_qid, to_inst } => {
                GraphAnswer::Path(self.path(from_qid.as_deref(), *to_inst, limit)?)
            }
            GraphOp::Growth => GraphAnswer::Growth(self.growth(filter, limit)),
        };
        Ok(GraphReply {
            answer,
            total_instantiations: self.nodes.len(),
            total_edges: self.edges.values().map(HashSet::len).sum(),
            dropped: self.dropped,
        })
    }

    fn name(&self, id: NodeId) -> &str {
        self.names.get(&id).map(String::as_str).unwrap_or("_")
    }

    fn info(&self, id: NodeId) -> InstInfo {
        self.info.get(&id).cloned().unwrap_or_default()
    }

    fn node(&self, id: NodeId) -> GraphNode {
        let info = self.info(id);
        GraphNode {
            inst: id.0,
            qid: self.name(id).to_owned(),
            depth: info.depth,
            round: info.round,
            term_depth: info.term_depth,
            strategy: info.strategy,
            function: None,
            source_span: None,
        }
    }

    fn keep(&self, filter: &GraphFilter, id: NodeId) -> bool {
        filter.quantifiers.as_ref().is_none_or(|qs| qs.contains(self.name(id)))
            && filter.min_depth.is_none_or(|min| self.info(id).depth >= min)
    }

    fn children(&self, id: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.edges.get(&id).into_iter().flatten().copied()
    }

    fn parents(&self) -> HashMap<NodeId, Vec<NodeId>> {
        let mut parents: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        for (&parent, children) in &self.edges {
            for &child in children {
                parents.entry(child).or_default().push(parent);
            }
        }
        for list in parents.values_mut() {
            list.sort();
        }
        parents
    }

    /// Every node, parents before children, ties broken by id. A trace graph
    /// could in principle contain a cycle; its nodes go last, by id.
    pub(crate) fn topological(&self) -> Vec<NodeId> {
        let parents = self.parents();
        let mut waiting: HashMap<NodeId, usize> =
            self.nodes.iter().map(|&n| (n, parents.get(&n).map_or(0, Vec::len))).collect();
        let mut ready: BinaryHeap<Reverse<NodeId>> =
            waiting.iter().filter(|(_, count)| **count == 0).map(|(&n, _)| Reverse(n)).collect();
        let mut order = Vec::with_capacity(self.nodes.len());
        while let Some(Reverse(node)) = ready.pop() {
            order.push(node);
            waiting.remove(&node);
            for child in self.children(node) {
                if let Some(count) = waiting.get_mut(&child) {
                    *count -= 1;
                    if *count == 0 {
                        ready.push(Reverse(child));
                    }
                }
            }
        }
        let mut rest: Vec<NodeId> = waiting.into_keys().collect();
        rest.sort();
        order.extend(rest);
        order
    }

    /// Set each node's depth from its parents, for graphs whose builder
    /// cannot say.
    pub(crate) fn compute_depths(&mut self) {
        let parents = self.parents();
        for node in self.topological() {
            let depth = parents
                .get(&node)
                .into_iter()
                .flatten()
                .filter_map(|p| self.info.get(p).map(|info| info.depth + 1))
                .max()
                .unwrap_or(0);
            self.info.entry(node).or_default().depth = depth;
        }
    }

    pub fn cycles(&self, filter: &GraphFilter, limit: usize) -> Vec<Cycle> {
        // Quantifier-level edges, weighted by how many instantiation edges
        // they stand for. The instantiation graph itself is acyclic: a parent
        // always precedes its child.
        let mut weights: BTreeMap<(&str, &str), u64> = BTreeMap::new();
        let mut adjacent: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for (&parent, children) in &self.edges {
            if !self.keep(filter, parent) {
                continue;
            }
            for &child in children.iter().filter(|&&child| self.keep(filter, child)) {
                let (from, to) = (self.name(parent), self.name(child));
                *weights.entry((from, to)).or_default() += 1;
                adjacent.entry(from).or_default().insert(to);
                adjacent.entry(to).or_default();
            }
        }
        let parents = self.parents();
        let order = self.topological();
        let mut cycles = Vec::new();
        for component in strongly_connected(&adjacent) {
            let members: BTreeSet<&str> = component.iter().copied().collect();
            if members.len() == 1 && !weights.contains_key(&(component[0], component[0])) {
                continue;
            }
            let repetitions = weights
                .iter()
                .filter(|((from, to), _)| members.contains(from) && members.contains(to))
                .map(|(_, count)| count)
                .sum();
            let member = |id: NodeId| self.keep(filter, id) && members.contains(self.name(id));
            // Longest chain among the members, by dynamic programming in
            // topological order.
            let mut best: HashMap<NodeId, (usize, Option<NodeId>)> = HashMap::new();
            let mut end: Option<(usize, NodeId)> = None;
            let mut instantiations = 0;
            for &node in order.iter().filter(|&&node| member(node)) {
                instantiations += 1;
                let entry = parents
                    .get(&node)
                    .into_iter()
                    .flatten()
                    .filter_map(|p| best.get(p).map(|(length, _)| (*length, *p)))
                    .max_by_key(|&(length, p)| (length, Reverse(p)))
                    .map_or((1, None), |(length, p)| (length + 1, Some(p)));
                if end.is_none_or(|(length, _)| entry.0 > length) {
                    end = Some((entry.0, node));
                }
                best.insert(node, entry);
            }
            let mut chain = Vec::new();
            let mut cursor = end.map(|(_, node)| node);
            while let Some(node) = cursor {
                chain.push(node);
                cursor = best[&node].1;
            }
            chain.reverse();
            let longest_chain = chain.len();
            chain.truncate(limit);
            cycles.push(Cycle {
                quantifiers: members.iter().map(|q| q.to_string()).collect(),
                length: members.len(),
                repetitions,
                instantiations,
                longest_chain,
                edges: chain.windows(2).map(|pair| (pair[0].0, pair[1].0)).collect(),
                nodes: chain.into_iter().map(|node| self.node(node)).collect(),
            });
        }
        cycles.sort_by(|a, b| {
            (Reverse(a.repetitions), Reverse(a.longest_chain), &a.quantifiers).cmp(&(
                Reverse(b.repetitions),
                Reverse(b.longest_chain),
                &b.quantifiers,
            ))
        });
        cycles.truncate(limit);
        cycles
    }

    pub fn top_cost(&self, filter: &GraphFilter, limit: usize) -> Vec<QuantifierCost> {
        let parents = self.parents();
        let mut cost: HashMap<NodeId, f64> = HashMap::new();
        for &node in self.topological().iter().rev() {
            let shares: f64 = self
                .children(node)
                .map(|child| {
                    cost.get(&child).copied().unwrap_or(0.0)
                        / parents.get(&child).map_or(1, Vec::len) as f64
                })
                .sum();
            cost.insert(node, 1.0 + shares);
        }
        let mut by_qid: BTreeMap<&str, QuantifierCost> = BTreeMap::new();
        for &node in self.nodes.iter().filter(|&&node| self.keep(filter, node)) {
            let qid = self.name(node);
            let entry = by_qid.entry(qid).or_insert_with(|| QuantifierCost {
                qid: qid.to_owned(),
                function: None,
                source_span: None,
                count: 0,
                children: 0,
                subtree_cost: 0.0,
                max_depth: 0,
            });
            entry.count += 1;
            entry.children += self.children(node).count() as u64;
            entry.subtree_cost += cost[&node];
            entry.max_depth = entry.max_depth.max(self.info(node).depth);
        }
        let mut costs: Vec<QuantifierCost> = by_qid.into_values().collect();
        costs.sort_by(|a, b| {
            b.subtree_cost
                .total_cmp(&a.subtree_cost)
                .then(b.count.cmp(&a.count))
                .then(a.qid.cmp(&b.qid))
        });
        costs.truncate(limit);
        for entry in &mut costs {
            // Shares are fractions; round what is reported to keep it legible.
            entry.subtree_cost = (entry.subtree_cost * 100.0).round() / 100.0;
        }
        costs
    }

    pub fn subgraph(&self, filter: &GraphFilter, limit: usize) -> Subgraph {
        let mut matching: Vec<NodeId> =
            self.nodes.iter().copied().filter(|&node| self.keep(filter, node)).collect();
        matching.sort();
        let matching_set: HashSet<NodeId> = matching.iter().copied().collect();
        let matching_edges = matching
            .iter()
            .map(|&node| self.children(node).filter(|c| matching_set.contains(c)).count())
            .sum();
        let matching_nodes = matching.len();
        matching.truncate(limit);
        let kept: HashSet<NodeId> = matching.iter().copied().collect();
        let mut edges: Vec<(u64, u64)> = matching
            .iter()
            .flat_map(|&node| {
                self.children(node).filter(|c| kept.contains(c)).map(move |c| (node.0, c.0))
            })
            .collect();
        edges.sort();
        Subgraph {
            nodes: matching.into_iter().map(|node| self.node(node)).collect(),
            edges,
            matching_nodes,
            matching_edges,
            truncated: matching_nodes > limit,
        }
    }

    pub fn path(
        &self,
        from_qid: Option<&str>,
        to_inst: u64,
        limit: usize,
    ) -> Result<PathAnswer, String> {
        let target = (to_inst, 0);
        if !self.nodes.contains(&target) {
            return Err(format!("no instantiation {to_inst} in the graph"));
        }
        let parents = self.parents();
        let is_start = |node: NodeId| match from_qid {
            Some(qid) => self.name(node) == qid,
            None => parents.get(&node).is_none_or(Vec::is_empty),
        };
        // Breadth first over parents finds the shortest chain.
        let mut next: HashMap<NodeId, NodeId> = HashMap::new();
        let mut queue = VecDeque::from([target]);
        let mut seen = HashSet::from([target]);
        let mut start = None;
        while let Some(node) = queue.pop_front() {
            if is_start(node) {
                start = Some(node);
                break;
            }
            for &parent in parents.get(&node).into_iter().flatten() {
                if seen.insert(parent) {
                    next.insert(parent, node);
                    queue.push_back(parent);
                }
            }
        }
        let Some(start) = start else {
            return Ok(PathAnswer { nodes: None, length: 0, truncated: false });
        };
        let mut chain = vec![start];
        while let Some(&node) = next.get(chain.last().unwrap()) {
            chain.push(node);
        }
        let length = chain.len();
        let truncated = length > limit;
        if truncated {
            // Keep both ends: where the chain starts and what it reaches.
            let head = limit.div_ceil(2);
            chain.drain(head..length - (limit - head));
        }
        Ok(PathAnswer {
            nodes: Some(chain.into_iter().map(|node| self.node(node)).collect()),
            length,
            truncated,
        })
    }

    pub fn growth(&self, filter: &GraphFilter, limit: usize) -> Growth {
        let kept: Vec<NodeId> =
            self.nodes.iter().copied().filter(|&node| self.keep(filter, node)).collect();
        let rounds = kept.iter().map(|&node| self.info(node).round).max().unwrap_or(0);
        let depths = kept.iter().map(|&node| self.info(node).depth).max();
        let series = |nodes: &mut dyn Iterator<Item = NodeId>, by_round: bool| {
            let steps =
                if by_round { rounds as usize } else { depths.map_or(0, |d| d as usize + 1) };
            let mut counts = vec![0u64; steps];
            for node in nodes {
                let info = self.info(node);
                let step = if by_round { info.round as usize } else { info.depth as usize + 1 };
                // Rounds count from 1; a round of 0 means the builder could not say.
                if step >= 1 && step <= steps {
                    counts[step - 1] += 1;
                }
            }
            counts
        };
        let by_round = rounds > 0;
        let per_round = if by_round { series(&mut kept.iter().copied(), true) } else { vec![] };
        let per_depth = series(&mut kept.iter().copied(), false);
        let overall = fit(if by_round { &per_round } else { &per_depth });
        let mut by_qid: BTreeMap<&str, Vec<NodeId>> = BTreeMap::new();
        for &node in &kept {
            by_qid.entry(self.name(node)).or_default().push(node);
        }
        let mut quantifiers: Vec<QuantifierGrowth> = by_qid
            .into_iter()
            .map(|(qid, nodes)| {
                let per_step = series(&mut nodes.iter().copied(), by_round);
                QuantifierGrowth {
                    qid: qid.to_owned(),
                    function: None,
                    source_span: None,
                    count: nodes.len() as u64,
                    fit: fit(&per_step),
                    per_step,
                }
            })
            .collect();
        quantifiers.sort_by(|a, b| b.count.cmp(&a.count).then(a.qid.cmp(&b.qid)));
        quantifiers.truncate(limit);
        Growth {
            step: if by_round { "round" } else { "depth" },
            per_round,
            per_depth,
            fit: overall,
            quantifiers,
        }
    }
}

/// Label a series of per-step counts. The thresholds are conventions, not
/// statistics: a factor of at least 1.25 per step that a log-linear fit
/// explains well (R² ≥ 0.8) is exponential; production in the last third of
/// the steps that keeps up with at least half of the first third's is linear;
/// anything else is bounded.
pub fn fit(counts: &[u64]) -> Fit {
    let n = counts.len();
    let xs: Vec<f64> = (1..=n).map(|x| x as f64).collect();
    let ys: Vec<f64> = counts.iter().map(|&c| c as f64).collect();
    let slope = least_squares(&xs, &ys).map_or(0.0, |(slope, _)| slope);
    if n < 3 {
        return Fit { label: "insufficient_data", slope, ratio: None, ratio_r2: None };
    }
    let (ratio, ratio_r2) = if counts.iter().all(|&c| c > 0) {
        let logs: Vec<f64> = ys.iter().map(|y| y.ln()).collect();
        match least_squares(&xs, &logs) {
            Some((log_slope, r2)) => (Some(log_slope.exp()), Some(r2)),
            None => (None, None),
        }
    } else {
        (None, None)
    };
    let third = n.div_ceil(3);
    let mean = |ys: &[f64]| ys.iter().sum::<f64>() / ys.len() as f64;
    let label = if ratio.is_some_and(|r| r >= 1.25) && ratio_r2.is_some_and(|r2| r2 >= 0.8) {
        "exponential"
    } else if counts[n - 1] > 0 && mean(&ys[n - third..]) >= 0.5 * mean(&ys[..third]) {
        "linear"
    } else {
        "bounded"
    };
    let round = |x: f64| (x * 1000.0).round() / 1000.0;
    Fit { label, slope: round(slope), ratio: ratio.map(round), ratio_r2: ratio_r2.map(round) }
}

/// Slope and R² of the least-squares line through the points, if there are
/// at least two distinct xs. R² is 1 when the ys are constant.
fn least_squares(xs: &[f64], ys: &[f64]) -> Option<(f64, f64)> {
    let n = xs.len() as f64;
    if xs.len() < 2 {
        return None;
    }
    let (mx, my) = (xs.iter().sum::<f64>() / n, ys.iter().sum::<f64>() / n);
    let sxx: f64 = xs.iter().map(|x| (x - mx).powi(2)).sum();
    let sxy: f64 = xs.iter().zip(ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let syy: f64 = ys.iter().map(|y| (y - my).powi(2)).sum();
    if sxx == 0.0 {
        return None;
    }
    let slope = sxy / sxx;
    let r2 = if syy == 0.0 { 1.0 } else { (sxy * sxy) / (sxx * syy) };
    Some((slope, r2))
}

/// Tarjan's strongly connected components, each sorted, in discovery order.
fn strongly_connected<'a>(adjacent: &BTreeMap<&'a str, BTreeSet<&'a str>>) -> Vec<Vec<&'a str>> {
    struct State<'a, 'b> {
        adjacent: &'b BTreeMap<&'a str, BTreeSet<&'a str>>,
        index: HashMap<&'a str, usize>,
        low: HashMap<&'a str, usize>,
        stack: Vec<&'a str>,
        on_stack: HashSet<&'a str>,
        components: Vec<Vec<&'a str>>,
    }
    fn visit<'a>(state: &mut State<'a, '_>, node: &'a str) {
        let index = state.index.len();
        state.index.insert(node, index);
        state.low.insert(node, index);
        state.stack.push(node);
        state.on_stack.insert(node);
        for &next in state.adjacent.get(node).into_iter().flatten() {
            if !state.index.contains_key(next) {
                visit(state, next);
                let low = state.low[node].min(state.low[next]);
                state.low.insert(node, low);
            } else if state.on_stack.contains(next) {
                let low = state.low[node].min(state.index[next]);
                state.low.insert(node, low);
            }
        }
        if state.low[node] == state.index[node] {
            let mut component = Vec::new();
            loop {
                let member = state.stack.pop().unwrap();
                state.on_stack.remove(member);
                component.push(member);
                if member == node {
                    break;
                }
            }
            component.sort();
            state.components.push(component);
        }
    }
    let mut state = State {
        adjacent,
        index: HashMap::new(),
        low: HashMap::new(),
        stack: Vec::new(),
        on_stack: HashSet::new(),
        components: Vec::new(),
    };
    for &node in adjacent.keys() {
        if !state.index.contains_key(node) {
            visit(&mut state, node);
        }
    }
    state.components
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(text: &str) -> Vec<String> {
        text.lines().map(str::to_owned).collect()
    }

    /// Two quantifiers feeding each other (a matching loop), fed by a root
    /// instantiation of a third, as cvc5 prints it.
    const LOOP: &str = "(instantiation-graph
(quantifier 0 user_decode_42)
(quantifier 1 user_encode_41)
(quantifier 2 |internal root|)
(node 0 2 QUANTIFIERS_INST_E_MATCHING 1 0 1 ())
(node 1 0 QUANTIFIERS_INST_E_MATCHING 1 1 1 (0))
(node 2 1 QUANTIFIERS_INST_E_MATCHING 2 2 2 (1))
(node 3 0 QUANTIFIERS_INST_E_MATCHING 3 3 3 (2))
(node 4 1 QUANTIFIERS_INST_E_MATCHING 4 4 4 (3))
(node 5 0 QUANTIFIERS_INST_E_MATCHING 4 1 1 (0))
(dropped 0)
)";

    fn graph() -> InstantiationGraph {
        InstantiationGraph::from_live(&lines(LOOP)).unwrap()
    }

    #[test]
    fn parses_nodes_edges_and_quoted_names() {
        let graph = graph();
        assert_eq!(graph.nodes.len(), 6);
        assert_eq!(graph.edges[&(0, 0)], HashSet::from([(1, 0), (5, 0)]));
        assert_eq!(graph.names[&(0, 0)], "internal root");
        assert_eq!(graph.info[&(4, 0)].depth, 4);
        let summary = graph.summary();
        assert_eq!((summary.edges, summary.quantifiers, summary.rounds), (5, 3, 4));
    }

    #[test]
    fn rejects_errors_truncation_and_forward_parents() {
        let error = lines("(error \"Cannot get the instantiation graph\")");
        assert!(InstantiationGraph::from_live(&error).unwrap_err().starts_with("(error"));
        let cut = lines("(instantiation-graph\n(quantifier 0 q)");
        assert!(InstantiationGraph::from_live(&cut).is_err());
        let forward =
            lines("(instantiation-graph\n(quantifier 0 q)\n(node 0 0 X 1 0 0 (1))\n(dropped 0)\n)");
        assert!(InstantiationGraph::from_live(&forward).is_err());
    }

    #[test]
    fn cycles_find_the_two_quantifier_loop() {
        let cycles = graph().cycles(&GraphFilter::default(), 10);
        assert_eq!(cycles.len(), 1);
        let cycle = &cycles[0];
        assert_eq!(cycle.quantifiers, ["user_decode_42", "user_encode_41"]);
        assert_eq!((cycle.length, cycle.repetitions, cycle.longest_chain), (2, 3, 4));
        assert_eq!(cycle.instantiations, 5);
        assert_eq!(cycle.edges, [(1, 2), (2, 3), (3, 4)]);
        // Filtering one side away breaks the loop.
        let filter = GraphFilter {
            quantifiers: Some(HashSet::from(["user_decode_42".to_owned()])),
            min_depth: None,
        };
        assert!(graph().cycles(&filter, 10).is_empty());
        // So does looking only below the second unrolling.
        let deep = GraphFilter { quantifiers: None, min_depth: Some(4) };
        assert!(graph().cycles(&deep, 10).is_empty());
    }

    #[test]
    fn top_cost_splits_descendants_among_parents() {
        let costs = graph().top_cost(&GraphFilter::default(), 10);
        // Costs: 4 -> 1, 3 -> 2, 2 -> 3, 1 -> 4, 5 -> 1, root 0 -> 1 + 4 + 1.
        // Decode's instantiations 1, 3 and 5 sum past the root's, since 3
        // descends from 1.
        let order: Vec<&str> = costs.iter().map(|c| c.qid.as_str()).collect();
        assert_eq!(order, ["user_decode_42", "internal root", "user_encode_41"]);
        let decode = &costs[0];
        assert_eq!((decode.count, decode.children, decode.max_depth), (3, 2, 3));
        assert_eq!(decode.subtree_cost, 4.0 + 2.0 + 1.0);
        assert_eq!(costs[1].subtree_cost, 6.0);
        assert_eq!(costs[2].subtree_cost, 3.0 + 1.0);
    }

    #[test]
    fn path_finds_the_shortest_chain_and_keeps_both_ends() {
        let graph = graph();
        let path = graph.path(Some("user_decode_42"), 4, 10).unwrap();
        let insts: Vec<u64> = path.nodes.unwrap().iter().map(|n| n.inst).collect();
        assert_eq!(insts, [3, 4]);
        let root = graph.path(None, 4, 3).unwrap();
        assert_eq!(root.length, 5);
        assert!(root.truncated);
        let insts: Vec<u64> = root.nodes.unwrap().iter().map(|n| n.inst).collect();
        assert_eq!(insts, [0, 1, 4]);
        assert!(graph.path(Some("absent"), 4, 10).unwrap().nodes.is_none());
        assert!(graph.path(None, 99, 10).is_err());
    }

    #[test]
    fn subgraph_limits_and_counts() {
        let sub = graph().subgraph(&GraphFilter { quantifiers: None, min_depth: Some(1) }, 3);
        assert_eq!((sub.matching_nodes, sub.matching_edges), (5, 3));
        assert!(sub.truncated);
        let insts: Vec<u64> = sub.nodes.iter().map(|n| n.inst).collect();
        assert_eq!(insts, [1, 2, 3]);
        assert_eq!(sub.edges, [(1, 2), (2, 3)]);
    }

    #[test]
    fn growth_uses_rounds_when_recorded() {
        let growth = graph().growth(&GraphFilter::default(), 10);
        assert_eq!(growth.step, "round");
        assert_eq!(growth.per_round, [2, 1, 1, 2]);
        assert_eq!(growth.per_depth, [1, 2, 1, 1, 1]);
    }

    #[test]
    fn fit_labels() {
        assert_eq!(fit(&[1, 2]).label, "insufficient_data");
        assert_eq!(fit(&[1, 2, 4, 8, 16, 32]).label, "exponential");
        assert_eq!(fit(&[3, 3, 3, 3, 3, 3]).label, "linear");
        assert_eq!(fit(&[9, 4, 1, 0, 0, 0]).label, "bounded");
        let exp = fit(&[1, 2, 4, 8, 16, 32]);
        assert_eq!(exp.ratio, Some(2.0));
    }

    #[test]
    fn annotate_fills_spans() {
        let mut answer = graph().query(&GraphOp::Cycles, &GraphFilter::default(), 10).unwrap();
        answer.answer.annotate(|qid| {
            (qid != "user_encode_41")
                .then(|| Site { function: "lib::f".to_owned(), span: Some(format!("{qid}.rs:1")) })
        });
        let GraphAnswer::Cycles { cycles } = &answer.answer else { panic!() };
        for node in &cycles[0].nodes {
            let expected = (node.qid != "user_encode_41").then(|| format!("{}.rs:1", node.qid));
            assert_eq!(node.source_span, expected);
        }
        assert_eq!(answer.total_instantiations, 6);
    }
}
