//! Distributed safety proof for the Raft protocol, as implemented by
//! `raft::node` — a Verus model-level proof over an abstract ensemble model.
//!
//! # What this is
//!
//! This module contains no executable code. It defines an abstract state
//! machine of the *whole cluster* — every host's state, a monotone history of
//! every message ever sent, and ghost proof bookkeeping — whose transitions
//! mirror the protocol steps of `RawNode<Role>` in `node.rs`. Over all states
//! reachable from `init` via `next`, it proves the Raft safety properties:
//!
//! * **Election safety** (`thm_election_safety`): at most one leader per
//!   term. Via vote-once-per-term (`set_term_vote` never changes a vote
//!   within a term) and quorum intersection.
//! * **Log matching** (`thm_log_matching`): logs that agree on the term of an
//!   entry agree on that entry and everything before it.
//! * **Leader completeness** (`thm_leader_completeness`): a committed prefix
//!   is contained, verbatim, in the log of every leader of a later term. Via
//!   the section 5.4.1 up-to-date vote check and the section 5.4.2 own-term
//!   commit restriction in `maybe_commit_and_apply`.
//! * **State machine safety** (`thm_state_machine_safety`): no two hosts ever
//!   disagree on a committed entry. (Nodes apply exactly the committed
//!   prefix of the verified log view via `Log::read_committed`, so agreement
//!   on committed entries carries to the commands each state machine is
//!   fed; the state machines themselves are outside the verified perimeter.)
//! * **Linearizable reads** (`thm_read_linearizable`): when the leader serves
//!   a read — after quorum confirmation of the read sequence number and with
//!   an own-term committed tail, `maybe_read`'s conditions — its committed
//!   prefix contains every write that was committed anywhere in the cluster
//!   when the read was submitted. (`maybe_read` additionally gates on the
//!   unverified applied index having caught up to the commit index, and the
//!   response bytes come from the unverified state machine.)
//!
//! `thm_raft_safety` packages election safety and state machine safety over
//! every state of every execution; `execution_implies_inv` transports the
//! inductive invariant `inv` (proved to hold initially and to be preserved by
//! every transition, `step_preserves_inv`) to all reachable states.
//!
//! # Correspondence to the implementation
//!
//! Each transition documents the `node.rs` code it models; the map is:
//!
//! | model               | implementation                                        |
//! |---------------------|-------------------------------------------------------|
//! | `t_campaign`        | `RawNode::<Candidate>::campaign`                      |
//! | `t_grant`           | `Message::Campaign` handling (follower step)          |
//! | `t_collect_vote`    | `Message::CampaignResponse` handling (candidate step) |
//! | `t_become_leader`   | `Candidate::into_leader` (incl. the noop append)      |
//! | `t_propose`         | `Leader::propose`                                     |
//! | `t_send_append`     | `Leader::maybe_send_append`                           |
//! | `t_recv_append`     | `Message::Append` handling + `Log::splice`            |
//! | `t_send_ack`        | matching `Message::HeartbeatResponse`, self-match     |
//! | `t_leader_commit`   | `Leader::maybe_commit_and_apply`                      |
//! | `t_send_commit`     | `Leader::heartbeat` (commit_index)                    |
//! | `t_recv_commit`     | `Message::Heartbeat` commit handling                  |
//! | `t_restart`         | `Node::new` after a crash-restart (commit may lag)    |
//! | `t_submit_read`     | `ClientRequest::Read` handling (leader step)          |
//! | `t_confirm_read`    | `Message::Read`/`ReadResponse` handling               |
//!
//! The network is modeled as a monotone message set: messages may be dropped,
//! reordered, and duplicated arbitrarily (a transition may fire on any
//! message ever sent, or never). Some messages carry ghost payloads — the
//! full logs behind `Campaign`/`CampaignResponse`'s (last_index, last_term)
//! summaries, and the commit record behind a heartbeat's commit_index — which
//! model sender state that the proof needs to refer to later.
//!
//! # Trust boundary
//!
//! This module is the protocol-level proof (in the spirit of TLA+, Verdi,
//! and IronFleet's protocol layer). The connection to the executable code
//! has two machine-checked layers and a trusted rim:
//!
//! * `raft::refine` verifies that the step functions' decision logic and
//!   state changes implement these model transitions (node-local
//!   refinement via verified step cores), under the trusted assumptions
//!   documented there (network non-forgery, storage integrity, the
//!   mechanical shell in `node.rs`).
//! * `raft::log` verifies the log's own state-transition invariants.
//!
//! Liveness (elections eventually succeed, requests eventually commit) is
//! out of scope — Raft's liveness is timing-dependent by design.
//!
//! # Proof structure
//!
//! The inductive invariant `inv` is a conjunction of per-family invariants,
//! the load-bearing ones being:
//!
//! * `log_pinned` (invariant families over hosts, messages, and leader logs):
//!   every entry was created once, by its term's leader, at a fixed position,
//!   pinning any log holding it to that leader's log up through it. This is
//!   Log Matching in inductive form.
//! * `ack_persist_ok` / `vote_persist_ok` / `frozen_persist_ok`: a host that
//!   acknowledged a leader's log prefix keeps that prefix — in its current
//!   log, and in the frozen log snapshots inside its later votes — as long as
//!   every leader elected in between kept it too (a conditional invariant
//!   discharged by Leader Completeness exactly when needed).
//! * `inv_leader_completeness` with `lemma_h2`/`lemma_uptodate_prefix`: the
//!   quorum-intersection induction. A commit's ack quorum overlaps every
//!   later election's vote quorum; the shared voter's log retained the
//!   committed prefix, and the section 5.4.1 up-to-date check forces the
//!   winner's log to contain it.
//! * `host_commit_ok`: every host's committed prefix equals a committed
//!   leader-log prefix (splices can never truncate it — the append source
//!   agrees with it by Leader Completeness), which yields state machine
//!   safety.
//! * `read_rec_ok`: ghost read records snapshot the commits existing at
//!   submission; confirmations by members of any higher-term commit quorum
//!   provably predate the read, so a quorum-confirmed read cannot have missed
//!   a submission-time commit.
//!
//! Everything below erases under a normal `cargo build`; only Verus sees it.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Abstract state
// ---------------------------------------------------------------------------

/// An abstract log entry: the term it was proposed in, and the command
/// payload (None is the leader's election noop; see `Log::append(None)`).
pub struct AEntry {
    pub term: nat,
    pub cmd: Option<Seq<u8>>,
}

/// A node role, mirroring `Node::{Follower, Candidate, Leader}`.
pub enum MRole {
    Follower,
    Candidate,
    Leader,
}

/// A ghost commit record: the leader of `term` observed an ack quorum for a
/// log prefix of length `ci` whose last entry is from `term` itself (the
/// section 5.4.2 own-term commit restriction in `maybe_commit_and_apply`).
/// `q` maps each quorum member to its acked match index (>= ci).
pub struct CommitRec {
    pub term: nat,
    pub ci: nat,
    pub q: Map<int, nat>,
}

/// Per-host abstract state: the durable log state (`LogState` in log.rs) plus
/// the volatile role state of `RawNode<R>`, plus ghost proof bookkeeping.
pub struct MHost {
    /// Current term (durable, `Log::get_term_vote().0`).
    pub term: nat,
    /// Vote in the current term (durable, `Log::get_term_vote().1`).
    pub vote: Option<int>,
    /// Current role (volatile).
    pub role: MRole,
    /// The log: entry k models impl index k+1 (impl indexes from 1).
    pub log: Seq<AEntry>,
    /// Commit index (number of committed entries; durable).
    pub commit: nat,
    /// Collected votes (volatile, `Candidate::votes`).
    pub votes: Set<int>,
    /// Ghost: for each collected vote, the voter's log at grant time.
    pub vote_logs: Map<int, Seq<AEntry>>,
    /// Ghost: the commit record justifying `commit` (meaningful when > 0).
    pub crec: CommitRec,
    /// Read sequence number (volatile, `Leader::read_seq`).
    pub read_seq: nat,
}

/// A ghost read record: a linearizable read submitted to the leader of `term`
/// with sequence number `seq`; `born` snapshots the commit records that
/// existed at submission time.
pub struct ReadRec {
    pub term: nat,
    pub seq: nat,
    pub born: Set<CommitRec>,
}

/// Messages, as a monotone history (the network may drop, reorder, and
/// duplicate; safety treats every sent message as forever available). Ghost
/// payloads (full logs on Campaign/Vote, the commit record on Commit) capture
/// sender state that the real messages only summarize.
pub enum Msg {
    /// `Message::Campaign`: candidate `c` solicits votes for `term`.
    /// `clog` is the candidate's log (impl sends its last_index/last_term).
    Campaign { c: int, term: nat, clog: Seq<AEntry> },
    /// `Message::CampaignResponse { vote: true }` from voter `v`, plus the
    /// candidate's implicit self-vote. `vlog` is the voter's log at grant.
    Vote { v: int, c: int, term: nat, vlog: Seq<AEntry> },
    /// `Message::Append` from the leader of `term`.
    Append { term: nat, base: nat, bterm: nat, entries: Seq<AEntry> },
    /// A commit index broadcast (`Message::Heartbeat { commit_index }`), with
    /// the justifying commit record as ghost payload.
    Commit { term: nat, ci: nat, rec: CommitRec },
    /// An accepted append or matching heartbeat response: host `v`'s log
    /// matched the leader-of-`term`'s log up to `mi`
    /// (`Message::{AppendResponse, HeartbeatResponse}` with match_index).
    Ack { v: int, term: nat, mi: nat },
    /// `Message::Read { seq }` from the leader of `term`.
    Read { term: nat, seq: nat },
    /// `Message::ReadResponse { seq }` from host `v`.
    ReadConfirm { v: int, term: nat, seq: nat },
}

/// The global (ensemble) state.
pub struct GState {
    /// Cluster size; hosts are identified by 0..n.
    pub n: nat,
    /// Per-host state, indexed by node id.
    pub hosts: Seq<MHost>,
    /// Monotone message history.
    pub net: Set<Msg>,
    /// Ghost: the definitive log of each term's leader (latest version while
    /// the leader reigns; frozen once it steps down). Domain = terms that
    /// elected a leader.
    pub leader_log: Map<nat, Seq<AEntry>>,
    /// Ghost: which node won each term's election.
    pub leader_of: Map<nat, int>,
    /// Ghost: the winning vote quorum of each term's election.
    pub voters: Map<nat, Set<int>>,
    /// Ghost: the winner's log at election time (before the noop append).
    pub elect_log: Map<nat, Seq<AEntry>>,
    /// Ghost: the winning quorum's vote logs at election time.
    pub elect_votes: Map<nat, Map<int, Seq<AEntry>>>,
    /// Ghost: all commit records.
    pub commits: Set<CommitRec>,
    /// Ghost: all submitted linearizable reads.
    pub reads: Set<ReadRec>,
    /// Ghost: highest read sequence number issued per term.
    pub read_hwm: Map<nat, nat>,
}

// ---------------------------------------------------------------------------
// Spec helpers
// ---------------------------------------------------------------------------

/// The set of node ids.
pub open spec fn node_ids(n: nat) -> Set<int> {
    Set::<int>::range(0, n as int)
}

/// A quorum: a strict majority of the cluster (`RawNode::quorum_size`).
pub open spec fn is_quorum(n: nat, q: Set<int>) -> bool {
    &&& q.subset_of(node_ids(n))
    &&& 2 * q.len() > n
}

/// The term of the last entry, 0 for an empty log (`Log::get_last_index`).
pub open spec fn last_term(log: Seq<AEntry>) -> nat {
    if log.len() == 0 { 0 } else { log[log.len() - 1].term }
}

/// The section 5.4.1 up-to-date check (`Message::Campaign` handling in
/// `RawNode::<Follower>::step`): `a` (candidate log) is at least as
/// up-to-date as `b` (voter log).
pub open spec fn up_to_date(a: Seq<AEntry>, b: Seq<AEntry>) -> bool {
    ||| last_term(a) > last_term(b)
    ||| (last_term(a) == last_term(b) && a.len() >= b.len())
}

/// The first `i` entries of `a` and `b` exist and agree.
pub open spec fn prefix_eq(a: Seq<AEntry>, b: Seq<AEntry>, i: nat) -> bool {
    &&& i <= a.len()
    &&& i <= b.len()
    &&& forall|j: int| 0 <= j < i ==> a[j] == b[j]
}

/// Whether the spliced entries are already fully present in the log, in which
/// case `Log::splice` keeps the (possibly longer) existing log.
pub open spec fn splice_is_noop(log: Seq<AEntry>, base: nat, entries: Seq<AEntry>) -> bool {
    &&& base + entries.len() <= log.len()
    &&& forall|j: int| 0 <= j < entries.len() ==> log[base + j] == entries[j]
}

/// The result of `Log::splice`: if all entries match the existing log, keep
/// it; otherwise truncate at the first conflict and append. (When a conflict
/// exists at offset c, log[..base+c] + entries[c..] == log[..base] + entries,
/// since the first c entries match.)
pub open spec fn splice(log: Seq<AEntry>, base: nat, entries: Seq<AEntry>) -> Seq<AEntry> {
    if splice_is_noop(log, base, entries) {
        log
    } else {
        log.subrange(0, base as int) + entries
    }
}

/// Entry `j` of `log` pins the log's prefix through `j` to the leader log of
/// the entry's term: entries are created once, by their term's leader, at a
/// fixed position, and every log agrees with that leader's log up to any
/// entry it shares with it (the Log Matching property, section 5.3).
/// `m` is the ghost per-term leader-log map.
pub open spec fn pinned_at(m: Map<nat, Seq<AEntry>>, log: Seq<AEntry>, j: int) -> bool {
    let t = log[j].term;
    &&& m.dom().contains(t)
    &&& j < m[t].len()
    &&& forall|k: int| 0 <= k <= j ==> log[k] == #[trigger] m[t][k]
}

/// Every entry of `log` pins its prefix (see `pinned_at`).
pub open spec fn log_pinned(m: Map<nat, Seq<AEntry>>, log: Seq<AEntry>) -> bool {
    forall|j: int| 0 <= j < log.len() ==> #[trigger] pinned_at(m, log, j)
}

/// Leader logs only ever grow (append-only per term; a new term starts fresh).
pub open spec fn ll_extends(m1: Map<nat, Seq<AEntry>>, m2: Map<nat, Seq<AEntry>>) -> bool {
    forall|t: nat| #[trigger] m1.dom().contains(t) ==> {
        &&& m2.dom().contains(t)
        &&& prefix_eq(m2[t], m1[t], m1[t].len())
    }
}

/// Pinning survives leader-log growth.
pub proof fn lemma_pinned_extend(m1: Map<nat, Seq<AEntry>>, m2: Map<nat, Seq<AEntry>>, log: Seq<AEntry>)
    requires
        log_pinned(m1, log),
        ll_extends(m1, m2),
    ensures
        log_pinned(m2, log),
{
    assert forall|j: int| 0 <= j < log.len() implies pinned_at(m2, log, j) by {
        assert(pinned_at(m1, log, j));
        let tau = log[j].term;
        assert(prefix_eq(m2[tau], m1[tau], m1[tau].len()));
        assert forall|k: int| 0 <= k <= j implies log[k] == m2[tau][k] by {
            assert(log[k] == m1[tau][k]);
        }
    }
}

/// The log-matching core: two pinned logs that agree on the term of a shared
/// position agree on the whole prefix through it.
pub proof fn lemma_log_matching(m: Map<nat, Seq<AEntry>>, la: Seq<AEntry>, lb: Seq<AEntry>, j: int)
    requires
        log_pinned(m, la),
        log_pinned(m, lb),
        0 <= j < la.len(),
        j < lb.len(),
        la[j].term == lb[j].term,
    ensures
        forall|k: int| 0 <= k <= j ==> la[k] == lb[k],
{
    assert(pinned_at(m, la, j));
    assert(pinned_at(m, lb, j));
    let tau = la[j].term;
    assert forall|k: int| 0 <= k <= j implies la[k] == lb[k] by {
        assert(la[k] == m[tau][k]);
        assert(lb[k] == m[tau][k]);
    }
}

/// Pinning transfers to any pointwise-equal (prefix) log.
pub proof fn lemma_pinned_transfer(m: Map<nat, Seq<AEntry>>, a: Seq<AEntry>, b: Seq<AEntry>)
    requires
        log_pinned(m, a),
        b.len() <= a.len(),
        forall|k: int| 0 <= k < b.len() ==> a[k] == b[k],
    ensures
        log_pinned(m, b),
{
    assert forall|j: int| 0 <= j < b.len() implies pinned_at(m, b, j) by {
        assert(pinned_at(m, a, j));
        let tau = a[j].term;
        assert forall|k: int| 0 <= k <= j implies b[k] == m[tau][k] by {
            assert(a[k] == m[tau][k]);
        }
    }
}

/// The up-to-date transfer at the heart of Leader Completeness: a candidate
/// log that (a) passed the section 5.4.1 check against a voter log holding a
/// committed prefix of `m[t]` ending in a term-t entry, (b) is pinned, and
/// (c) holds only entries of terms below `hi`, where every elected term in
/// (t, hi) complies with the committed prefix — itself holds the prefix.
pub proof fn lemma_uptodate_prefix(
    m: Map<nat, Seq<AEntry>>, t: nat, ci: nat, vlog: Seq<AEntry>, clog: Seq<AEntry>, hi: nat,
)
    requires
        m.dom().contains(t),
        1 <= ci <= m[t].len(),
        m[t][ci - 1].term == t,
        terms_le(m[t], t),
        prefix_eq(vlog, m[t], ci),
        log_wf(vlog),
        log_pinned(m, clog),
        terms_lt(clog, hi),
        up_to_date(clog, vlog),
        mid_compliant(m, t, hi, ci),
        t < hi,
    ensures
        prefix_eq(clog, m[t], ci),
{
    // The voter's last term is at least t (its entry at ci-1 has term t).
    assert(vlog[ci - 1].term == t);
    assert(last_term(vlog) >= t) by {
        assert(vlog[ci - 1].term <= vlog[vlog.len() - 1].term);
    }
    let lv = last_term(vlog);
    let lc = last_term(clog);
    let cl = clog.len();
    if lc == t {
        // Equal last terms: clog is at least as long as vlog, and its last
        // entry pins it to m[t] through cl >= ci.
        assert(lv == t && cl >= vlog.len() >= ci);
        assert(clog[cl - 1].term == t);
        assert(pinned_at(m, clog, cl - 1));
        assert forall|k: int| 0 <= k < ci implies clog[k] == m[t][k] by {
            assert(clog[k] == m[t][k]);
        }
    } else {
        // clog ends in an entry of a term in (t, hi); that term's leader log
        // complies, and clog must reach past ci (else its high-term last
        // entry would equal a low-term committed one).
        assert(lc > t) by {
            if lc == lv {
                assert(cl >= vlog.len());
            }
        }
        assert(cl >= 1) by {
            assert(lc >= 1);
        }
        assert(clog[cl - 1].term == lc);
        assert(pinned_at(m, clog, cl - 1));
        assert(m.dom().contains(lc));
        assert(lc < hi);
        assert(prefix_eq(m[lc], m[t], ci));
        assert(cl >= ci) by {
            if cl < ci {
                assert(clog[cl - 1] == m[lc][cl - 1]);
                assert(m[lc][cl - 1] == m[t][cl - 1]);
                assert(m[t][cl - 1].term <= t);
                assert(false);
            }
        }
        assert forall|k: int| 0 <= k < ci implies clog[k] == m[t][k] by {
            assert(clog[k] == m[lc][k]);
            assert(m[lc][k] == m[t][k]);
        }
    }
}

/// A splice whose entries come from a source log that agrees with the target
/// on the first `k` entries preserves agreement with the target on those
/// entries: no conflict can arise below `k`, so nothing there is truncated.
pub proof fn lemma_splice_prefix(
    log: Seq<AEntry>, b: nat, entries: Seq<AEntry>, src: Seq<AEntry>, tgt: Seq<AEntry>, k: nat,
)
    requires
        b <= log.len(),
        prefix_eq(log, tgt, k),
        prefix_eq(src, tgt, k),
        b + entries.len() <= src.len(),
        forall|j: int| 0 <= j < entries.len() ==> #[trigger] entries[j] == src[b + j],
    ensures
        prefix_eq(splice(log, b, entries), tgt, k),
{
    if !splice_is_noop(log, b, entries) {
        let r = log.subrange(0, b as int) + entries;
        assert(r == splice(log, b, entries));
        if b < k {
            // If the entries ended below k they would all match the log
            // (both sides agree with tgt), i.e. the splice would be a noop.
            if b + entries.len() < k {
                assert forall|j: int| 0 <= j < entries.len() implies log[b + j] == entries[j] by {
                    assert(entries[j] == src[b + j]);
                    assert(src[b + j] == tgt[b + j]);
                    assert(log[b + j] == tgt[b + j]);
                }
                assert(splice_is_noop(log, b, entries));
                assert(false);
            }
            assert forall|j: int| 0 <= j < k implies r[j] == tgt[j] by {
                if j < b {
                    assert(r[j] == log[j]);
                } else {
                    assert(r[j] == entries[j - b]);
                    assert(entries[j - b] == src[j]);
                }
            }
        } else {
            assert forall|j: int| 0 <= j < k implies r[j] == tgt[j] by {
                assert(r[j] == log[j]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Transitions
// ---------------------------------------------------------------------------

/// Ghost components untouched by most transitions.
pub open spec fn unch_ghost(pre: GState, post: GState) -> bool {
    &&& post.leader_log == pre.leader_log
    &&& post.leader_of == pre.leader_of
    &&& post.voters == pre.voters
    &&& post.elect_log == pre.elect_log
    &&& post.elect_votes == pre.elect_votes
    &&& post.commits == pre.commits
    &&& post.reads == pre.reads
    &&& post.read_hwm == pre.read_hwm
}

/// Election bookkeeping untouched.
pub open spec fn unch_elect(pre: GState, post: GState) -> bool {
    &&& post.leader_of == pre.leader_of
    &&& post.voters == pre.voters
    &&& post.elect_log == pre.elect_log
    &&& post.elect_votes == pre.elect_votes
}

/// Read tracking untouched.
pub open spec fn unch_reads(pre: GState, post: GState) -> bool {
    &&& post.reads == pre.reads
    &&& post.read_hwm == pre.read_hwm
}

/// `RawNode::<Candidate>::campaign` (also reached via
/// `Follower::into_candidate`): bump the term, vote for self, solicit votes.
/// The candidate's self-vote is modeled as a `Vote` message for uniformity.
pub open spec fn t_campaign(pre: GState, post: GState, i: int) -> bool {
    let h = pre.hosts[i];
    let t = (h.term + 1) as nat;
    &&& 0 <= i < pre.n
    &&& !(h.role is Leader)  // leaders never campaign
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        term: t,
        vote: Some(i),
        role: MRole::Candidate,
        votes: Set::empty().insert(i),
        vote_logs: Map::empty().insert(i, h.log),
        ..h
    })
    &&& post.net == pre.net
        .insert(Msg::Campaign { c: i, term: t, clog: h.log })
        .insert(Msg::Vote { v: i, c: i, term: t, vlog: h.log })
    &&& unch_ghost(pre, post)
}

/// A follower grants a vote (`Message::Campaign` handling): only if it hasn't
/// voted for someone else this term, and only if the candidate's log is at
/// least as up-to-date (section 5.4.1). A higher-term campaign first steps
/// the receiver into the new term (`into_follower(term, None)`).
pub open spec fn t_grant(pre: GState, post: GState, v: int, c: int, t: nat, clog: Seq<AEntry>) -> bool {
    let h = pre.hosts[v];
    &&& 0 <= v < pre.n
    &&& v != c
    &&& pre.net.contains(Msg::Campaign { c, term: t, clog })
    &&& t >= h.term
    &&& t == h.term ==> h.role is Follower && (h.vote is None || h.vote == Some(c))
    &&& up_to_date(clog, h.log)
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(v, MHost {
        term: t,
        vote: Some(c),
        role: MRole::Follower,
        ..h
    })
    &&& post.net == pre.net.insert(Msg::Vote { v, c, term: t, vlog: h.log })
    &&& unch_ghost(pre, post)
}

/// A candidate records a granted vote (`Message::CampaignResponse` handling).
pub open spec fn t_collect_vote(pre: GState, post: GState, i: int, v: int, vlog: Seq<AEntry>) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& h.role is Candidate
    &&& pre.net.contains(Msg::Vote { v, c: i, term: h.term, vlog })
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        votes: h.votes.insert(v),
        vote_logs: h.vote_logs.insert(v, vlog),
        ..h
    })
    &&& post.net == pre.net
    &&& unch_ghost(pre, post)
}

/// `Candidate::into_leader`: with a vote quorum, become leader and append the
/// noop entry (section 5.4.2). Registers the term's definitive leader log and
/// freezes the election evidence.
pub open spec fn t_become_leader(pre: GState, post: GState, i: int) -> bool {
    let h = pre.hosts[i];
    let newlog = h.log.push(AEntry { term: h.term, cmd: None });
    &&& 0 <= i < pre.n
    &&& h.role is Candidate
    &&& is_quorum(pre.n, h.votes)
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        role: MRole::Leader,
        log: newlog,
        read_seq: 0,
        ..h
    })
    &&& post.net == pre.net
    &&& post.leader_log == pre.leader_log.insert(h.term, newlog)
    &&& post.leader_of == pre.leader_of.insert(h.term, i)
    &&& post.voters == pre.voters.insert(h.term, h.votes)
    &&& post.elect_log == pre.elect_log.insert(h.term, h.log)
    &&& post.elect_votes == pre.elect_votes.insert(h.term, h.vote_logs)
    &&& post.commits == pre.commits
    &&& unch_reads(pre, post)
}

/// `RawNode::<Leader>::propose`: append a client command to the leader's log.
pub open spec fn t_propose(pre: GState, post: GState, i: int, cmd: Option<Seq<u8>>) -> bool {
    let h = pre.hosts[i];
    let newlog = h.log.push(AEntry { term: h.term, cmd });
    &&& 0 <= i < pre.n
    &&& h.role is Leader
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost { log: newlog, ..h })
    &&& post.net == pre.net
    &&& post.leader_log == pre.leader_log.insert(h.term, newlog)
    &&& post.commits == pre.commits
    &&& unch_elect(pre, post)
    &&& unch_reads(pre, post)
}

/// `Leader::maybe_send_append`: send any window [b, e) of the leader's log,
/// with the entry before it as base. (The impl sends specific windows driven
/// by next_index; the model allows any, a superset.)
pub open spec fn t_send_append(pre: GState, post: GState, i: int, b: nat, e: nat) -> bool {
    let h = pre.hosts[i];
    let bt: nat = if b == 0 { 0 } else { h.log[b - 1].term };
    &&& 0 <= i < pre.n
    &&& h.role is Leader
    &&& b <= e <= h.log.len()
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts
    &&& post.net == pre.net.insert(Msg::Append {
        term: h.term,
        base: b,
        bterm: bt,
        entries: h.log.subrange(b as int, e as int),
    })
    &&& unch_ghost(pre, post)
}

/// `Message::Append` handling in `RawNode::<Follower>::step` (candidates step
/// down first; leaders can't see same-term appends, see the panic there): if
/// the base entry matches, splice the entries and ack the resulting match
/// index. A higher-term append first steps the receiver into the new term.
/// Rejections don't change state and are elided.
pub open spec fn t_recv_append(
    pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>,
) -> bool {
    let h = pre.hosts[i];
    let newlog = splice(h.log, b, entries);
    let newvote: Option<int> = if t > h.term { None } else { h.vote };
    &&& 0 <= i < pre.n
    &&& pre.net.contains(Msg::Append { term: t, base: b, bterm: bt, entries })
    &&& t >= h.term
    &&& !(h.role is Leader && t == h.term)
    &&& b == 0 || (b <= h.log.len() && h.log[b - 1].term == bt)
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        term: t,
        vote: newvote,
        role: MRole::Follower,
        log: newlog,
        ..h
    })
    &&& post.net == pre.net.insert(Msg::Ack { v: i, term: t, mi: (b + entries.len()) as nat })
    &&& unch_ghost(pre, post)
}

/// A heartbeat-response match (`Message::Heartbeat` handling: match_index =
/// last_index when `log.has(last_index, msg.term)`), and the leader's own
/// match of its last index (`maybe_commit_and_apply` chains `[last_index]`).
/// Any host whose log has an entry of its own current term at `mi` matched
/// that term's leader log up to there.
pub open spec fn t_send_ack(pre: GState, post: GState, i: int, mi: nat) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& 1 <= mi <= h.log.len()
    &&& h.log[mi - 1].term == h.term
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts
    &&& post.net == pre.net.insert(Msg::Ack { v: i, term: h.term, mi })
    &&& unch_ghost(pre, post)
}

/// `Leader::maybe_commit_and_apply`: commit index `ci` once a quorum's match
/// indexes reach it, but only if the entry at `ci` is from the leader's own
/// term (section 5.4.2). Also announces the commit (heartbeat commit_index).
pub open spec fn t_leader_commit(pre: GState, post: GState, i: int, ci: nat, q: Map<int, nat>) -> bool {
    let h = pre.hosts[i];
    let rec = CommitRec { term: h.term, ci, q };
    let newcommit: nat = if ci > h.commit { ci } else { h.commit };
    let newcrec: CommitRec = if ci > h.commit { rec } else { h.crec };
    &&& 0 <= i < pre.n
    &&& h.role is Leader
    &&& 1 <= ci <= h.log.len()
    &&& h.log[ci - 1].term == h.term
    &&& is_quorum(pre.n, q.dom())
    &&& forall|v: int| q.dom().contains(v) ==>
            (#[trigger] q[v]) >= ci && pre.net.contains(Msg::Ack { v, term: h.term, mi: q[v] })
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost { commit: newcommit, crec: newcrec, ..h })
    &&& post.net == pre.net.insert(Msg::Commit { term: h.term, ci, rec })
    &&& post.leader_log == pre.leader_log
    &&& post.commits == pre.commits.insert(rec)
    &&& unch_elect(pre, post)
    &&& unch_reads(pre, post)
}

/// `Leader::heartbeat`: re-announce any committed index.
pub open spec fn t_send_commit(pre: GState, post: GState, i: int, ci: nat) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& h.role is Leader
    &&& 1 <= ci <= h.commit
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts
    &&& post.net == pre.net.insert(Msg::Commit { term: h.term, ci, rec: h.crec })
    &&& unch_ghost(pre, post)
}

/// `Message::Heartbeat` commit handling: a host that matched the current
/// term's leader log at `mi >= ci` advances its commit index to `ci`.
pub open spec fn t_recv_commit(pre: GState, post: GState, i: int, ci: nat, mi: nat, rec: CommitRec) -> bool {
    let h = pre.hosts[i];
    let newcommit: nat = if ci > h.commit { ci } else { h.commit };
    let newcrec: CommitRec = if ci > h.commit { rec } else { h.crec };
    &&& 0 <= i < pre.n
    &&& pre.net.contains(Msg::Commit { term: h.term, ci, rec })
    &&& ci <= mi <= h.log.len()
    &&& 1 <= mi
    &&& h.log[mi - 1].term == h.term
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost { commit: newcommit, crec: newcrec, ..h })
    &&& post.net == pre.net
    &&& unch_ghost(pre, post)
}

/// Discovering a higher term (`into_follower(term, None)` on any
/// higher-term message, before the message itself is stepped): become a
/// leaderless follower in the new term with a cleared vote. Modeled as a
/// spontaneous step — it only removes power, so safety cannot depend on
/// what prompted it — which also covers a crash between the term bump and
/// the follow-up step.
pub open spec fn t_bump_term(pre: GState, post: GState, i: int, t: nat) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& t > h.term
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        term: t,
        vote: None,
        role: MRole::Follower,
        ..h
    })
    &&& post.net == pre.net
    &&& unch_ghost(pre, post)
}

/// A candidate stepping down to follower in its own term
/// (`Candidate::into_follower(term, Some(leader))` on discovering the
/// election's winner). Only the volatile role changes.
pub open spec fn t_step_down(pre: GState, post: GState, i: int) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& h.role is Candidate
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost { role: MRole::Follower, ..h })
    &&& post.net == pre.net
    &&& unch_ghost(pre, post)
}

/// A crash-restart (`Node::new` after restart): durable state (term, vote,
/// log) survives; volatile role state resets to follower. The commit index
/// is not fsynced (`Log::commit`), so the recovered value `c` may lag the
/// pre-crash one — it is recovered from the quorum later. The commit witness
/// `crec` is kept: it still covers the (smaller) committed prefix.
pub open spec fn t_restart(pre: GState, post: GState, i: int, c: nat) -> bool {
    let h = pre.hosts[i];
    &&& 0 <= i < pre.n
    &&& c <= h.commit
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        role: MRole::Follower,
        commit: c,
        votes: Set::empty(),
        vote_logs: Map::empty(),
        read_seq: 0,
        ..h
    })
    &&& post.net == pre.net
    &&& unch_ghost(pre, post)
}

/// `Message::ClientRequest { Read }` handling on the leader: assign the next
/// read sequence number and broadcast it for quorum confirmation. The ghost
/// read record snapshots the commit records existing at submission.
pub open spec fn t_submit_read(pre: GState, post: GState, i: int) -> bool {
    let h = pre.hosts[i];
    let s = (h.read_seq + 1) as nat;
    &&& 0 <= i < pre.n
    &&& h.role is Leader
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost { read_seq: s, ..h })
    &&& post.net == pre.net
        .insert(Msg::Read { term: h.term, seq: s })
        .insert(Msg::ReadConfirm { v: i, term: h.term, seq: s })
    &&& post.leader_log == pre.leader_log
    &&& post.commits == pre.commits
    &&& unch_elect(pre, post)
    &&& post.reads == pre.reads.insert(ReadRec { term: h.term, seq: s, born: pre.commits })
    &&& post.read_hwm == pre.read_hwm.insert(h.term, s)
}

/// `Message::Read` handling: a follower confirms the leader's read sequence
/// number. A higher-term read first steps the receiver into the new term.
pub open spec fn t_confirm_read(pre: GState, post: GState, i: int, t: nat, s: nat) -> bool {
    let h = pre.hosts[i];
    let newvote: Option<int> = if t > h.term { None } else { h.vote };
    &&& 0 <= i < pre.n
    &&& pre.net.contains(Msg::Read { term: t, seq: s })
    &&& t >= h.term
    &&& !(h.role is Leader && t == h.term)
    &&& post.n == pre.n
    &&& post.hosts == pre.hosts.update(i, MHost {
        term: t,
        vote: newvote,
        role: MRole::Follower,
        ..h
    })
    &&& post.net == pre.net.insert(Msg::ReadConfirm { v: i, term: t, seq: s })
    &&& unch_ghost(pre, post)
}

/// One protocol step, as a labeled transition.
pub enum TStep {
    Campaign { i: int },
    Grant { v: int, c: int, term: nat, clog: Seq<AEntry> },
    CollectVote { i: int, v: int, vlog: Seq<AEntry> },
    BecomeLeader { i: int },
    Propose { i: int, cmd: Option<Seq<u8>> },
    SendAppend { i: int, b: nat, e: nat },
    RecvAppend { i: int, term: nat, base: nat, bterm: nat, entries: Seq<AEntry> },
    SendAck { i: int, mi: nat },
    LeaderCommit { i: int, ci: nat, q: Map<int, nat> },
    SendCommit { i: int, ci: nat },
    RecvCommit { i: int, ci: nat, mi: nat, rec: CommitRec },
    BumpTerm { i: int, term: nat },
    StepDown { i: int },
    Restart { i: int, commit: nat },
    SubmitRead { i: int },
    ConfirmRead { i: int, term: nat, seq: nat },
}

pub open spec fn next_step(pre: GState, post: GState, step: TStep) -> bool {
    match step {
        TStep::Campaign { i } => t_campaign(pre, post, i),
        TStep::Grant { v, c, term, clog } => t_grant(pre, post, v, c, term, clog),
        TStep::CollectVote { i, v, vlog } => t_collect_vote(pre, post, i, v, vlog),
        TStep::BecomeLeader { i } => t_become_leader(pre, post, i),
        TStep::Propose { i, cmd } => t_propose(pre, post, i, cmd),
        TStep::SendAppend { i, b, e } => t_send_append(pre, post, i, b, e),
        TStep::RecvAppend { i, term, base, bterm, entries } =>
            t_recv_append(pre, post, i, term, base, bterm, entries),
        TStep::SendAck { i, mi } => t_send_ack(pre, post, i, mi),
        TStep::LeaderCommit { i, ci, q } => t_leader_commit(pre, post, i, ci, q),
        TStep::SendCommit { i, ci } => t_send_commit(pre, post, i, ci),
        TStep::RecvCommit { i, ci, mi, rec } => t_recv_commit(pre, post, i, ci, mi, rec),
        TStep::BumpTerm { i, term } => t_bump_term(pre, post, i, term),
        TStep::StepDown { i } => t_step_down(pre, post, i),
        TStep::Restart { i, commit } => t_restart(pre, post, i, commit),
        TStep::SubmitRead { i } => t_submit_read(pre, post, i),
        TStep::ConfirmRead { i, term, seq } => t_confirm_read(pre, post, i, term, seq),
    }
}

pub open spec fn next(pre: GState, post: GState) -> bool {
    exists|step: TStep| next_step(pre, post, step)
}

/// The initial host state: a leaderless follower at term 0 with an empty
/// log (`Node::new` on a fresh cluster; what `Abs::recover` yields over an
/// empty log).
pub open spec fn init_host() -> MHost {
    MHost {
        term: 0,
        vote: None::<int>,
        role: MRole::Follower,
        log: Seq::empty(),
        commit: 0,
        votes: Set::empty(),
        vote_logs: Map::empty(),
        crec: CommitRec { term: 0, ci: 0, q: Map::empty() },
        read_seq: 0,
    }
}

/// The initial state: every node in the initial host state.
pub open spec fn init(s: GState) -> bool {
    &&& s.n >= 1
    &&& s.hosts.len() == s.n
    &&& forall|i: int| 0 <= i < s.n ==> s.hosts[i] == init_host()
    &&& s.net == Set::<Msg>::empty()
    &&& s.leader_log == Map::<nat, Seq<AEntry>>::empty()
    &&& s.leader_of == Map::<nat, int>::empty()
    &&& s.voters == Map::<nat, Set<int>>::empty()
    &&& s.elect_log == Map::<nat, Seq<AEntry>>::empty()
    &&& s.elect_votes == Map::<nat, Map<int, Seq<AEntry>>>::empty()
    &&& s.commits == Set::<CommitRec>::empty()
    &&& s.reads == Set::<ReadRec>::empty()
    &&& s.read_hwm == Map::<nat, nat>::empty()
}

/// An execution: a nonempty sequence of states, starting at init, stepping
/// via next.
pub open spec fn execution(ex: Seq<GState>) -> bool {
    &&& ex.len() >= 1
    &&& init(ex[0])
    &&& forall|k: int| 0 <= k < ex.len() - 1 ==> next(#[trigger] ex[k], ex[k + 1])
}

// ---------------------------------------------------------------------------
// Invariants: structural well-formedness
// ---------------------------------------------------------------------------

/// Well-formedness of a single log: terms are >= 1 and nondecreasing
/// (enforced by the verified `raft::log` transitions on each host).
pub open spec fn log_wf(log: Seq<AEntry>) -> bool {
    &&& forall|j: int| 0 <= j < log.len() ==> (#[trigger] log[j]).term >= 1
    &&& forall|j1: int, j2: int| 0 <= j1 <= j2 < log.len() ==> (#[trigger] log[j1]).term <= (#[trigger] log[j2]).term
}

/// All entry terms at or below `t`.
pub open spec fn terms_le(log: Seq<AEntry>, t: nat) -> bool {
    forall|j: int| 0 <= j < log.len() ==> (#[trigger] log[j]).term <= t
}

/// All entry terms strictly below `t`.
pub open spec fn terms_lt(log: Seq<AEntry>, t: nat) -> bool {
    forall|j: int| 0 <= j < log.len() ==> (#[trigger] log[j]).term < t
}

/// Structural well-formedness of the global state.
pub open spec fn inv_wf(s: GState) -> bool {
    &&& s.n >= 1
    &&& s.hosts.len() == s.n
}

// ---------------------------------------------------------------------------
// Invariants: per-host state
// ---------------------------------------------------------------------------

/// Per-host invariant.
pub open spec fn host_ok(s: GState, i: int) -> bool {
    let h = s.hosts[i];
    &&& log_wf(h.log)
    &&& terms_le(h.log, h.term)
    &&& log_pinned(s.leader_log, h.log)
    &&& h.votes.subset_of(node_ids(s.n))
    &&& (h.vote matches Some(c) ==> 0 <= c < s.n)
    // Candidates: campaigned in their current term with their current log,
    // voted for themselves, only hold entries from before their term, only
    // count granted votes, and are not the recorded winner of their term
    // (they could only re-enter candidacy at a higher term).
    &&& (h.role is Candidate ==> {
        &&& h.term >= 1
        &&& h.vote == Some(i)
        &&& s.net.contains(Msg::Campaign { c: i, term: h.term, clog: h.log })
        &&& terms_lt(h.log, h.term)
        &&& forall|v: int| #[trigger] h.votes.contains(v) ==> {
            &&& h.vote_logs.dom().contains(v)
            &&& s.net.contains(Msg::Vote { v, c: i, term: h.term, vlog: h.vote_logs[v] })
        }
        &&& s.leader_of.dom().contains(h.term) ==> s.leader_of[h.term] != i
    })
    // Leaders: recorded as their term's unique winner, and their log is the
    // term's definitive leader log; read sequence numbers track the ghost
    // high-water mark.
    &&& (h.role is Leader ==> {
        &&& h.term >= 1
        &&& h.vote == Some(i)
        &&& s.leader_log.dom().contains(h.term)
        &&& s.leader_of[h.term] == i
        &&& s.leader_log[h.term] == h.log
        &&& (s.read_hwm.dom().contains(h.term) ==> s.read_hwm[h.term] == h.read_seq)
        &&& (!s.read_hwm.dom().contains(h.term) ==> h.read_seq == 0)
    })
}

pub open spec fn inv_hosts(s: GState) -> bool {
    forall|i: int| 0 <= i < s.n ==> #[trigger] host_ok(s, i)
}

// ---------------------------------------------------------------------------
// Invariants: messages
// ---------------------------------------------------------------------------

/// Campaign messages carry the candidate's log at campaign time; the
/// candidate's term never regresses below it, and campaign logs only hold
/// entries from before the campaigned term.
pub open spec fn campaign_msg_ok(s: GState, c: int, t: nat, clog: Seq<AEntry>) -> bool {
    &&& 0 <= c < s.n
    &&& t >= 1
    &&& s.hosts[c].term >= t
    &&& log_wf(clog)
    &&& terms_lt(clog, t)
    &&& log_pinned(s.leader_log, clog)
}

/// Vote messages: the voter's term never regresses below the voted term, and
/// while the voter remains in that term its recorded vote is this vote (the
/// vote-once-per-term rule of `set_term_vote`). While the candidate is still
/// campaigning in that term, its (unchanged) log passed the section 5.4.1
/// up-to-date check against the voter's grant-time log.
pub open spec fn vote_msg_ok(s: GState, v: int, c: int, t: nat, vlog: Seq<AEntry>) -> bool {
    &&& 0 <= v < s.n
    &&& 0 <= c < s.n
    &&& t >= 1
    &&& s.hosts[v].term >= t
    &&& (s.hosts[v].term == t ==> s.hosts[v].vote == Some(c))
    &&& s.hosts[c].term >= t  // votes require a campaign, which requires this
    &&& log_wf(vlog)
    &&& terms_le(vlog, t)
    &&& log_pinned(s.leader_log, vlog)
    &&& (s.hosts[c].role is Candidate && s.hosts[c].term == t ==> up_to_date(s.hosts[c].log, vlog))
}

/// Append messages carry a window of the sending leader's log.
pub open spec fn append_msg_ok(s: GState, t: nat, b: nat, bt: nat, entries: Seq<AEntry>) -> bool {
    &&& t >= 1
    &&& s.leader_log.dom().contains(t)
    &&& b + entries.len() <= s.leader_log[t].len()
    &&& forall|j: int| 0 <= j < entries.len() ==> #[trigger] entries[j] == s.leader_log[t][b + j]
    &&& (b >= 1 ==> b <= s.leader_log[t].len() && bt == s.leader_log[t][b - 1].term)
    &&& (b == 0 ==> bt == 0)
}

/// Ack messages: host `v` matched the leader-of-`t`'s log up to `mi` when its
/// term was `t`; while it remains in term `t` the match persists (only
/// same-term leader appends can touch its log, and they never conflict below
/// an acked index).
pub open spec fn ack_msg_ok(s: GState, v: int, t: nat, mi: nat) -> bool {
    &&& 0 <= v < s.n
    &&& t >= 1
    &&& s.hosts[v].term >= t
    &&& s.leader_log.dom().contains(t)
    &&& mi <= s.leader_log[t].len()
    &&& (s.hosts[v].term == t ==> prefix_eq(s.hosts[v].log, s.leader_log[t], mi))
}

pub open spec fn inv_msgs(s: GState) -> bool {
    &&& forall|c: int, t: nat, clog: Seq<AEntry>|
            #[trigger] s.net.contains(Msg::Campaign { c, term: t, clog }) ==> campaign_msg_ok(s, c, t, clog)
    // A node campaigns at most once per term (each campaign bumps the term).
    &&& forall|c: int, t: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
            #[trigger] s.net.contains(Msg::Campaign { c, term: t, clog: l1 })
            && #[trigger] s.net.contains(Msg::Campaign { c, term: t, clog: l2 }) ==> l1 == l2
    &&& forall|v: int, c: int, t: nat, vlog: Seq<AEntry>|
            #[trigger] s.net.contains(Msg::Vote { v, c, term: t, vlog }) ==> vote_msg_ok(s, v, c, t, vlog)
    // Vote once per term: all votes by `v` in term `t` name the same candidate.
    &&& forall|v: int, c1: int, t: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
            #[trigger] s.net.contains(Msg::Vote { v, c: c1, term: t, vlog: l1 })
            && #[trigger] s.net.contains(Msg::Vote { v, c: c2, term: t, vlog: l2 }) ==> c1 == c2
    &&& forall|t: nat, b: nat, bt: nat, entries: Seq<AEntry>|
            #[trigger] s.net.contains(Msg::Append { term: t, base: b, bterm: bt, entries }) ==> append_msg_ok(s, t, b, bt, entries)
    &&& forall|v: int, t: nat, mi: nat|
            #[trigger] s.net.contains(Msg::Ack { v, term: t, mi }) ==> ack_msg_ok(s, v, t, mi)
}

// ---------------------------------------------------------------------------
// Invariants: per-term leader logs and election evidence
// ---------------------------------------------------------------------------

/// The persistence evidence frozen into an election record: for any ack the
/// voter `w` had cast in an earlier term `t`, if every leader elected
/// strictly between `t` and `u` kept the acked prefix, then `w`'s grant-time
/// log `vlog` kept it too. Unlike `vote_persist_ok` the range excludes `u`:
/// when the winning votes were cast no leader of `u` existed yet, so no
/// leader-of-`u` append could have touched the voters' logs. New acks by `w`
/// in terms below `u` can never appear later (its term is already >= u).
pub open spec fn frozen_persist_at(s: GState, u: nat, vlog: Seq<AEntry>, t: nat, mi: nat) -> bool {
    forall|i: nat| i <= mi && #[trigger] mid_compliant(s.leader_log, t, u, i) ==>
        prefix_eq(vlog, s.leader_log[t], i)
}

pub open spec fn frozen_persist_ok(s: GState, u: nat, vlog: Seq<AEntry>, w: int) -> bool {
    forall|t: nat, mi: nat| t < u && #[trigger] s.net.contains(Msg::Ack { v: w, term: t, mi }) ==>
        frozen_persist_at(s, u, vlog, t, mi)
}

/// Per-voter election evidence: the winning quorum member's vote message,
/// the up-to-date check it passed against the winner's election log, and its
/// frozen persistence evidence.
pub open spec fn voter_ok(s: GState, u: nat, x: int) -> bool {
    let vlog = s.elect_votes[u][x];
    &&& s.elect_votes[u].dom().contains(x)
    &&& s.net.contains(Msg::Vote { v: x, c: s.leader_of[u], term: u, vlog })
    &&& up_to_date(s.elect_log[u], vlog)
    &&& frozen_persist_ok(s, u, vlog, x)
}

/// Per-elected-term invariant: the term's leader log is nonempty, ends in an
/// entry of that term (the election noop), holds no later entries, and the
/// recorded winner's term never regresses below it. The winner was elected by
/// the recorded vote quorum, each member's grant-time log dominated by the
/// winner's frozen election log.
pub open spec fn lterm_ok(s: GState, u: nat) -> bool {
    let ll = s.leader_log[u];
    let elog = s.elect_log[u];
    &&& u >= 1
    &&& ll.len() >= 1
    &&& log_wf(ll)
    &&& terms_le(ll, u)
    &&& log_pinned(s.leader_log, ll)
    &&& last_term(ll) == u
    &&& 0 <= s.leader_of[u] < s.n
    &&& s.hosts[s.leader_of[u]].term >= u
    &&& s.voters.dom().contains(u)
    &&& s.elect_log.dom().contains(u)
    &&& s.elect_votes.dom().contains(u)
    &&& is_quorum(s.n, s.voters[u])
    &&& prefix_eq(ll, elog, elog.len())
    &&& elog.len() < ll.len()
    &&& ll[elog.len() as int].term == u
    &&& terms_lt(elog, u)
    &&& log_wf(elog)
    &&& forall|x: int| #[trigger] s.voters[u].contains(x) ==> voter_ok(s, u, x)
}

pub open spec fn inv_lterms(s: GState) -> bool {
    &&& s.leader_of.dom() == s.leader_log.dom()
    &&& s.read_hwm.dom().subset_of(s.leader_log.dom())
    &&& forall|u: nat| #[trigger] s.leader_log.dom().contains(u) ==> lterm_ok(s, u)
}

// ---------------------------------------------------------------------------
// Invariants: acked-prefix persistence (the leader-completeness engine)
// ---------------------------------------------------------------------------

/// The leader logs of all elected terms strictly between `t` and `ub` agree
/// with `m[t]` on the first `i` entries.
pub open spec fn mid_compliant(m: Map<nat, Seq<AEntry>>, t: nat, ub: nat, i: nat) -> bool {
    forall|x: nat| t < x < ub && #[trigger] m.dom().contains(x) ==> prefix_eq(m[x], m[t], i)
}

/// K2c: while every leader elected after term `t` (up to the acker's current
/// term) has kept the acked prefix in its own log, the acker's log keeps it
/// too — later leaders' appends then never conflict below it. (With no such
/// leaders the condition is vacuous and the acked prefix simply persists.)
pub open spec fn ack_persist_ok(s: GState, v: int, t: nat, mi: nat) -> bool {
    forall|i: nat| i <= mi
        && #[trigger] mid_compliant(s.leader_log, t, (s.hosts[v].term + 1) as nat, i) ==>
        prefix_eq(s.hosts[v].log, s.leader_log[t], i)
}

pub open spec fn inv_ack_persist(s: GState) -> bool {
    forall|v: int, t: nat, mi: nat| #[trigger] s.net.contains(Msg::Ack { v, term: t, mi }) ==>
        ack_persist_ok(s, v, t, mi)
}

/// K3'': the same persistence, frozen into the log a voter reported when
/// granting a vote in a later term `u`. The compliance range includes `u`
/// itself: a voter that was already spliced by the leader of `u` (a re-grant
/// after an election) is covered by requiring that leader's compliance too.
pub open spec fn vote_persist_ok(s: GState, u: nat, vlog: Seq<AEntry>, t: nat, mi: nat) -> bool {
    forall|i: nat| i <= mi && #[trigger] mid_compliant(s.leader_log, t, (u + 1) as nat, i) ==>
        prefix_eq(vlog, s.leader_log[t], i)
}

pub open spec fn inv_vote_persist(s: GState) -> bool {
    forall|v: int, c: int, u: nat, vlog: Seq<AEntry>, t: nat, mi: nat|
        #[trigger] s.net.contains(Msg::Vote { v, c, term: u, vlog })
        && #[trigger] s.net.contains(Msg::Ack { v, term: t, mi })
        && t < u ==> vote_persist_ok(s, u, vlog, t, mi)
}

/// Compliance over a wider term range implies compliance over a narrower one.
pub proof fn lemma_mid_narrow(m: Map<nat, Seq<AEntry>>, t: nat, ub1: nat, ub2: nat, i: nat)
    requires
        ub1 <= ub2,
        mid_compliant(m, t, ub2, i),
    ensures
        mid_compliant(m, t, ub1, i),
{
    assert forall|x: nat| t < x < ub1 && #[trigger] m.dom().contains(x) implies prefix_eq(m[x], m[t], i) by {
        assert(t < x < ub2);
    }
}

/// Inserting a fresh term into the leader-log map cannot make a compliance
/// hypothesis easier: compliance over the extended map implies compliance
/// over the original.
pub proof fn lemma_mid_unfresh(m1: Map<nat, Seq<AEntry>>, u0: nat, log0: Seq<AEntry>, t: nat, ub: nat, i: nat)
    requires
        !m1.dom().contains(u0),
        m1.dom().contains(t),
        mid_compliant(m1.insert(u0, log0), t, ub, i),
    ensures
        mid_compliant(m1, t, ub, i),
{
    let m2 = m1.insert(u0, log0);
    assert forall|x: nat| t < x < ub && #[trigger] m1.dom().contains(x) implies prefix_eq(m1[x], m1[t], i) by {
        assert(m2.dom().contains(x));
        assert(prefix_eq(m2[x], m2[t], i));
        assert(x != u0 && t != u0);
    }
}

/// Extending one term's leader log with an entry of its own term cannot make
/// a compliance hypothesis easier either: agreement with an older term's log
/// cannot extend into the new entry (its term is too new), so agreement over
/// the extended map implies agreement over the original.
pub proof fn lemma_mid_unext(m1: Map<nat, Seq<AEntry>>, u0: nat, e: AEntry, t: nat, ub: nat, i: nat)
    requires
        m1.dom().contains(u0),
        m1.dom().contains(t),
        e.term == u0,
        terms_le(m1[t], t),
        i <= m1[t].len(),
        mid_compliant(m1.insert(u0, m1[u0].push(e)), t, ub, i),
    ensures
        mid_compliant(m1, t, ub, i),
{
    let m2 = m1.insert(u0, m1[u0].push(e));
    assert forall|x: nat| t < x < ub && #[trigger] m1.dom().contains(x) implies prefix_eq(m1[x], m1[t], i) by {
        assert(m2.dom().contains(x));
        assert(prefix_eq(m2[x], m2[t], i));
        assert(x != t);
        if x == u0 {
            // Agreement cannot reach the pushed entry: its term is x > t while
            // m[t]'s entries are at most t.
            if i > m1[u0].len() {
                let p = m1[u0].len() as int;
                assert(m2[u0][p] == e);
                assert(m2[t][p] == m1[t][p]);
                assert(m1[t][p].term <= t);
                assert(false);
            }
            assert forall|k: int| 0 <= k < i implies m1[x][k] == m1[t][k] by {
                assert(m2[x][k] == m2[t][k]);
            }
        } else if t == u0 {
            assert forall|k: int| 0 <= k < i implies m1[x][k] == m1[t][k] by {
                assert(m2[x][k] == m2[t][k]);
                assert(m2[t][k] == m1[t][k]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Invariants: commits and leader completeness
// ---------------------------------------------------------------------------

/// CM1: a commit record is justified — its index is within the committing
/// term's leader log, the entry there is from that term itself (section
/// 5.4.2), and a quorum acked the prefix at recorded match indexes.
pub open spec fn commit_rec_ok(s: GState, rec: CommitRec) -> bool {
    &&& s.leader_log.dom().contains(rec.term)
    &&& 1 <= rec.ci <= s.leader_log[rec.term].len()
    &&& s.leader_log[rec.term][rec.ci - 1].term == rec.term
    &&& is_quorum(s.n, rec.q.dom())
    &&& forall|v: int| #[trigger] rec.q.dom().contains(v) ==>
            rec.q[v] >= rec.ci && s.net.contains(Msg::Ack { v, term: rec.term, mi: rec.q[v] })
}

pub open spec fn inv_commits(s: GState) -> bool {
    forall|rec: CommitRec| #[trigger] s.commits.contains(rec) ==> commit_rec_ok(s, rec)
}

/// D (Leader Completeness): every leader elected after a commit holds the
/// committed prefix, verbatim, in its own log.
pub open spec fn inv_leader_completeness(s: GState) -> bool {
    forall|rec: CommitRec, u: nat|
        #[trigger] s.commits.contains(rec) && #[trigger] s.leader_log.dom().contains(u)
        && u > rec.term ==>
        prefix_eq(s.leader_log[u], s.leader_log[rec.term], rec.ci)
}

/// Commit messages carry a justifying commit record covering their index, and
/// the announcing term's leader log agrees with the committed prefix.
pub open spec fn commit_msg_ok(s: GState, t: nat, ci: nat, rec: CommitRec) -> bool {
    &&& t >= 1
    &&& ci >= 1
    &&& s.leader_log.dom().contains(t)
    &&& ci <= s.leader_log[t].len()
    &&& s.commits.contains(rec)
    &&& rec.ci >= ci
    &&& rec.term <= t
    &&& prefix_eq(s.leader_log[t], s.leader_log[rec.term], ci)
}

pub open spec fn inv_commit_msgs(s: GState) -> bool {
    forall|t: nat, ci: nat, rec: CommitRec|
        #[trigger] s.net.contains(Msg::Commit { term: t, ci, rec }) ==> commit_msg_ok(s, t, ci, rec)
}

/// HC: a host's committed prefix is a committed leader-log prefix (so applied
/// state never diverges). The witnessing record rides in ghost `crec`.
pub open spec fn host_commit_ok(s: GState, i: int) -> bool {
    let h = s.hosts[i];
    h.commit > 0 ==> {
        &&& s.commits.contains(h.crec)
        &&& h.crec.ci >= h.commit
        &&& h.crec.term <= h.term
        &&& prefix_eq(h.log, s.leader_log[h.crec.term], h.commit)
    }
}

pub open spec fn inv_host_commits(s: GState) -> bool {
    forall|i: int| 0 <= i < s.n ==> #[trigger] host_commit_ok(s, i)
}

/// A committing leader's own commit index covers its records while it stays
/// leader in that term. (After a crash-restart it is a follower, possibly
/// with a regressed commit index, and can never lead that term again.) Used
/// by the linearizable-read theorem.
pub open spec fn commit_leader_ok(s: GState, rec: CommitRec) -> bool {
    let l = s.hosts[s.leader_of[rec.term]];
    l.role is Leader && l.term == rec.term ==> l.commit >= rec.ci
}

pub open spec fn inv_commit_leaders(s: GState) -> bool {
    forall|rec: CommitRec| #[trigger] s.commits.contains(rec) ==> commit_leader_ok(s, rec)
}

// ---------------------------------------------------------------------------
// Invariants: linearizable reads
// ---------------------------------------------------------------------------

/// Read broadcasts carry sequence numbers at or below the term's high-water
/// mark.
pub open spec fn read_msg_ok(s: GState, t: nat, sq: nat) -> bool {
    &&& s.read_hwm.dom().contains(t)
    &&& 1 <= sq <= s.read_hwm[t]
}

/// Read confirmations: sent by a host whose term was `t` (and never
/// regresses), for an issued sequence number.
pub open spec fn confirm_msg_ok(s: GState, v: int, t: nat, sq: nat) -> bool {
    &&& 0 <= v < s.n
    &&& s.hosts[v].term >= t
    &&& s.read_hwm.dom().contains(t)
    &&& 1 <= sq <= s.read_hwm[t]
}

/// Read records: the born set snapshots commits at submission. Members of a
/// higher-term commit's ack quorum had already moved past this read's term at
/// submission, so any of their confirmations in this term predate it (R2) —
/// the linearizability core.
pub open spec fn read_rec_ok(s: GState, r: ReadRec) -> bool {
    &&& 1 <= r.seq
    &&& s.read_hwm.dom().contains(r.term)
    &&& r.seq <= s.read_hwm[r.term]
    &&& forall|rec: CommitRec| #[trigger] r.born.contains(rec) ==> s.commits.contains(rec)
    &&& forall|rec: CommitRec, z: int, sq: nat|
            #[trigger] r.born.contains(rec) && rec.term > r.term
            && #[trigger] rec.q.dom().contains(z)
            && #[trigger] s.net.contains(Msg::ReadConfirm { v: z, term: r.term, seq: sq })
            ==> sq < r.seq
}

pub open spec fn inv_reads(s: GState) -> bool {
    &&& forall|t: nat, sq: nat| #[trigger] s.net.contains(Msg::Read { term: t, seq: sq }) ==> read_msg_ok(s, t, sq)
    &&& forall|v: int, t: nat, sq: nat|
            #[trigger] s.net.contains(Msg::ReadConfirm { v, term: t, seq: sq }) ==> confirm_msg_ok(s, v, t, sq)
    &&& forall|r: ReadRec| #[trigger] s.reads.contains(r) ==> read_rec_ok(s, r)
}

/// The invariant conjunction (grown stage by stage).
pub open spec fn inv(s: GState) -> bool {
    &&& inv_wf(s)
    &&& inv_hosts(s)
    &&& inv_msgs(s)
    &&& inv_lterms(s)
    &&& inv_ack_persist(s)
    &&& inv_vote_persist(s)
    &&& inv_commits(s)
    &&& inv_leader_completeness(s)
    &&& inv_commit_msgs(s)
    &&& inv_host_commits(s)
    &&& inv_commit_leaders(s)
    &&& inv_reads(s)
}

// ---------------------------------------------------------------------------
// Quorum intersection
// ---------------------------------------------------------------------------

/// Two quorums of the same cluster always share a node.
pub proof fn lemma_quorum_overlap(n: nat, q1: Set<int>, q2: Set<int>)
    requires
        is_quorum(n, q1),
        is_quorum(n, q2),
    ensures
        exists|v: int| q1.contains(v) && q2.contains(v),
{
    if q1.disjoint(q2) {
        vstd::set_lib::lemma_set_disjoint_lens(q1, q2);
        assert(q1.union(q2).subset_of(node_ids(n)));
        vstd::set_lib::lemma_len_subset(q1.union(q2), node_ids(n));
        vstd::set_lib::lemma_int_range(0, n as int);
        assert(node_ids(n) == vstd::set_lib::set_int_range(0, n as int));
        assert(false);
    } else {
        let v = choose|v: int| q1.contains(v) && !(!q2.contains(v));
        assert(q1.contains(v) && q2.contains(v));
    }
}

/// A candidate holding a vote quorum campaigns in a term that has not elected
/// a leader yet: an existing winner's quorum would overlap the candidate's,
/// and the shared voter's votes would name two different winners (vote-once).
pub proof fn lemma_election_fresh(s: GState, i: int)
    requires
        inv(s),
        0 <= i < s.n,
        s.hosts[i].role is Candidate,
        is_quorum(s.n, s.hosts[i].votes),
    ensures
        !s.leader_log.dom().contains(s.hosts[i].term),
{
    let h = s.hosts[i];
    let u = h.term;
    if s.leader_log.dom().contains(u) {
        assert(lterm_ok(s, u));
        let l = s.leader_of[u];
        assert(host_ok(s, i));
        assert(l != i);
        let w = s.voters[u];
        lemma_quorum_overlap(s.n, w, h.votes);
        let x = choose|x: int| w.contains(x) && h.votes.contains(x);
        // x voted for both l and i in term u.
        assert(voter_ok(s, u, x));
        assert(s.net.contains(Msg::Vote { v: x, c: l, term: u, vlog: s.elect_votes[u][x] }));
        assert(s.net.contains(Msg::Vote { v: x, c: i, term: u, vlog: h.vote_logs[x] }));
        assert(false);
    }
}

/// The heart of Leader Completeness: if the current leader of term t holds an
/// ack quorum `q` at index `ci` for an own-term entry (the section 5.4.2
/// commit condition), then every already-elected later term's leader log
/// holds the committed prefix. By strong induction on the later term u: u's
/// recorded vote quorum overlaps `q` in a voter x; every leader elected
/// between t and u complies (induction), so x's frozen grant-time log still
/// held the prefix (frozen persistence); the section 5.4.1 up-to-date check
/// then forces u's election log — and hence u's leader log — to contain it.
proof fn lemma_h2(s: GState, t: nat, ci: nat, q: Map<int, nat>, u: nat)
    requires
        inv(s),
        s.leader_log.dom().contains(t),
        1 <= ci <= s.leader_log[t].len(),
        s.leader_log[t][ci - 1].term == t,
        is_quorum(s.n, q.dom()),
        forall|v: int| #[trigger] q.dom().contains(v) ==>
            q[v] >= ci && s.net.contains(Msg::Ack { v, term: t, mi: q[v] }),
        s.leader_log.dom().contains(u),
        u > t,
    ensures
        prefix_eq(s.leader_log[u], s.leader_log[t], ci),
    decreases u,
{
    let m = s.leader_log;
    assert(lterm_ok(s, t));
    assert(lterm_ok(s, u));
    // The vote quorum of u overlaps the ack quorum.
    lemma_quorum_overlap(s.n, s.voters[u], q.dom());
    let x = choose|x: int| s.voters[u].contains(x) && q.dom().contains(x);
    assert(voter_ok(s, u, x));
    let vlog = s.elect_votes[u][x];
    let mi = q[x];
    assert(mi >= ci && s.net.contains(Msg::Ack { v: x, term: t, mi }));
    assert(frozen_persist_at(s, u, vlog, t, mi));
    // All leaders elected between t and u comply, by induction.
    assert(mid_compliant(m, t, u, ci)) by {
        assert forall|x2: nat| t < x2 < u && #[trigger] m.dom().contains(x2)
            implies prefix_eq(m[x2], m[t], ci) by {
            lemma_h2(s, t, ci, q, x2);
        }
    }
    // So the voter's grant-time log held the committed prefix.
    assert(prefix_eq(vlog, m[t], ci));
    assert(s.net.contains(Msg::Vote { v: x, c: s.leader_of[u], term: u, vlog }));
    assert(vote_msg_ok(s, x, s.leader_of[u], u, vlog));
    // The winner's election log passed the up-to-date check against vlog, so
    // it holds the prefix too; it is a pinned prefix of the leader log of u.
    let elog = s.elect_log[u];
    let elen = elog.len();
    assert(up_to_date(elog, vlog));
    assert(prefix_eq(m[u], elog, elen));
    assert(elen < m[u].len());
    lemma_pinned_transfer(m, m[u], elog);
    lemma_uptodate_prefix(m, t, ci, vlog, elog, u);
    assert forall|k: int| 0 <= k < ci implies m[u][k] == m[t][k] by {
        assert(m[u][k] == elog[k]);
        assert(elog[k] == m[t][k]);
    }
}

// ---------------------------------------------------------------------------
// Inductive invariant: initialization and preservation
// ---------------------------------------------------------------------------

pub proof fn init_implies_inv(s: GState)
    requires init(s),
    ensures inv(s),
{
    assert forall|i: int| 0 <= i < s.n implies #[trigger] host_ok(s, i) by {
        assert(s.hosts[i].votes.subset_of(node_ids(s.n)));
    }
}

proof fn campaign_preserves(pre: GState, post: GState, i: int)
    requires inv(pre), t_campaign(pre, post, i),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let t = (h.term + 1) as nat;
    let mc = Msg::Campaign { c: i, term: t, clog: h.log };
    let mv = Msg::Vote { v: i, c: i, term: t, vlog: h.log };

    // No existing campaign or vote at term t by/for i: their invariants would
    // put i's term at >= t already.
    assert forall|l2: Seq<AEntry>| !pre.net.contains(Msg::Campaign { c: i, term: t, clog: l2 }) by {
        if pre.net.contains(Msg::Campaign { c: i, term: t, clog: l2 }) {
            assert(campaign_msg_ok(pre, i, t, l2));
        }
    }
    assert forall|c2: int, l2: Seq<AEntry>| !pre.net.contains(Msg::Vote { v: i, c: c2, term: t, vlog: l2 }) by {
        if pre.net.contains(Msg::Vote { v: i, c: c2, term: t, vlog: l2 }) {
            assert(vote_msg_ok(pre, i, c2, t, l2));
        }
    }

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        if j == i {
            // Candidate facts for i.
            assert(post.net.contains(mc));
            assert(post.hosts[i].votes =~= Set::empty().insert(i));
            assert forall|v: int| #[trigger] post.hosts[i].votes.contains(v) implies {
                &&& post.hosts[i].vote_logs.dom().contains(v)
                &&& post.net.contains(Msg::Vote { v, c: i, term: t, vlog: post.hosts[i].vote_logs[v] })
            } by {
                assert(v == i);
                assert(post.hosts[i].vote_logs[i] == h.log);
            }
            // C1: if term t already has a winner, it isn't i.
            if pre.leader_of.dom().contains(t) {
                assert(pre.leader_log.dom().contains(t));
                assert(lterm_ok(pre, t));
                if pre.leader_of[t] == i {
                    assert(pre.hosts[i].term >= t);
                    assert(false);
                }
            }
        }
    }

    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        if pre.net.contains(Msg::Campaign { c, term: t2, clog }) {
            assert(campaign_msg_ok(pre, c, t2, clog));
        } else {
            assert(Msg::Campaign { c, term: t2, clog } == mc);
            assert(host_ok(pre, i));
        }
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        if pre.net.contains(Msg::Vote { v, c, term: t2, vlog }) {
            assert(vote_msg_ok(pre, v, c, t2, vlog));
            // The candidate-condition: if c == i, then pre.hosts[i].term >= t2
            // yet i is now a candidate at term t = pre term + 1 > t2, so the
            // condition is vacuous.
            if c == i && post.hosts[i].role is Candidate && post.hosts[i].term == t2 {
                assert(pre.hosts[i].term >= t2);
                assert(false);
            }
        } else {
            assert(Msg::Vote { v, c, term: t2, vlog } == mv);
            assert(host_ok(pre, i));
            assert(up_to_date(h.log, h.log));
        }
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        let m1 = Msg::Vote { v, c: c1, term: t2, vlog: l1 };
        let m2 = Msg::Vote { v, c: c2, term: t2, vlog: l2 };
        if pre.net.contains(m1) && pre.net.contains(m2) {
        } else if !pre.net.contains(m1) && !pre.net.contains(m2) {
        } else if pre.net.contains(m1) {
            // m2 is new: v == i, t2 == t; but no pre votes at (i, t).
            assert(m2 == mv);
            assert(false);
        } else {
            assert(m1 == mv);
            assert(false);
        }
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        let m1 = Msg::Campaign { c, term: t2, clog: l1 };
        let m2 = Msg::Campaign { c, term: t2, clog: l2 };
        if pre.net.contains(m1) && pre.net.contains(m2) {
        } else if !pre.net.contains(m1) && !pre.net.contains(m2) {
        } else if pre.net.contains(m1) {
            assert(m2 == mc);
            assert(false);
        } else {
            assert(m1 == mc);
            assert(false);
        }
    }
    assert forall|t2: nat, b: nat, bt: nat, entries: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }) implies append_msg_ok(post, t2, b, bt, entries) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }));
        assert(append_msg_ok(pre, t2, b, bt, entries));
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(pre.net.contains(Msg::Ack { v, term: t2, mi }));
        assert(ack_msg_ok(pre, v, t2, mi));
    }

    assert forall|u: nat| #[trigger] post.leader_log.dom().contains(u) implies lterm_ok(post, u) by {
        assert(lterm_ok(pre, u));
    }

    // Persistence: i's term grew, widening its compliance ranges; its log is
    // unchanged. The new self-vote inherits persistence from i's acks.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_persist_ok(pre, v2, t0, mi));
        if v2 == i {
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (post.hosts[v2].term + 1) as nat, i2)
                implies prefix_eq(post.hosts[v2].log, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[i].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[i].log, pre.leader_log[t0], i2));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        if pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }) {
            assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
        } else {
            assert(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 } == mv);
            assert(ack_persist_ok(pre, i, t0, mi));
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (u2 + 1) as nat, i2)
                implies prefix_eq(vlog2, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[i].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[i].log, pre.leader_log[t0], i2));
            }
        }
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

proof fn grant_preserves(pre: GState, post: GState, v: int, c: int, t: nat, clog: Seq<AEntry>)
    requires inv(pre), t_grant(pre, post, v, c, t, clog),
    ensures inv(post),
{
    let h = pre.hosts[v];
    let mv = Msg::Vote { v, c, term: t, vlog: h.log };
    assert(campaign_msg_ok(pre, c, t, clog));

    // Vote-once: any pre vote by v in term t names c.
    assert forall|c2: int, l2: Seq<AEntry>|
        pre.net.contains(Msg::Vote { v, c: c2, term: t, vlog: l2 }) implies c2 == c by {
        assert(vote_msg_ok(pre, v, c2, t, l2));
        // pre term >= t and guard t >= pre term, so pre term == t.
        assert(h.term == t);
        assert(h.vote == Some(c2));
        // guard: vote is None or Some(c)
        assert(c2 == c);
    }

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }

    assert forall|c2: int, t2: nat, clog2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c: c2, term: t2, clog: clog2 }) implies campaign_msg_ok(post, c2, t2, clog2) by {
        assert(pre.net.contains(Msg::Campaign { c: c2, term: t2, clog: clog2 }));
        assert(campaign_msg_ok(pre, c2, t2, clog2));
        if c2 == v {
            assert(post.hosts[v].term == t >= h.term);
        }
    }
    assert forall|c2: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c: c2, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c: c2, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c: c2, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c: c2, term: t2, clog: l2 }));
    }
    assert forall|v2: int, c2: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: t2, vlog }) implies vote_msg_ok(post, v2, c2, t2, vlog) by {
        if pre.net.contains(Msg::Vote { v: v2, c: c2, term: t2, vlog }) {
            assert(vote_msg_ok(pre, v2, c2, t2, vlog));
            if v2 == v {
                // v's term moved to t >= pre term; vote became Some(c).
                if post.hosts[v].term == t2 {
                    // t == t2 and pre term >= t2 means pre term == t == t2.
                    assert(h.term == t2);
                    assert(h.vote == Some(c2));
                    assert(c2 == c);
                }
            }
            if c2 == v {
                // v is no longer a candidate.
                assert(!(post.hosts[v].role is Candidate));
            }
        } else {
            assert(Msg::Vote { v: v2, c: c2, term: t2, vlog } == mv);
            // New vote: establish vote_msg_ok.
            assert(host_ok(pre, v));
            assert(post.hosts[v].term == t && post.hosts[v].vote == Some(c));
            assert(terms_le(h.log, t));
            // Candidate-condition: if c is a candidate in term t now, its log
            // is the campaigned log (campaign uniqueness), which passed the
            // up-to-date check.
            if post.hosts[c].role is Candidate && post.hosts[c].term == t {
                assert(host_ok(pre, c));
                assert(pre.net.contains(Msg::Campaign { c, term: t, clog: pre.hosts[c].log }));
                assert(clog == pre.hosts[c].log);
                assert(up_to_date(post.hosts[c].log, h.log));
            }
        }
    }
    assert forall|v2: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        let m1 = Msg::Vote { v: v2, c: c1, term: t2, vlog: l1 };
        let m2 = Msg::Vote { v: v2, c: c2, term: t2, vlog: l2 };
        if pre.net.contains(m1) && pre.net.contains(m2) {
        } else if !pre.net.contains(m1) {
            assert(m1 == mv);
            if pre.net.contains(m2) {
                assert(c2 == c);
            }
        } else {
            assert(m2 == mv);
            assert(c1 == c);
        }
    }
    assert forall|t2: nat, b: nat, bt: nat, entries: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }) implies append_msg_ok(post, t2, b, bt, entries) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }));
        assert(append_msg_ok(pre, t2, b, bt, entries));
    }
    assert forall|v2: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t2, mi }) implies ack_msg_ok(post, v2, t2, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t2, mi }));
        assert(ack_msg_ok(pre, v2, t2, mi));
    }

    assert forall|u: nat| #[trigger] post.leader_log.dom().contains(u) implies lterm_ok(post, u) by {
        assert(lterm_ok(pre, u));
    }

    // Persistence: v's term moved up to t (widening its ranges); its log is
    // unchanged. The new vote inherits persistence from v's acks.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_persist_ok(pre, v2, t0, mi));
        if v2 == v {
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (post.hosts[v2].term + 1) as nat, i2)
                implies prefix_eq(post.hosts[v2].log, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[v].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[v].log, pre.leader_log[t0], i2));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        if pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }) {
            assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
        } else {
            assert(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 } == mv);
            assert(ack_persist_ok(pre, v, t0, mi));
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (u2 + 1) as nat, i2)
                implies prefix_eq(vlog2, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[v].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[v].log, pre.leader_log[t0], i2));
            }
        }
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged; host terms only grow, so committing-leader claims persist).
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

proof fn collect_vote_preserves(pre: GState, post: GState, i: int, v: int, vlog: Seq<AEntry>)
    requires inv(pre), t_collect_vote(pre, post, i, v, vlog),
    ensures inv(post),
{
    let h = pre.hosts[i];
    assert(vote_msg_ok(pre, v, i, h.term, vlog));
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        if j == i {
            let hp = post.hosts[i];
            assert(hp.votes =~= h.votes.insert(v));
            assert(0 <= v < pre.n);
            assert(node_ids(pre.n).contains(v)) by {
                vstd::set_lib::lemma_int_range(0, pre.n as int);
            }
            assert forall|x: int| #[trigger] hp.votes.contains(x) implies {
                &&& hp.vote_logs.dom().contains(x)
                &&& post.net.contains(Msg::Vote { v: x, c: i, term: hp.term, vlog: hp.vote_logs[x] })
            } by {
                if x == v {
                    assert(hp.vote_logs[v] == vlog);
                } else {
                    assert(h.votes.contains(x));
                    assert(hp.vote_logs[x] == h.vote_logs[x]);
                }
            }
        }
    }
    assert forall|u: nat| #[trigger] post.leader_log.dom().contains(u) implies lterm_ok(post, u) by {
        assert(lterm_ok(pre, u));
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v2: int, c: int, t2: nat, vlog2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v: v2, c, term: t2, vlog: vlog2 }) implies vote_msg_ok(post, v2, c, t2, vlog2) by {
            assert(vote_msg_ok(pre, v2, c, t2, vlog2));
            // i's role/term/log unchanged; only votes/vote_logs changed.
        }
        assert forall|t2: nat, b: nat, bt: nat, entries: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }) implies append_msg_ok(post, t2, b, bt, entries) by {
            assert(append_msg_ok(pre, t2, b, bt, entries));
        }
        assert forall|v2: int, t2: nat, mi: nat|
            #[trigger] post.net.contains(Msg::Ack { v: v2, term: t2, mi }) implies ack_msg_ok(post, v2, t2, mi) by {
            assert(ack_msg_ok(pre, v2, t2, mi));
        }
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

/// The result of a base-matching splice from a leader's log window is
/// well-formed and bounded by the leader's term.
proof fn lemma_splice_wf(s: GState, log: Seq<AEntry>, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires
        inv(s),
        s.net.contains(Msg::Append { term: t, base: b, bterm: bt, entries }),
        log_wf(log),
        terms_le(log, t),
        b == 0 || (b <= log.len() && log[b - 1].term == bt),
    ensures
        log_wf(splice(log, b, entries)),
        terms_le(splice(log, b, entries), t),
{
    assert(append_msg_ok(s, t, b, bt, entries));
    assert(s.leader_log.dom().contains(t));
    assert(lterm_ok(s, t));
    let ll = s.leader_log[t];
    let r = splice(log, b, entries);
    if splice_is_noop(log, b, entries) {
    } else {
        assert(r == log.subrange(0, b as int) + entries);
        assert(r.len() == b + entries.len());
        // Pointwise: prefix from log, suffix from the leader log window.
        assert(forall|j: int| 0 <= j < b ==> r[j] == log[j]);
        assert forall|j: int| b <= j < r.len() implies r[j] == ll[j] by {
            assert(entries[j - b] == ll[b + (j - b)]);
        }
        assert forall|j: int| 0 <= j < r.len() implies (#[trigger] r[j]).term >= 1 && r[j].term <= t by {
            if j < b {
                assert(log[j].term >= 1 && log[j].term <= t);
            } else {
                assert(r[j] == ll[j]);
                assert(ll[j].term >= 1 && ll[j].term <= t);
            }
        }
        assert forall|j1: int, j2: int| 0 <= j1 <= j2 < r.len() implies
            (#[trigger] r[j1]).term <= (#[trigger] r[j2]).term by {
            if j2 < b {
                assert(log[j1].term <= log[j2].term);
            } else if j1 >= b {
                assert(r[j1] == ll[j1] && r[j2] == ll[j2]);
                assert(ll[j1].term <= ll[j2].term);
            } else {
                // j1 < b <= j2: chain through the base entry.
                assert(log[j1].term <= log[b - 1].term);
                assert(log[b - 1].term == bt == ll[b - 1].term);
                assert(ll[b - 1].term <= ll[j2].term);
                assert(r[j2] == ll[j2]);
            }
        }
    }
}

proof fn become_leader_preserves(pre: GState, post: GState, i: int)
    requires inv(pre), t_become_leader(pre, post, i),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let u = h.term;
    let newlog = h.log.push(AEntry { term: u, cmd: None });
    lemma_election_fresh(pre, i);
    assert(host_ok(pre, i));
    let m1 = pre.leader_log;
    let m2 = post.leader_log;
    assert(ll_extends(m1, m2)) by {
        assert forall|t2: nat| #[trigger] m1.dom().contains(t2)
            implies m2.dom().contains(t2) && prefix_eq(m2[t2], m1[t2], m1[t2].len()) by {
            assert(t2 != u);
        }
    }
    // The new leader log is pinned: old entries via the candidate's pinned
    // log, the noop via the new map entry itself.
    assert(log_pinned(m2, newlog)) by {
        lemma_pinned_extend(m1, m2, h.log);
        assert forall|j: int| 0 <= j < newlog.len() implies pinned_at(m2, newlog, j) by {
            if j < h.log.len() {
                assert(pinned_at(m2, h.log, j));
                let tau = h.log[j].term;
                assert(newlog[j].term == tau);
                assert forall|k: int| 0 <= k <= j implies newlog[k] == m2[tau][k] by {
                    assert(h.log[k] == m2[tau][k]);
                }
            } else {
                assert(newlog[j].term == u);
                assert(m2[u] == newlog);
            }
        }
    }

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        lemma_pinned_extend(m1, m2, pre.hosts[j].log);
        if j == i {
            // Leader facts.
            assert(post.leader_log.dom().contains(u));
            assert(post.leader_of[u] == i);
            assert(post.leader_log[u] == newlog);
            // No stale read high-water mark for a fresh term.
            assert(!pre.read_hwm.dom().contains(u));
            assert(terms_le(newlog, u));
            assert(log_wf(newlog)) by {
                assert(terms_lt(h.log, u));
            }
        } else {
            let hj = pre.hosts[j];
            if hj.role is Candidate {
                // C1: if j campaigns in term u, the new winner is i != j.
                if post.leader_of.dom().contains(hj.term) {
                    if hj.term == u {
                        assert(post.leader_of[u] == i);
                    } else {
                        assert(pre.leader_of.dom().contains(hj.term));
                    }
                }
            }
            if hj.role is Leader {
                // j leads a different term (u had no leader yet).
                assert(pre.leader_log.dom().contains(hj.term));
                assert(hj.term != u);
                assert(post.leader_of[hj.term] == pre.leader_of[hj.term]);
                assert(post.leader_log[hj.term] == pre.leader_log[hj.term]);
            }
        }
    }

    // Messages: net unchanged; only i's role and log changed.
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(campaign_msg_ok(pre, c, t2, clog));
        lemma_pinned_extend(m1, m2, clog);
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(vote_msg_ok(pre, v, c, t2, vlog));
        lemma_pinned_extend(m1, m2, vlog);
        // Candidate-condition for c == i: i is now a leader, vacuous.
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {}
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {}
    assert forall|t2: nat, b: nat, bt: nat, entries: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }) implies append_msg_ok(post, t2, b, bt, entries) by {
        assert(append_msg_ok(pre, t2, b, bt, entries));
        // Appends reference elected terms; u was fresh, so t2 != u and the
        // leader log at t2 is unchanged.
        assert(t2 != u);
        assert(post.leader_log[t2] == pre.leader_log[t2]);
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(ack_msg_ok(pre, v, t2, mi));
        // Acked terms were already elected, so t2 != u and its leader log is
        // unchanged.
        assert(t2 != u);
        assert(m2[t2] == m1[t2]);
    }

    // Leader-log terms.
    assert(post.leader_of.dom() =~= post.leader_log.dom());
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        if u2 == u {
            // The new term's election evidence.
            assert(post.leader_log[u] == newlog);
            assert(post.elect_log[u] == h.log);
            assert(post.voters[u] == h.votes);
            assert(post.elect_votes[u] == h.vote_logs);
            assert(log_pinned(m2, newlog));
            assert(log_wf(newlog)) by {
                assert(terms_lt(h.log, u));
            }
            assert(last_term(newlog) == u);
            assert(newlog[h.log.len() as int].term == u);
            assert(prefix_eq(newlog, h.log, h.log.len()));
            assert forall|x: int| #[trigger] post.voters[u].contains(x) implies voter_ok(post, u, x) by {
                assert(h.votes.contains(x));
                let vlog = h.vote_logs[x];
                assert(pre.net.contains(Msg::Vote { v: x, c: i, term: u, vlog }));
                assert(vote_msg_ok(pre, x, i, u, vlog));
                // i was a candidate in term u with log h.log.
                assert(up_to_date(h.log, vlog));
                // Freeze the persistence evidence: u was fresh, so the
                // exclusive range (t0, u) matches K3''-range (t0, u] on the
                // pre-state map.
                assert forall|t0: nat, mi: nat| t0 < u
                    && #[trigger] post.net.contains(Msg::Ack { v: x, term: t0, mi })
                    implies frozen_persist_at(post, u, vlog, t0, mi) by {
                    assert(pre.net.contains(Msg::Ack { v: x, term: t0, mi }));
                    assert(ack_msg_ok(pre, x, t0, mi));
                    assert(vote_persist_ok(pre, u, vlog, t0, mi));
                    assert(t0 != u);
                    assert forall|i2: nat| i2 <= mi && #[trigger] mid_compliant(m2, t0, u, i2)
                        implies prefix_eq(vlog, m2[t0], i2) by {
                        lemma_mid_unfresh(m1, u, newlog, t0, u, i2);
                        // Widen (t0, u) to (t0, u]: u was not elected pre-state.
                        assert(mid_compliant(m1, t0, (u + 1) as nat, i2)) by {
                            assert forall|x2: nat| t0 < x2 < u + 1 && #[trigger] m1.dom().contains(x2)
                                implies prefix_eq(m1[x2], m1[t0], i2) by {
                                assert(x2 != u);
                                assert(t0 < x2 < u);
                            }
                        }
                        assert(prefix_eq(vlog, m1[t0], i2));
                    }
                }
            }
        } else {
            assert(pre.leader_log.dom().contains(u2));
            assert(lterm_ok(pre, u2));
            assert(post.leader_log[u2] == pre.leader_log[u2]);
            assert(post.leader_of[u2] == pre.leader_of[u2]);
            assert(post.voters[u2] == pre.voters[u2]);
            assert(post.elect_log[u2] == pre.elect_log[u2]);
            assert(post.elect_votes[u2] == pre.elect_votes[u2]);
            lemma_pinned_extend(m1, m2, pre.leader_log[u2]);
            assert forall|x: int| #[trigger] post.voters[u2].contains(x) implies voter_ok(post, u2, x) by {
                assert(voter_ok(pre, u2, x));
                let vlog = pre.elect_votes[u2][x];
                assert forall|t0: nat, mi: nat| t0 < u2
                    && #[trigger] post.net.contains(Msg::Ack { v: x, term: t0, mi })
                    implies frozen_persist_at(post, u2, vlog, t0, mi) by {
                    assert(pre.net.contains(Msg::Ack { v: x, term: t0, mi }));
                    assert(ack_msg_ok(pre, x, t0, mi));
                    assert(frozen_persist_at(pre, u2, vlog, t0, mi));
                    assert(t0 != u);
                    assert forall|i2: nat| i2 <= mi && #[trigger] mid_compliant(m2, t0, u2, i2)
                        implies prefix_eq(vlog, m2[t0], i2) by {
                        lemma_mid_unfresh(m1, u, newlog, t0, u2, i2);
                        assert(prefix_eq(vlog, m1[t0], i2));
                    }
                }
            }
        }
    }

    // Persistence: the leader-log map gained the fresh term u. For the new
    // leader's own acks the compliance hypothesis now covers u itself, whose
    // leader log IS the new log — the conclusion is direct. Everyone else
    // strips the fresh term and falls back to the pre-state invariant.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_msg_ok(pre, v2, t0, mi));
        assert(ack_persist_ok(pre, v2, t0, mi));
        assert(t0 != u);
        assert forall|i2: nat| i2 <= mi
            && #[trigger] mid_compliant(m2, t0, (post.hosts[v2].term + 1) as nat, i2)
            implies prefix_eq(post.hosts[v2].log, m2[t0], i2) by {
            if v2 == i {
                // t0 <= pre term == u and t0 != u, so t0 < u < u + 1: the
                // hypothesis at x == u gives the conclusion directly.
                assert(t0 < u);
                assert(m2.dom().contains(u));
                assert(prefix_eq(m2[u], m2[t0], i2));
                assert(m2[u] == newlog && m2[t0] == m1[t0]);
            } else {
                lemma_mid_unfresh(m1, u, newlog, t0, (post.hosts[v2].term + 1) as nat, i2);
                assert(mid_compliant(m1, t0, (pre.hosts[v2].term + 1) as nat, i2));
                assert(prefix_eq(pre.hosts[v2].log, m1[t0], i2));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }));
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_msg_ok(pre, v2, t0, mi));
        assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
        assert(t0 != u);
        assert forall|i2: nat| i2 <= mi
            && #[trigger] mid_compliant(m2, t0, (u2 + 1) as nat, i2)
            implies prefix_eq(vlog2, m2[t0], i2) by {
            lemma_mid_unfresh(m1, u, newlog, t0, (u2 + 1) as nat, i2);
            assert(prefix_eq(vlog2, m1[t0], i2));
        }
    }

    // Commit families: all commit data references previously elected terms,
    // whose leader logs are unchanged. The new term's leader log holds every
    // committed prefix (H1): its vote quorum overlaps each commit's ack
    // quorum in a voter whose grant-time log kept the prefix (K3''), and the
    // up-to-date check transfers it into the winner's log.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
            assert(pre.hosts[j2].crec.term != u);
            assert(m2[pre.hosts[j2].crec.term] == m1[pre.hosts[j2].crec.term]);
            if j2 == i {
                assert(forall|k: int| 0 <= k < pre.hosts[i].commit ==> newlog[k] == h.log[k]);
            }
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(rec.term != u);
        assert(m2[rec.term] == m1[rec.term]);
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }));
        assert(commit_msg_ok(pre, t9, ci9, rec9));
        assert(commit_rec_ok(pre, rec9));
        assert(t9 != u && rec9.term != u);
        assert(m2[t9] == m1[t9] && m2[rec9.term] == m1[rec9.term]);
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(commit_rec_ok(pre, rec));
        assert(rec.term != u);
        assert(m2[rec.term] == m1[rec.term]);
        if u9 == u {
            // H1. Overlap the commit's ack quorum with the election's votes.
            lemma_quorum_overlap(pre.n, h.votes, rec.q.dom());
            let x = choose|x: int| h.votes.contains(x) && rec.q.dom().contains(x);
            let vlog = h.vote_logs[x];
            assert(pre.net.contains(Msg::Vote { v: x, c: i, term: u, vlog }));
            assert(vote_msg_ok(pre, x, i, u, vlog));
            let mi = rec.q[x];
            assert(mi >= rec.ci && pre.net.contains(Msg::Ack { v: x, term: rec.term, mi }));
            assert(lterm_ok(pre, rec.term));
            // K3'': the voter's grant-time log kept the committed prefix,
            // since every leader elected after rec.term complies (D; u was
            // not elected yet).
            assert(vote_persist_ok(pre, u, vlog, rec.term, mi));
            assert(mid_compliant(m1, rec.term, (u + 1) as nat, rec.ci)) by {
                assert forall|x2: nat| rec.term < x2 < u + 1 && #[trigger] m1.dom().contains(x2)
                    implies prefix_eq(m1[x2], m1[rec.term], rec.ci) by {
                    assert(x2 != u);
                    assert(prefix_eq(m1[x2], m1[rec.term], rec.ci));
                }
            }
            assert(prefix_eq(vlog, m1[rec.term], rec.ci));
            // The candidate passed the up-to-date check against the voter.
            assert(up_to_date(h.log, vlog));
            lemma_mid_narrow(m1, rec.term, u, (u + 1) as nat, rec.ci);
            lemma_uptodate_prefix(m1, rec.term, rec.ci, vlog, h.log, u);
            assert(prefix_eq(h.log, m1[rec.term], rec.ci));
            assert(m2[u] == newlog);
            assert(forall|k: int| 0 <= k < rec.ci ==> newlog[k] == h.log[k]);
        } else {
            assert(pre.leader_log.dom().contains(u9));
            assert(prefix_eq(m1[u9], m1[rec.term], rec.ci));
            assert(m2[u9] == m1[u9]);
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
        assert(rec.term != u);
        assert(post.leader_of[rec.term] == pre.leader_of[rec.term]);
        // Host i's term and commit index are unchanged.
    }
}

proof fn propose_preserves(pre: GState, post: GState, i: int, cmd: Option<Seq<u8>>)
    requires inv(pre), t_propose(pre, post, i, cmd),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let u = h.term;
    let newlog = h.log.push(AEntry { term: u, cmd });
    assert(host_ok(pre, i));
    assert(pre.leader_log.dom().contains(u));
    assert(lterm_ok(pre, u));
    assert(pre.leader_log[u] == h.log);
    let m1 = pre.leader_log;
    let m2 = post.leader_log;
    assert(ll_extends(m1, m2)) by {
        assert forall|t2: nat| #[trigger] m1.dom().contains(t2)
            implies m2.dom().contains(t2) && prefix_eq(m2[t2], m1[t2], m1[t2].len()) by {
            if t2 == u {
                assert(prefix_eq(newlog, h.log, h.log.len()));
            }
        }
    }
    assert(log_pinned(m2, newlog)) by {
        lemma_pinned_extend(m1, m2, h.log);
        assert forall|j: int| 0 <= j < newlog.len() implies pinned_at(m2, newlog, j) by {
            if j < h.log.len() {
                assert(pinned_at(m2, h.log, j));
                let tau = h.log[j].term;
                assert(newlog[j].term == tau);
                assert forall|k: int| 0 <= k <= j implies newlog[k] == m2[tau][k] by {
                    assert(h.log[k] == m2[tau][k]);
                }
            } else {
                assert(newlog[j].term == u);
                assert(m2[u] == newlog);
            }
        }
    }

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        lemma_pinned_extend(m1, m2, pre.hosts[j].log);
        if j == i {
            assert(log_wf(newlog)) by {
                assert(terms_le(h.log, u));
            }
            assert(terms_le(newlog, u));
            assert(post.leader_log[u] == newlog);
        } else {
            let hj = pre.hosts[j];
            if hj.role is Leader {
                // Only one leader per term: j leads a different term.
                assert(pre.leader_of[hj.term] == j);
                assert(hj.term != u);
                assert(post.leader_log[hj.term] == pre.leader_log[hj.term]);
            }
        }
    }

    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(campaign_msg_ok(pre, c, t2, clog));
        lemma_pinned_extend(m1, m2, clog);
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(vote_msg_ok(pre, v, c, t2, vlog));
        lemma_pinned_extend(m1, m2, vlog);
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {}
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {}
    assert forall|t2: nat, b: nat, bt: nat, entries: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b, bterm: bt, entries }) implies append_msg_ok(post, t2, b, bt, entries) by {
        assert(append_msg_ok(pre, t2, b, bt, entries));
        if t2 == u {
            // The leader log grew; existing windows are unchanged prefixes.
            assert(post.leader_log[u] == newlog);
            assert(forall|j: int| 0 <= j < h.log.len() ==> newlog[j] == h.log[j]);
        } else {
            assert(post.leader_log[t2] == pre.leader_log[t2]);
        }
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(ack_msg_ok(pre, v, t2, mi));
        if t2 == u {
            // The acked prefix sits below the old length; the extension keeps it.
            assert(post.leader_log[u] == newlog);
            assert(mi <= h.log.len());
            if post.hosts[v].term == t2 {
                assert(prefix_eq(post.hosts[v].log, newlog, mi)) by {
                    assert(prefix_eq(pre.hosts[v].log, h.log, mi));
                    assert(forall|j: int| 0 <= j < mi ==> newlog[j] == h.log[j]);
                }
            }
        } else {
            assert(post.leader_log[t2] == pre.leader_log[t2]);
        }
    }

    assert(post.leader_of.dom() =~= post.leader_log.dom()) by {
        assert(pre.leader_of.dom().contains(u));
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(pre.leader_log.dom().contains(u2));
        assert(lterm_ok(pre, u2));
        if u2 == u {
            assert(post.leader_log[u] == newlog);
            assert(log_pinned(m2, newlog));
            assert(log_wf(newlog)) by {
                assert(terms_le(h.log, u));
            }
            assert(last_term(newlog) == u);
            assert(prefix_eq(newlog, pre.elect_log[u], pre.elect_log[u].len())) by {
                assert(prefix_eq(h.log, pre.elect_log[u], pre.elect_log[u].len()));
            }
            assert(newlog[pre.elect_log[u].len() as int].term == u) by {
                assert(h.log[pre.elect_log[u].len() as int].term == u);
            }
        } else {
            assert(post.leader_log[u2] == pre.leader_log[u2]);
            lemma_pinned_extend(m1, m2, pre.leader_log[u2]);
        }
        // Frozen voter evidence survives the own-term extension.
        assert forall|x: int| #[trigger] post.voters[u2].contains(x) implies voter_ok(post, u2, x) by {
            assert(voter_ok(pre, u2, x));
            let vlog = pre.elect_votes[u2][x];
            assert forall|t0: nat, mi: nat| t0 < u2
                && #[trigger] post.net.contains(Msg::Ack { v: x, term: t0, mi })
                implies frozen_persist_at(post, u2, vlog, t0, mi) by {
                assert(pre.net.contains(Msg::Ack { v: x, term: t0, mi }));
                assert(ack_msg_ok(pre, x, t0, mi));
                assert(frozen_persist_at(pre, u2, vlog, t0, mi));
                assert(lterm_ok(pre, t0));
                assert forall|i2: nat| i2 <= mi && #[trigger] mid_compliant(m2, t0, u2, i2)
                    implies prefix_eq(vlog, m2[t0], i2) by {
                    assert(terms_le(m1[t0], t0));
                    assert(i2 <= m1[t0].len());
                    lemma_mid_unext(m1, u, AEntry { term: u, cmd }, t0, u2, i2);
                    assert(prefix_eq(vlog, m1[t0], i2));
                    if t0 == u {
                        assert(m2[u] == newlog);
                        assert(forall|k: int| 0 <= k < i2 ==> newlog[k] == h.log[k]);
                    } else {
                        assert(m2[t0] == m1[t0]);
                    }
                }
            }
        }
    }

    // Persistence: the leader log at u grew by an own-term entry. Compliance
    // over the extended map implies compliance over the original (agreement
    // cannot reach the new entry), and all prefixes below acked indexes are
    // frozen by the extension.
    let e = AEntry { term: u, cmd };
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_msg_ok(pre, v2, t0, mi));
        assert(ack_persist_ok(pre, v2, t0, mi));
        assert(lterm_ok(pre, t0));
        assert forall|i2: nat| i2 <= mi
            && #[trigger] mid_compliant(m2, t0, (post.hosts[v2].term + 1) as nat, i2)
            implies prefix_eq(post.hosts[v2].log, m2[t0], i2) by {
            assert(terms_le(m1[t0], t0));
            assert(i2 <= m1[t0].len());
            lemma_mid_unext(m1, u, e, t0, (post.hosts[v2].term + 1) as nat, i2);
            assert(mid_compliant(m1, t0, (pre.hosts[v2].term + 1) as nat, i2));
            assert(prefix_eq(pre.hosts[v2].log, m1[t0], i2));
            // Map the conclusion across the extension: positions below i2 are
            // frozen in both the leader log at t0 and (for the leader itself)
            // its own log.
            if t0 == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < i2 ==> newlog[k] == h.log[k]);
            } else {
                assert(m2[t0] == m1[t0]);
            }
            if v2 == i {
                assert(post.hosts[i].log == newlog);
                assert(forall|k: int| 0 <= k < i2 ==> newlog[k] == h.log[k]);
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }));
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_msg_ok(pre, v2, t0, mi));
        assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
        assert(lterm_ok(pre, t0));
        assert forall|i2: nat| i2 <= mi
            && #[trigger] mid_compliant(m2, t0, (u2 + 1) as nat, i2)
            implies prefix_eq(vlog2, m2[t0], i2) by {
            assert(terms_le(m1[t0], t0));
            assert(i2 <= m1[t0].len());
            lemma_mid_unext(m1, u, e, t0, (u2 + 1) as nat, i2);
            assert(prefix_eq(vlog2, m1[t0], i2));
            if t0 == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < i2 ==> newlog[k] == h.log[k]);
            } else {
                assert(m2[t0] == m1[t0]);
            }
        }
    }

    // Commit families: the extension freezes all positions below the old
    // length, which every commit-related prefix sits under.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
            let ct = pre.hosts[j2].crec.term;
            if ct == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < pre.hosts[j2].commit ==> newlog[k] == h.log[k]);
            } else {
                assert(m2[ct] == m1[ct]);
            }
            if j2 == i {
                assert(forall|k: int| 0 <= k < pre.hosts[i].commit ==> newlog[k] == h.log[k]);
            }
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        if rec.term == u {
            assert(m2[u] == newlog);
            assert(newlog[rec.ci - 1] == h.log[rec.ci - 1]);
        } else {
            assert(m2[rec.term] == m1[rec.term]);
        }
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }));
        assert(commit_msg_ok(pre, t9, ci9, rec9));
        assert(commit_rec_ok(pre, rec9));
        assert(forall|k: int| 0 <= k < ci9 ==> m2[t9][k] == m1[t9][k]) by {
            if t9 == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < ci9 ==> newlog[k] == h.log[k]);
            }
        }
        assert(forall|k: int| 0 <= k < ci9 ==> m2[rec9.term][k] == m1[rec9.term][k]) by {
            if rec9.term == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < ci9 ==> newlog[k] == h.log[k]);
            }
        }
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(commit_rec_ok(pre, rec));
        assert(prefix_eq(m1[u9], m1[rec.term], rec.ci));
        assert(forall|k: int| 0 <= k < rec.ci ==> m2[u9][k] == m1[u9][k]) by {
            if u9 == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < rec.ci ==> newlog[k] == h.log[k]);
            }
        }
        assert(forall|k: int| 0 <= k < rec.ci ==> m2[rec.term][k] == m1[rec.term][k]) by {
            if rec.term == u {
                assert(m2[u] == newlog);
                assert(forall|k: int| 0 <= k < rec.ci ==> newlog[k] == h.log[k]);
            }
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
        // Host i's term and commit index are unchanged.
    }
}

proof fn send_append_preserves(pre: GState, post: GState, i: int, b: nat, e: nat)
    requires inv(pre), t_send_append(pre, post, i, b, e),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let u = h.term;
    let bt: nat = if b == 0 { 0 } else { h.log[b - 1].term };
    let entries = h.log.subrange(b as int, e as int);
    let m = Msg::Append { term: u, base: b, bterm: bt, entries };
    assert(host_ok(pre, i));
    assert(pre.leader_log.dom().contains(u));
    assert(pre.leader_log[u] == h.log);
    assert(lterm_ok(pre, u));

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
        assert(campaign_msg_ok(pre, c, t2, clog));
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
        assert(vote_msg_ok(pre, v, c, t2, vlog));
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
        assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
    }
    assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
        if pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) {
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        } else {
            assert(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 } == m);
            assert(b + entries.len() <= h.log.len());
            assert(forall|j: int| 0 <= j < entries.len() ==> #[trigger] entries[j] == h.log[b + j]);
        }
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(pre.net.contains(Msg::Ack { v, term: t2, mi }));
        assert(ack_msg_ok(pre, v, t2, mi));
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

/// Shape facts for a base-matching append: the receiver's log matches the
/// leader's up to the base (Log Matching on the base entry), hence up to the
/// end of the spliced entries; the spliced log is pinned and well-formed.
proof fn recv_append_shape(pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires inv(pre), t_recv_append(pre, post, i, t, b, bt, entries),
    ensures
        pre.leader_log.dom().contains(t),
        prefix_eq(pre.hosts[i].log, pre.leader_log[t], b),
        prefix_eq(splice(pre.hosts[i].log, b, entries), pre.leader_log[t], (b + entries.len()) as nat),
        log_pinned(pre.leader_log, splice(pre.hosts[i].log, b, entries)),
        log_wf(splice(pre.hosts[i].log, b, entries)),
        terms_le(splice(pre.hosts[i].log, b, entries), t),
{
    let h = pre.hosts[i];
    let newlog = splice(h.log, b, entries);
    assert(host_ok(pre, i));
    assert(append_msg_ok(pre, t, b, bt, entries));
    assert(terms_le(h.log, t)) by {
        assert(terms_le(h.log, h.term));
    }
    lemma_splice_wf(pre, h.log, t, b, bt, entries);

    let m = pre.leader_log;
    assert(lterm_ok(pre, t));
    let ll_t = m[t];
    let mi_new = (b + entries.len()) as nat;
    assert(prefix_eq(h.log, ll_t, b)) by {
        if b >= 1 {
            assert(h.log[b - 1].term == bt == ll_t[b - 1].term);
            lemma_log_matching(m, h.log, ll_t, b - 1);
        }
    }
    assert(prefix_eq(newlog, ll_t, mi_new)) by {
        if splice_is_noop(h.log, b, entries) {
            assert forall|j: int| 0 <= j < mi_new implies h.log[j] == ll_t[j] by {
                if j >= b {
                    assert(h.log[j] == entries[j - b]);
                    assert(entries[j - b] == ll_t[b + (j - b)]);
                }
            }
        } else {
            assert(newlog == h.log.subrange(0, b as int) + entries);
            assert forall|j: int| 0 <= j < mi_new implies newlog[j] == ll_t[j] by {
                if j < b {
                    assert(newlog[j] == h.log[j]);
                } else {
                    assert(newlog[j] == entries[j - b]);
                    assert(entries[j - b] == ll_t[b + (j - b)]);
                }
            }
        }
    }
    assert(log_pinned(m, newlog)) by {
        assert forall|j: int| 0 <= j < newlog.len() implies pinned_at(m, newlog, j) by {
            if splice_is_noop(h.log, b, entries) {
                assert(pinned_at(m, h.log, j));
            } else {
                assert(newlog.len() == mi_new);
                assert(pinned_at(m, ll_t, j));
                let tau = ll_t[j].term;
                assert(newlog[j].term == tau);
                assert forall|k: int| 0 <= k <= j implies newlog[k] == m[tau][k] by {
                    assert(newlog[k] == ll_t[k]);
                    assert(ll_t[k] == m[tau][k]);
                }
            }
        }
    }
}

proof fn recv_append_hosts_msgs(pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires inv(pre), t_recv_append(pre, post, i, t, b, bt, entries),
    ensures inv_wf(post), inv_hosts(post), inv_msgs(post), inv_lterms(post),
{
    let h = pre.hosts[i];
    let newlog = splice(h.log, b, entries);
    let ma = Msg::Ack { v: i, term: t, mi: (b + entries.len()) as nat };
    let m = pre.leader_log;
    let mi_new = (b + entries.len()) as nat;
    assert(host_ok(pre, i));
    assert(append_msg_ok(pre, t, b, bt, entries));
    recv_append_shape(pre, post, i, t, b, bt, entries);
    let ll_t = m[t];

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
        assert(campaign_msg_ok(pre, c, t2, clog));
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
        assert(vote_msg_ok(pre, v, c, t2, vlog));
        if v == i && post.hosts[i].term == t2 {
            // Same-term step: the vote is kept.
            assert(pre.hosts[i].term >= t2);
            assert(t == t2);
            assert(pre.hosts[i].term == t2);
        }
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
        assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
    }
    assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
        assert(append_msg_ok(pre, t2, b2, bt2, entries2));
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        if pre.net.contains(Msg::Ack { v, term: t2, mi }) {
            assert(ack_msg_ok(pre, v, t2, mi));
            if v == i && post.hosts[i].term == t2 {
                // t2 == t == pre term: a same-term append never conflicts
                // below an acked index.
                assert(t2 == t && h.term == t);
                lemma_splice_prefix(h.log, b, entries, ll_t, ll_t, mi);
            }
        } else {
            assert(Msg::Ack { v, term: t2, mi } == ma);
            assert(prefix_eq(newlog, ll_t, mi_new));
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
        // Frozen voter evidence: the new ack is in term t, at or above the
        // receiver's term, so it cannot be a below-u2 ack by a u2-voter.
        assert forall|x: int| #[trigger] post.voters[u2].contains(x) implies voter_ok(post, u2, x) by {
            assert(voter_ok(pre, u2, x));
            let vlog = pre.elect_votes[u2][x];
            assert forall|t0: nat, mi: nat| t0 < u2
                && #[trigger] post.net.contains(Msg::Ack { v: x, term: t0, mi })
                implies frozen_persist_at(post, u2, vlog, t0, mi) by {
                if pre.net.contains(Msg::Ack { v: x, term: t0, mi }) {
                    assert(frozen_persist_at(pre, u2, vlog, t0, mi));
                } else {
                    assert(Msg::Ack { v: x, term: t0, mi } == ma);
                    assert(x == i && t0 == t);
                    assert(vote_msg_ok(pre, x, pre.leader_of[u2], u2, vlog));
                    assert(pre.hosts[i].term >= u2);
                    assert(false);
                }
            }
        }
    }
}

proof fn recv_append_persist(pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires inv(pre), t_recv_append(pre, post, i, t, b, bt, entries),
    ensures inv_ack_persist(post), inv_vote_persist(post),
{
    let h = pre.hosts[i];
    let newlog = splice(h.log, b, entries);
    let ma = Msg::Ack { v: i, term: t, mi: (b + entries.len()) as nat };
    let m = pre.leader_log;
    let mi_new = (b + entries.len()) as nat;
    assert(host_ok(pre, i));
    assert(append_msg_ok(pre, t, b, bt, entries));
    recv_append_shape(pre, post, i, t, b, bt, entries);
    let ll_t = m[t];

    // For i's earlier acks: the compliance hypothesis covers the appending
    // leader's term t, whose log window the splice writes — so the splice
    // never conflicts below a compliant prefix. The new ack is an
    // unconditional match with the leader log of t.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        if pre.net.contains(Msg::Ack { v: v2, term: t0, mi }) {
            assert(ack_msg_ok(pre, v2, t0, mi));
            assert(ack_persist_ok(pre, v2, t0, mi));
            if v2 == i {
                assert forall|i2: nat| i2 <= mi
                    && #[trigger] mid_compliant(m, t0, (post.hosts[v2].term + 1) as nat, i2)
                    implies prefix_eq(post.hosts[v2].log, m[t0], i2) by {
                    lemma_mid_narrow(m, t0, (pre.hosts[i].term + 1) as nat, (t + 1) as nat, i2);
                    assert(prefix_eq(h.log, m[t0], i2));
                    assert(prefix_eq(ll_t, m[t0], i2)) by {
                        if t0 < t {
                            assert(m.dom().contains(t));
                            assert(prefix_eq(m[t], m[t0], i2));
                        } else {
                            assert(t0 == t);
                        }
                    }
                    lemma_splice_prefix(h.log, b, entries, ll_t, m[t0], i2);
                }
            }
        } else {
            assert(Msg::Ack { v: v2, term: t0, mi } == ma);
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(m, t0, (post.hosts[v2].term + 1) as nat, i2)
                implies prefix_eq(post.hosts[v2].log, m[t0], i2) by {
                assert(prefix_eq(newlog, ll_t, mi_new));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }));
        assert(vote_msg_ok(pre, v2, c2, u2, vlog2));
        if pre.net.contains(Msg::Ack { v: v2, term: t0, mi }) {
            assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
        } else {
            // The new ack is by i in term t == post term >= any vote term by
            // i, contradicting t0 < u2: the pair cannot exist.
            assert(Msg::Ack { v: v2, term: t0, mi } == ma);
            assert(v2 == i && t0 == t);
            assert(pre.hosts[i].term >= u2);
            assert(t >= pre.hosts[i].term);
            assert(false);
        }
    }
}

proof fn recv_append_commits(pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires inv(pre), t_recv_append(pre, post, i, t, b, bt, entries),
    ensures
        inv_commits(post),
        inv_leader_completeness(post),
        inv_commit_msgs(post),
        inv_host_commits(post),
        inv_commit_leaders(post),
{
    let h = pre.hosts[i];
    let m = pre.leader_log;
    assert(host_ok(pre, i));
    assert(append_msg_ok(pre, t, b, bt, entries));
    recv_append_shape(pre, post, i, t, b, bt, entries);
    let ll_t = m[t];

    // The receiver's committed prefix survives the splice — the appending
    // leader's log agrees with it (same term, or by Leader Completeness), so
    // no conflict can arise below the commit index.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && h.commit > 0 {
            let crec = h.crec;
            let ct = crec.term;
            assert(prefix_eq(h.log, m[ct], h.commit));
            assert(prefix_eq(ll_t, m[ct], h.commit)) by {
                if ct == t {
                } else {
                    assert(ct <= h.term <= t);
                    assert(prefix_eq(m[t], m[ct], crec.ci));
                }
            }
            lemma_splice_prefix(h.log, b, entries, ll_t, m[ct], h.commit);
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }));
        assert(commit_msg_ok(pre, t9, ci9, rec9));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
        // Host i's commit index is unchanged and its term only grows.
    }
}

proof fn recv_append_preserves(pre: GState, post: GState, i: int, t: nat, b: nat, bt: nat, entries: Seq<AEntry>)
    requires inv(pre), t_recv_append(pre, post, i, t, b, bt, entries),
    ensures inv(post),
{
    recv_append_hosts_msgs(pre, post, i, t, b, bt, entries);
    recv_append_persist(pre, post, i, t, b, bt, entries);
    recv_append_commits(pre, post, i, t, b, bt, entries);
}


proof fn send_ack_preserves(pre: GState, post: GState, i: int, mi: nat)
    requires inv(pre), t_send_ack(pre, post, i, mi),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let ma = Msg::Ack { v: i, term: h.term, mi };
    assert(host_ok(pre, i));

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
        assert(campaign_msg_ok(pre, c, t2, clog));
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
        assert(vote_msg_ok(pre, v, c, t2, vlog));
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
        assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
    }
    assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
        assert(append_msg_ok(pre, t2, b2, bt2, entries2));
    }
    assert forall|v: int, t2: nat, mi2: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
        if pre.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) {
            assert(ack_msg_ok(pre, v, t2, mi2));
        } else {
            assert(Msg::Ack { v, term: t2, mi: mi2 } == ma);
            // h.term >= 1 since the log entry at mi has h.term and terms >= 1.
            assert(h.log[mi - 1].term >= 1);
            // The entry at mi has the host's own term, so its pinning pins
            // the whole prefix to the current term's leader log.
            assert(pinned_at(pre.leader_log, h.log, mi - 1));
            assert(prefix_eq(h.log, pre.leader_log[h.term], mi)) by {
                assert(forall|k: int| 0 <= k <= mi - 1 ==>
                    h.log[k] == #[trigger] pre.leader_log[h.term][k]);
            }
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
        // Frozen voter evidence: the new ack is in the sender's current term,
        // so it cannot be a below-u2 ack by a u2-voter.
        assert forall|x: int| #[trigger] post.voters[u2].contains(x) implies voter_ok(post, u2, x) by {
            assert(voter_ok(pre, u2, x));
            let vlog = pre.elect_votes[u2][x];
            assert forall|t0: nat, mi2: nat| t0 < u2
                && #[trigger] post.net.contains(Msg::Ack { v: x, term: t0, mi: mi2 })
                implies frozen_persist_at(post, u2, vlog, t0, mi2) by {
                if pre.net.contains(Msg::Ack { v: x, term: t0, mi: mi2 }) {
                    assert(frozen_persist_at(pre, u2, vlog, t0, mi2));
                } else {
                    assert(Msg::Ack { v: x, term: t0, mi: mi2 } == ma);
                    assert(x == i && t0 == h.term);
                    assert(vote_msg_ok(pre, x, pre.leader_of[u2], u2, vlog));
                    assert(pre.hosts[i].term >= u2);
                    assert(false);
                }
            }
        }
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

proof fn leader_commit_preserves(pre: GState, post: GState, i: int, ci: nat, q: Map<int, nat>)
    requires inv(pre), t_leader_commit(pre, post, i, ci, q),
    ensures inv(post),
{
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
        assert(campaign_msg_ok(pre, c, t2, clog));
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
        assert(vote_msg_ok(pre, v, c, t2, vlog));
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
        assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
    }
    assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
        assert(append_msg_ok(pre, t2, b2, bt2, entries2));
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(pre.net.contains(Msg::Ack { v, term: t2, mi }));
        assert(ack_msg_ok(pre, v, t2, mi));
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families: the new record and message are justified by the guard;
    // leader completeness for the new record is the H2 induction.
    let h = pre.hosts[i];
    let t = h.term;
    let rec = CommitRec { term: t, ci, q };
    assert(host_ok(pre, i));
    assert(pre.leader_log.dom().contains(t));
    assert(pre.leader_log[t] == h.log);
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && ci > h.commit {
            assert(post.hosts[i].crec == rec);
            assert(post.hosts[i].commit == ci);
            assert(post.commits.contains(rec));
            assert(prefix_eq(h.log, post.leader_log[t], ci));
        }
    }
    assert forall|rec2: CommitRec| #[trigger] post.commits.contains(rec2) implies commit_rec_ok(post, rec2) by {
        if pre.commits.contains(rec2) {
            assert(commit_rec_ok(pre, rec2));
        } else {
            assert(rec2 == rec);
        }
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        if pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) {
            assert(commit_msg_ok(pre, t9, ci9, rec9));
        } else {
            assert(Msg::Commit { term: t9, ci: ci9, rec: rec9 } == Msg::Commit { term: t, ci, rec });
            assert(post.commits.contains(rec));
            assert(prefix_eq(post.leader_log[t], post.leader_log[t], ci));
        }
    }
    assert forall|rec2: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec2) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec2.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec2.term], rec2.ci) by {
        if pre.commits.contains(rec2) {
            assert(pre.leader_log.dom().contains(u9));
            assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec2.term], rec2.ci));
        } else {
            assert(rec2 == rec);
            lemma_h2(pre, t, ci, q, u9);
        }
    }
    assert forall|rec2: CommitRec| #[trigger] post.commits.contains(rec2) implies commit_leader_ok(post, rec2) by {
        if pre.commits.contains(rec2) {
            assert(commit_rec_ok(pre, rec2));
            assert(lterm_ok(pre, rec2.term));
            assert(commit_leader_ok(pre, rec2));
            // Only host i changed, and its commit index only grew.
        } else {
            assert(rec2 == rec);
            assert(pre.leader_of[t] == i);
            assert(post.hosts[i].commit >= ci);
        }
    }
}

proof fn send_commit_preserves(pre: GState, post: GState, i: int, ci: nat)
    requires inv(pre), t_send_commit(pre, post, i, ci),
    ensures inv(post),
{
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert forall|c: int, t2: nat, clog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
        assert(campaign_msg_ok(pre, c, t2, clog));
    }
    assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
        assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
        assert(vote_msg_ok(pre, v, c, t2, vlog));
    }
    assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
        && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
        assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
    }
    assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
        && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
        assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
        assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
    }
    assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
        #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
        assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
        assert(append_msg_ok(pre, t2, b2, bt2, entries2));
    }
    assert forall|v: int, t2: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi }) implies ack_msg_ok(post, v, t2, mi) by {
        assert(pre.net.contains(Msg::Ack { v, term: t2, mi }));
        assert(ack_msg_ok(pre, v, t2, mi));
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families: the new commit message re-announces a committed index
    // covered by the leader's own commit witness.
    let h = pre.hosts[i];
    assert(host_ok(pre, i));
    assert(host_commit_ok(pre, i));
    assert(pre.leader_log[h.term] == h.log);
    assert(pre.commits.contains(h.crec));
    assert(commit_rec_ok(pre, h.crec));
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        if pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) {
            assert(commit_msg_ok(pre, t9, ci9, rec9));
        } else {
            assert(Msg::Commit { term: t9, ci: ci9, rec: rec9 }
                == Msg::Commit { term: h.term, ci, rec: h.crec });
            // The leader's log is its term's leader log, and its committed
            // prefix (>= ci) agrees with the witness record's leader log.
            assert(prefix_eq(h.log, pre.leader_log[h.crec.term], h.commit));
            assert(prefix_eq(pre.leader_log[h.term], pre.leader_log[h.crec.term], ci)) by {
                assert(forall|k: int| 0 <= k < ci ==> h.log[k] == pre.leader_log[h.crec.term][k]);
            }
        }
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }
}

proof fn recv_commit_preserves(pre: GState, post: GState, i: int, ci: nat, mi: nat, rec: CommitRec)
    requires inv(pre), t_recv_commit(pre, post, i, ci, mi, rec),
    ensures inv(post),
{
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(vote_msg_ok(pre, v, c, t2, vlog));
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(ack_msg_ok(pre, v, t2, mi2));
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families: the receiver adopts the announced commit index, using
    // the message's witness record; its log matched its own term's leader log
    // through mi >= ci, which agrees with the witness prefix.
    let h = pre.hosts[i];
    assert(host_ok(pre, i));
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && ci > h.commit {
            assert(commit_msg_ok(pre, h.term, ci, rec));
            assert(pinned_at(pre.leader_log, h.log, mi - 1));
            assert(prefix_eq(h.log, pre.leader_log[h.term], mi)) by {
                assert(forall|k: int| 0 <= k <= mi - 1 ==>
                    h.log[k] == #[trigger] pre.leader_log[h.term][k]);
            }
            assert(prefix_eq(h.log, pre.leader_log[rec.term], ci)) by {
                assert(forall|k: int| 0 <= k < ci ==> h.log[k] == pre.leader_log[h.term][k]);
                assert(forall|k: int| 0 <= k < ci ==>
                    pre.leader_log[h.term][k] == pre.leader_log[rec.term][k]);
            }
            assert(post.hosts[i].crec == rec && post.hosts[i].commit == ci);
        }
    }
    assert forall|rec2: CommitRec| #[trigger] post.commits.contains(rec2) implies commit_rec_ok(post, rec2) by {
        assert(commit_rec_ok(pre, rec2));
    }
    assert forall|t9: nat, ci9: nat, rec9: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }) implies commit_msg_ok(post, t9, ci9, rec9) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec: rec9 }));
        assert(commit_msg_ok(pre, t9, ci9, rec9));
    }
    assert forall|rec2: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec2) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec2.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec2.term], rec2.ci) by {
        assert(pre.commits.contains(rec2) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec2.term], rec2.ci));
    }
    assert forall|rec2: CommitRec| #[trigger] post.commits.contains(rec2) implies commit_leader_ok(post, rec2) by {
        assert(commit_rec_ok(pre, rec2));
        assert(lterm_ok(pre, rec2.term));
        assert(commit_leader_ok(pre, rec2));
        // Host i's commit index only grew.
    }
}

proof fn bump_term_preserves(pre: GState, post: GState, i: int, t: nat)
    requires inv(pre), t_bump_term(pre, post, i, t),
    ensures inv(post),
{
    let h = pre.hosts[i];
    assert(host_ok(pre, i));
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(vote_msg_ok(pre, v, c, t2, vlog));
            if v == i && post.hosts[i].term == t2 {
                // The bump moved i's term strictly above every voted term.
                assert(pre.hosts[i].term >= t2);
                assert(false);
            }
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(ack_msg_ok(pre, v, t2, mi2));
            if v == i && post.hosts[i].term == t2 {
                assert(pre.hosts[i].term >= t2);
                assert(false);
            }
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Persistence: i's term grew, widening its compliance ranges; no new
    // messages, and its log is unchanged.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_persist_ok(pre, v2, t0, mi));
        if v2 == i {
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (post.hosts[v2].term + 1) as nat, i2)
                implies prefix_eq(post.hosts[v2].log, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[i].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[i].log, pre.leader_log[t0], i2));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }));
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
    }

    // Commit families: framed; host i's term only grows.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }
}

proof fn step_down_preserves(pre: GState, post: GState, i: int)
    requires inv(pre), t_step_down(pre, post, i),
    ensures inv(post),
{
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(vote_msg_ok(pre, v, c, t2, vlog));
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(ack_msg_ok(pre, v, t2, mi2));
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }
}

proof fn restart_preserves(pre: GState, post: GState, i: int, c: nat)
    requires inv(pre), t_restart(pre, post, i, c),
    ensures inv(post),
{
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        if j == i {
            assert(post.hosts[i].votes.subset_of(node_ids(post.n)));
        }
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(vote_msg_ok(pre, v, c, t2, vlog));
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(ack_msg_ok(pre, v, t2, mi2));
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

proof fn submit_read_preserves(pre: GState, post: GState, i: int)
    requires inv(pre), t_submit_read(pre, post, i),
    ensures inv(post),
{
    let h = pre.hosts[i];
    let u = h.term;
    assert(host_ok(pre, i));
    assert(pre.leader_log.dom().contains(u));

    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
        if j == i {
            assert(post.read_hwm[u] == post.hosts[i].read_seq);
        } else {
            let hj = pre.hosts[j];
            if hj.role is Leader {
                // Election safety via the recorded winner: j leads another term.
                assert(pre.leader_of[hj.term] == j);
                assert(pre.leader_of[u] == i);
                assert(hj.term != u);
                assert(post.read_hwm.dom().contains(hj.term) == pre.read_hwm.dom().contains(hj.term));
            }
        }
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
            assert(vote_msg_ok(pre, v, c, t2, vlog));
        }
        assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
            && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
        }
        assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
            && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
            assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
            assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(pre.net.contains(Msg::Ack { v, term: t2, mi: mi2 }));
            assert(ack_msg_ok(pre, v, t2, mi2));
        }
    }
    assert(post.read_hwm.dom().subset_of(post.leader_log.dom()));
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

proof fn confirm_read_preserves(pre: GState, post: GState, i: int, t: nat, sq: nat)
    requires inv(pre), t_confirm_read(pre, post, i, t, sq),
    ensures inv(post),
{
    let h = pre.hosts[i];
    assert(host_ok(pre, i));
    assert forall|j: int| 0 <= j < post.n implies #[trigger] host_ok(post, j) by {
        assert(host_ok(pre, j));
    }
    assert(inv_msgs(post)) by {
        assert forall|c: int, t2: nat, clog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog }) implies campaign_msg_ok(post, c, t2, clog) by {
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog }));
            assert(campaign_msg_ok(pre, c, t2, clog));
        }
        assert forall|v: int, c: int, t2: nat, vlog: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c, term: t2, vlog }) implies vote_msg_ok(post, v, c, t2, vlog) by {
            assert(pre.net.contains(Msg::Vote { v, c, term: t2, vlog }));
            assert(vote_msg_ok(pre, v, c, t2, vlog));
            if v == i && post.hosts[i].term == t2 {
                assert(pre.hosts[i].term >= t2);
                assert(t == t2);
                assert(pre.hosts[i].term == t2);
            }
        }
        assert forall|c: int, t2: nat, l1: Seq<AEntry>, l2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l1 })
            && #[trigger] post.net.contains(Msg::Campaign { c, term: t2, clog: l2 }) implies l1 == l2 by {
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l1 }));
            assert(pre.net.contains(Msg::Campaign { c, term: t2, clog: l2 }));
        }
        assert forall|v: int, c1: int, t2: nat, l1: Seq<AEntry>, c2: int, l2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 })
            && #[trigger] post.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }) implies c1 == c2 by {
            assert(pre.net.contains(Msg::Vote { v, c: c1, term: t2, vlog: l1 }));
            assert(pre.net.contains(Msg::Vote { v, c: c2, term: t2, vlog: l2 }));
        }
        assert forall|t2: nat, b2: nat, bt2: nat, entries2: Seq<AEntry>|
            #[trigger] post.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }) implies append_msg_ok(post, t2, b2, bt2, entries2) by {
            assert(pre.net.contains(Msg::Append { term: t2, base: b2, bterm: bt2, entries: entries2 }));
            assert(append_msg_ok(pre, t2, b2, bt2, entries2));
        }
        assert forall|v: int, t2: nat, mi2: nat|
            #[trigger] post.net.contains(Msg::Ack { v, term: t2, mi: mi2 }) implies ack_msg_ok(post, v, t2, mi2) by {
            assert(pre.net.contains(Msg::Ack { v, term: t2, mi: mi2 }));
            assert(ack_msg_ok(pre, v, t2, mi2));
        }
    }
    assert forall|u2: nat| #[trigger] post.leader_log.dom().contains(u2) implies lterm_ok(post, u2) by {
        assert(lterm_ok(pre, u2));
    }

    // Persistence: i's term may have grown (widening ranges); log unchanged.
    assert forall|v2: int, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi }) implies ack_persist_ok(post, v2, t0, mi) by {
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(ack_persist_ok(pre, v2, t0, mi));
        if v2 == i {
            assert forall|i2: nat| i2 <= mi
                && #[trigger] mid_compliant(post.leader_log, t0, (post.hosts[v2].term + 1) as nat, i2)
                implies prefix_eq(post.hosts[v2].log, post.leader_log[t0], i2) by {
                lemma_mid_narrow(pre.leader_log, t0, (pre.hosts[i].term + 1) as nat, (t + 1) as nat, i2);
                assert(prefix_eq(pre.hosts[i].log, pre.leader_log[t0], i2));
            }
        }
    }
    assert forall|v2: int, c2: int, u2: nat, vlog2: Seq<AEntry>, t0: nat, mi: nat|
        #[trigger] post.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 })
        && #[trigger] post.net.contains(Msg::Ack { v: v2, term: t0, mi })
        && t0 < u2 implies vote_persist_ok(post, u2, vlog2, t0, mi) by {
        assert(pre.net.contains(Msg::Vote { v: v2, c: c2, term: u2, vlog: vlog2 }));
        assert(pre.net.contains(Msg::Ack { v: v2, term: t0, mi }));
        assert(vote_persist_ok(pre, u2, vlog2, t0, mi));
    }

    // Commit families (framed: leader logs, commits, and commit messages are
    // unchanged). The restarted host's commit index may regress; its witness
    // still covers the shorter prefix. It is a follower afterwards, so the
    // committing-leader claim for its term is vacuous.
    assert forall|j2: int| 0 <= j2 < post.n implies #[trigger] host_commit_ok(post, j2) by {
        assert(host_commit_ok(pre, j2));
        if pre.hosts[j2].commit > 0 {
            assert(commit_rec_ok(pre, pre.hosts[j2].crec));
        }
        if j2 == i && post.hosts[i].commit > 0 {
            assert(prefix_eq(pre.hosts[i].log, pre.leader_log[pre.hosts[i].crec.term], pre.hosts[i].commit));
        }
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_rec_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
    }
    assert forall|t9: nat, ci9: nat, rec: CommitRec|
        #[trigger] post.net.contains(Msg::Commit { term: t9, ci: ci9, rec }) implies commit_msg_ok(post, t9, ci9, rec) by {
        assert(pre.net.contains(Msg::Commit { term: t9, ci: ci9, rec }));
        assert(commit_msg_ok(pre, t9, ci9, rec));
    }
    assert forall|rec: CommitRec, u9: nat|
        #[trigger] post.commits.contains(rec) && #[trigger] post.leader_log.dom().contains(u9) && u9 > rec.term
        implies prefix_eq(post.leader_log[u9], post.leader_log[rec.term], rec.ci) by {
        assert(pre.commits.contains(rec) && pre.leader_log.dom().contains(u9));
        assert(prefix_eq(pre.leader_log[u9], pre.leader_log[rec.term], rec.ci));
    }
    assert forall|rec: CommitRec| #[trigger] post.commits.contains(rec) implies commit_leader_ok(post, rec) by {
        assert(commit_rec_ok(pre, rec));
        assert(lterm_ok(pre, rec.term));
        assert(commit_leader_ok(pre, rec));
    }

}

/// Every step preserves the invariant.
pub proof fn step_preserves_inv(pre: GState, post: GState, step: TStep)
    requires inv(pre), next_step(pre, post, step),
    ensures inv(post),
{
    match step {
        TStep::Campaign { i } => campaign_preserves(pre, post, i),
        TStep::Grant { v, c, term, clog } => grant_preserves(pre, post, v, c, term, clog),
        TStep::CollectVote { i, v, vlog } => collect_vote_preserves(pre, post, i, v, vlog),
        TStep::BecomeLeader { i } => become_leader_preserves(pre, post, i),
        TStep::Propose { i, cmd } => propose_preserves(pre, post, i, cmd),
        TStep::SendAppend { i, b, e } => send_append_preserves(pre, post, i, b, e),
        TStep::RecvAppend { i, term, base, bterm, entries } =>
            recv_append_preserves(pre, post, i, term, base, bterm, entries),
        TStep::SendAck { i, mi } => send_ack_preserves(pre, post, i, mi),
        TStep::LeaderCommit { i, ci, q } => leader_commit_preserves(pre, post, i, ci, q),
        TStep::SendCommit { i, ci } => send_commit_preserves(pre, post, i, ci),
        TStep::RecvCommit { i, ci, mi, rec } => recv_commit_preserves(pre, post, i, ci, mi, rec),
        TStep::BumpTerm { i, term } => bump_term_preserves(pre, post, i, term),
        TStep::StepDown { i } => step_down_preserves(pre, post, i),
        TStep::Restart { i, commit } => restart_preserves(pre, post, i, commit),
        TStep::SubmitRead { i } => submit_read_preserves(pre, post, i),
        TStep::ConfirmRead { i, term, seq } => confirm_read_preserves(pre, post, i, term, seq),
    }
}

/// The invariant holds in every state of every execution.
pub proof fn execution_implies_inv(ex: Seq<GState>, k: int)
    requires
        execution(ex),
        0 <= k < ex.len(),
    ensures
        inv(ex[k]),
    decreases k,
{
    if k == 0 {
        init_implies_inv(ex[0]);
    } else {
        execution_implies_inv(ex, k - 1);
        assert(next(ex[k - 1], ex[k]));
        let step = choose|step: TStep| #[trigger] next_step(ex[k - 1], ex[k], step);
        step_preserves_inv(ex[k - 1], ex[k], step);
    }
}

// ---------------------------------------------------------------------------
// The safety theorems
// ---------------------------------------------------------------------------

/// Election Safety: at most one leader per term.
pub proof fn thm_election_safety(s: GState, i: int, j: int)
    requires
        inv(s),
        0 <= i < s.n,
        0 <= j < s.n,
        s.hosts[i].role is Leader,
        s.hosts[j].role is Leader,
        s.hosts[i].term == s.hosts[j].term,
    ensures
        i == j,
{
    // Both are the recorded winner of the shared term.
    assert(host_ok(s, i));
    assert(host_ok(s, j));
}

/// Log Matching: if two hosts' logs agree on the term of some position, they
/// agree on all entries up to and including it.
pub proof fn thm_log_matching(s: GState, i: int, j: int, k: int)
    requires
        inv(s),
        0 <= i < s.n,
        0 <= j < s.n,
        0 <= k < s.hosts[i].log.len(),
        k < s.hosts[j].log.len(),
        s.hosts[i].log[k].term == s.hosts[j].log[k].term,
    ensures
        forall|k2: int| 0 <= k2 <= k ==> s.hosts[i].log[k2] == s.hosts[j].log[k2],
{
    assert(host_ok(s, i));
    assert(host_ok(s, j));
    lemma_log_matching(s.leader_log, s.hosts[i].log, s.hosts[j].log, k);
}

/// Leader Completeness: a committed prefix is present, verbatim, in the log
/// of every leader of a later term.
pub proof fn thm_leader_completeness(s: GState, rec: CommitRec, i: int)
    requires
        inv(s),
        s.commits.contains(rec),
        0 <= i < s.n,
        s.hosts[i].role is Leader,
        s.hosts[i].term > rec.term,
    ensures
        prefix_eq(s.hosts[i].log, s.leader_log[rec.term], rec.ci),
{
    assert(host_ok(s, i));
    assert(commit_rec_ok(s, rec));
    assert(prefix_eq(s.leader_log[s.hosts[i].term], s.leader_log[rec.term], rec.ci));
}

/// State Machine Safety: two hosts never disagree on a committed (hence
/// applied) entry.
pub proof fn thm_state_machine_safety(s: GState, i: int, j: int, k: int)
    requires
        inv(s),
        0 <= i < s.n,
        0 <= j < s.n,
        0 <= k < s.hosts[i].commit,
        k < s.hosts[j].commit,
    ensures
        s.hosts[i].log[k] == s.hosts[j].log[k],
{
    assert(host_commit_ok(s, i));
    assert(host_commit_ok(s, j));
    let ri = s.hosts[i].crec;
    let rj = s.hosts[j].crec;
    assert(commit_rec_ok(s, ri));
    assert(commit_rec_ok(s, rj));
    // Both entries equal their commit witness's leader-log entry; the two
    // witnesses' logs agree below both commit indexes (Leader Completeness).
    assert(s.hosts[i].log[k] == s.leader_log[ri.term][k]);
    assert(s.hosts[j].log[k] == s.leader_log[rj.term][k]);
    if ri.term < rj.term {
        assert(prefix_eq(s.leader_log[rj.term], s.leader_log[ri.term], ri.ci));
    } else if rj.term < ri.term {
        assert(prefix_eq(s.leader_log[ri.term], s.leader_log[rj.term], rj.ci));
    }
}

/// Linearizable reads: when the leader serves a read — its committed tail is
/// from its own term (`maybe_read`'s commit_term check) and a quorum has
/// confirmed the read's sequence number — every write committed anywhere at
/// submission time is contained in the leader's committed (applied) prefix.
pub proof fn thm_read_linearizable(s: GState, l: int, r: ReadRec, conf: Set<int>)
    requires
        inv(s),
        0 <= l < s.n,
        s.hosts[l].role is Leader,
        s.reads.contains(r),
        r.term == s.hosts[l].term,
        s.hosts[l].commit >= 1,
        s.hosts[l].log[s.hosts[l].commit - 1].term == s.hosts[l].term,
        is_quorum(s.n, conf),
        forall|z: int| #[trigger] conf.contains(z) ==>
            exists|sq: nat| sq >= r.seq && s.net.contains(Msg::ReadConfirm { v: z, term: r.term, seq: sq }),
    ensures
        forall|rec: CommitRec| #[trigger] r.born.contains(rec) ==> {
            &&& rec.term <= r.term
            &&& rec.ci <= s.hosts[l].commit
            &&& prefix_eq(s.hosts[l].log, s.leader_log[rec.term], rec.ci)
        },
{
    let h = s.hosts[l];
    let t = r.term;
    assert(host_ok(s, l));
    assert(read_rec_ok(s, r));
    assert(s.leader_log[t] == h.log);
    assert(lterm_ok(s, t));
    assert forall|rec: CommitRec| #[trigger] r.born.contains(rec) implies {
        &&& rec.term <= t
        &&& rec.ci <= h.commit
        &&& prefix_eq(h.log, s.leader_log[rec.term], rec.ci)
    } by {
        assert(s.commits.contains(rec));
        assert(commit_rec_ok(s, rec));
        // A higher-term commit's ack quorum would overlap the confirm quorum
        // in a node whose confirmations all predate the read (R2) —
        // contradicting the quorum confirmation at r.seq.
        if rec.term > t {
            lemma_quorum_overlap(s.n, conf, rec.q.dom());
            let z = choose|z: int| conf.contains(z) && rec.q.dom().contains(z);
            let sq = choose|sq: nat| sq >= r.seq
                && s.net.contains(Msg::ReadConfirm { v: z, term: t, seq: sq });
            assert(sq < r.seq);
            assert(false);
        }
        if rec.term == t {
            // The leader's own record: its commit index covers it.
            assert(commit_leader_ok(s, rec));
            assert(s.leader_of[t] == l);
            assert(h.commit >= rec.ci);
            assert(prefix_eq(h.log, s.leader_log[t], rec.ci));
        } else {
            // Leader Completeness pins the committed prefix into the leader's
            // log; the own-term committed tail bounds the record's index.
            assert(prefix_eq(s.leader_log[t], s.leader_log[rec.term], rec.ci));
            assert(lterm_ok(s, rec.term));
            if rec.ci > h.commit {
                // The entry at the leader's commit index has term t, but it
                // sits inside the record's prefix, whose terms are at most
                // rec.term < t.
                assert(h.log[h.commit - 1] == s.leader_log[rec.term][h.commit - 1]);
                assert(s.leader_log[rec.term][h.commit - 1].term <= rec.term);
                assert(false);
            }
        }
    }
}

/// The headline result, over all reachable states: election safety and state
/// machine safety hold in every state of every execution of the protocol.
pub proof fn thm_raft_safety(ex: Seq<GState>, k: int)
    requires
        execution(ex),
        0 <= k < ex.len(),
    ensures
        forall|i: int, j: int|
            #![trigger ex[k].hosts[i], ex[k].hosts[j]]
            0 <= i < ex[k].n && 0 <= j < ex[k].n
            && ex[k].hosts[i].role is Leader && ex[k].hosts[j].role is Leader
            && ex[k].hosts[i].term == ex[k].hosts[j].term ==> i == j,
        forall|i: int, j: int, e: int|
            #![trigger ex[k].hosts[i].log[e], ex[k].hosts[j].log[e]]
            0 <= i < ex[k].n && 0 <= j < ex[k].n
            && 0 <= e < ex[k].hosts[i].commit && e < ex[k].hosts[j].commit ==>
            ex[k].hosts[i].log[e] == ex[k].hosts[j].log[e],
{
    execution_implies_inv(ex, k);
    let s = ex[k];
    assert forall|i: int, j: int|
        0 <= i < s.n && 0 <= j < s.n
        && s.hosts[i].role is Leader && s.hosts[j].role is Leader
        && s.hosts[i].term == s.hosts[j].term implies i == j by {
        thm_election_safety(s, i, j);
    }
    assert forall|i: int, j: int, e: int|
        0 <= i < s.n && 0 <= j < s.n
        && 0 <= e < s.hosts[i].commit && e < s.hosts[j].commit implies
        s.hosts[i].log[e] == s.hosts[j].log[e] by {
        thm_state_machine_safety(s, i, j, e);
    }
}

} // verus!
