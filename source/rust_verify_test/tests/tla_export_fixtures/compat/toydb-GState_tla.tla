---- MODULE GState_tla ----
\* Exported by verus -V tla-export from the Verus model in `test_crate`.
\* Mapping: structs are records; enum values are records with a `tag`;
\* Seq is a 1-based sequence (every index shifted once); Set is a set;
\* Map is a function (dom = DOMAIN, insert = :> @@); an ISet or IMap is a Set or
\* Map; Multiset is a function from the elements it holds to their counts (each
\* above 0, count = the value or 0); Option is a record tagged
\* None/Some with field v0; nat/int/uN are Int, and TypeOK keeps each variable
\* in its type's range (conjoined to Init, primed to Next); a spec fn is an operator, its
\* pre/post state parameters dropped and read as the unprimed/primed variables;
\* a quantifier is bounded from its guard, or from a CONSTANT Dom_<Type>.
\* What the export could not express is an Assert(FALSE, ...) that stops TLC
\* wherever it is evaluated.
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Dom_Option_Seq_u8_Some_v0, Dom_TStep_BumpTerm_term, Dom_TStep_LeaderCommit_q

VARIABLES n, hosts, net, leader_log, leader_of, voters, elect_log, elect_votes, commits, reads, read_hwm
vars == <<n, hosts, net, leader_log, leader_of, voters, elect_log, elect_votes, commits, reads, read_hwm>>

\* test_crate::init_host, @SOURCE@:880:1: 880:38 (#0)
init_host ==
    [term |-> 0, vote |-> [tag |-> "None"], role |-> [tag |-> "Follower"], log |-> << >>, commit |-> 0, votes |-> {}, vote_logs |-> [k__ \in {} |-> k__], crec |-> [term |-> 0, ci |-> 0, q |-> [k__2 \in {} |-> k__2]], read_seq |-> 0]

\* test_crate::init, @SOURCE@:895:1: 895:41 (#0)
init ==
    ((((((((((((n >= 1) /\ (n = Len(hosts))) /\ (\A i \in 0..(n) - 1 : (((0 <= i) /\ (i < n)) => (hosts[(i) + 1] = init_host)))) /\ (net = {})) /\ (leader_log = [k__ \in {} |-> k__])) /\ (leader_of = [k__2 \in {} |-> k__2])) /\ (voters = [k__3 \in {} |-> k__3])) /\ (elect_log = [k__4 \in {} |-> k__4])) /\ (elect_votes = [k__5 \in {} |-> k__5])) /\ (commits = {})) /\ (reads = {})) /\ (read_hwm = [k__6 \in {} |-> k__6]))

\* test_crate::unch_ghost, @SOURCE@:490:1: 490:63 (#0)
unch_ghost ==
    ((((((((leader_log' = leader_log) /\ (leader_of' = leader_of)) /\ (voters' = voters)) /\ (elect_log' = elect_log)) /\ (elect_votes' = elect_votes)) /\ (commits' = commits)) /\ (reads' = reads)) /\ (read_hwm' = read_hwm))

\* test_crate::t_campaign, @SOURCE@:518:1: 518:71 (#0)
t_campaign(i) ==
    (LET h == hosts[(i) + 1]
         t == (h.term + 1) IN (((((((0 <= i) /\ (i < n)) /\ ~((h.role = [tag |-> "Leader"]))) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.term = t, !.vote = [tag |-> "Some", v0 |-> i], !.role = [tag |-> "Candidate"], !.votes = ({} \cup {i}), !.vote_logs = ((i :> h.log) @@ [k__ \in {} |-> k__])]])) /\ (net' = ((net \cup {[tag |-> "Campaign", c |-> i, term |-> t, clog |-> h.log]}) \cup {[tag |-> "Vote", v |-> i, c |-> i, term |-> t, vlog |-> h.log]}))) /\ unch_ghost))

\* test_crate::last_term, @SOURCE@:247:1: 247:52 (#0)
last_term(log) ==
    (IF (Len(log) = 0) THEN 0 ELSE log[((Len(log) - 1)) + 1].term)

\* test_crate::up_to_date, @SOURCE@:254:1: 254:68 (#0)
up_to_date(a, b) ==
    (IF (last_term(a) > last_term(b)) THEN TRUE ELSE ((last_term(a) = last_term(b)) /\ (Len(a) >= Len(b))))

\* test_crate::t_grant, @SOURCE@:542:1: 542:103 (#0)
t_grant(v, c, t, clog) ==
    (LET h == hosts[(v) + 1] IN (((((((((((0 <= v) /\ (v < n)) /\ ~((v = c))) /\ ([tag |-> "Campaign", c |-> c, term |-> t, clog |-> clog] \in net)) /\ (t >= h.term)) /\ ((t = h.term) => ((h.role = [tag |-> "Follower"]) /\ (IF (h.vote = [tag |-> "None"]) THEN TRUE ELSE (h.vote = [tag |-> "Some", v0 |-> c]))))) /\ up_to_date(clog, h.log)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(v) + 1] = [h EXCEPT !.term = t, !.vote = [tag |-> "Some", v0 |-> c], !.role = [tag |-> "Follower"]]])) /\ (net' = (net \cup {[tag |-> "Vote", v |-> v, c |-> c, term |-> t, vlog |-> h.log]}))) /\ unch_ghost))

\* test_crate::t_collect_vote, @SOURCE@:562:1: 562:102 (#0)
t_collect_vote(i, v, vlog) ==
    (LET h == hosts[(i) + 1] IN ((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Candidate"])) /\ ([tag |-> "Vote", v |-> v, c |-> i, term |-> h.term, vlog |-> vlog] \in net)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.votes = (h.votes \cup {v}), !.vote_logs = ((v :> vlog) @@ h.vote_logs)]])) /\ (net' = net)) /\ unch_ghost))

\* test_crate::node_ids, @SOURCE@:236:1: 236:46 (#0)
node_ids(n_2) ==
    (0)..((n_2) - 1)

\* test_crate::is_quorum, @SOURCE@:241:1: 241:56 (#0)
is_quorum(n_2, q) ==
    ((q \subseteq node_ids(n_2)) /\ ((2 * Cardinality(q)) > n_2))

\* test_crate::unch_reads, @SOURCE@:510:1: 510:63 (#0)
unch_reads ==
    ((reads' = reads) /\ (read_hwm' = read_hwm))

\* test_crate::t_become_leader, @SOURCE@:580:1: 580:76 (#0)
t_become_leader(i) ==
    (LET h == hosts[(i) + 1]
         newlog == Append(h.log, [term |-> h.term, cmd |-> [tag |-> "None"]]) IN ((((((((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Candidate"])) /\ is_quorum(n, h.votes)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.role = [tag |-> "Leader"], !.log = newlog, !.read_seq = 0]])) /\ (net' = net)) /\ (leader_log' = ((h.term :> newlog) @@ leader_log))) /\ (leader_of' = ((h.term :> i) @@ leader_of))) /\ (voters' = ((h.term :> h.votes) @@ voters))) /\ (elect_log' = ((h.term :> h.log) @@ elect_log))) /\ (elect_votes' = ((h.term :> h.vote_logs) @@ elect_votes))) /\ (commits' = commits)) /\ unch_reads))

\* test_crate::unch_elect, @SOURCE@:502:1: 502:63 (#0)
unch_elect ==
    ((((leader_of' = leader_of) /\ (voters' = voters)) /\ (elect_log' = elect_log)) /\ (elect_votes' = elect_votes))

\* test_crate::t_propose, @SOURCE@:604:1: 604:92 (#0)
t_propose(i, cmd) ==
    (LET h == hosts[(i) + 1]
         newlog == Append(h.log, [term |-> h.term, cmd |-> cmd]) IN ((((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Leader"])) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.log = newlog]])) /\ (net' = net)) /\ (leader_log' = ((h.term :> newlog) @@ leader_log))) /\ (commits' = commits)) /\ unch_elect) /\ unch_reads))

\* test_crate::t_send_append, @SOURCE@:621:1: 621:90 (#0)
t_send_append(i, b, e) ==
    (LET h == hosts[(i) + 1]
         bt == (IF (b = 0) THEN 0 ELSE h.log[((b - 1)) + 1].term) IN ((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Leader"])) /\ ((b <= e) /\ (e <= Len(h.log)))) /\ (n' = n)) /\ (hosts' = hosts)) /\ (net' = (net \cup {[tag |-> "Append", term |-> h.term, base |-> b, bterm |-> bt, entries |-> SubSeq(h.log, (b) + 1, e)]}))) /\ unch_ghost))

\* test_crate::splice_is_noop, @SOURCE@:268:1: 268:91 (#0)
splice_is_noop(log, base, entries) ==
    (((base + Len(entries)) <= Len(log)) /\ (\A j \in 0..(Len(entries)) - 1 : (((0 <= j) /\ (j < Len(entries))) => (log[((base + j)) + 1] = entries[(j) + 1]))))

\* vstd::seq::impl&%2::spec_add, vstd/seq.rs:1064:5: 1064:59 (#0)
spec_add(self, rhs) ==
    (self \o rhs)

\* test_crate::splice, @SOURCE@:277:1: 277:90 (#0)
splice(log, base, entries) ==
    (IF splice_is_noop(log, base, entries) THEN log ELSE spec_add(SubSeq(log, (0) + 1, base), entries))

\* test_crate::t_recv_append, @SOURCE@:643:1: 645:10 (#0)
t_recv_append(i, t, b, bt, entries) ==
    (LET h == hosts[(i) + 1]
         newlog == splice(h.log, b, entries)
         newvote == (IF (t > h.term) THEN [tag |-> "None"] ELSE h.vote) IN ((((((((((0 <= i) /\ (i < n)) /\ ([tag |-> "Append", term |-> t, base |-> b, bterm |-> bt, entries |-> entries] \in net)) /\ (t >= h.term)) /\ ~(((h.role = [tag |-> "Leader"]) /\ (t = h.term)))) /\ (IF (b = 0) THEN TRUE ELSE ((b <= Len(h.log)) /\ (h.log[((b - 1)) + 1].term = bt)))) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.term = t, !.vote = newvote, !.role = [tag |-> "Follower"], !.log = newlog]])) /\ (net' = (net \cup {[tag |-> "Ack", v |-> i, term |-> t, mi |-> (b + Len(entries))]}))) /\ unch_ghost))

\* test_crate::t_send_ack, @SOURCE@:671:1: 671:80 (#0)
t_send_ack(i, mi) ==
    (LET h == hosts[(i) + 1] IN ((((((((0 <= i) /\ (i < n)) /\ ((1 <= mi) /\ (mi <= Len(h.log)))) /\ (h.log[((mi - 1)) + 1].term = h.term)) /\ (n' = n)) /\ (hosts' = hosts)) /\ (net' = (net \cup {[tag |-> "Ack", v |-> i, term |-> h.term, mi |-> mi]}))) /\ unch_ghost))

\* test_crate::t_leader_commit, @SOURCE@:685:1: 685:103 (#0)
t_leader_commit(i, ci, q) ==
    (LET h == hosts[(i) + 1]
         rec == [term |-> h.term, ci |-> ci, q |-> q]
         newcommit == (IF (ci > h.commit) THEN ci ELSE h.commit)
         newcrec == (IF (ci > h.commit) THEN rec ELSE h.crec) IN ((((((((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Leader"])) /\ ((1 <= ci) /\ (ci <= Len(h.log)))) /\ (h.log[((ci - 1)) + 1].term = h.term)) /\ is_quorum(n, DOMAIN q)) /\ (\A v \in DOMAIN q : ((v \in DOMAIN q) => ((q[v] >= ci) /\ ([tag |-> "Ack", v |-> v, term |-> h.term, mi |-> q[v]] \in net))))) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.commit = newcommit, !.crec = newcrec]])) /\ (net' = (net \cup {[tag |-> "Commit", term |-> h.term, ci |-> ci, rec |-> rec]}))) /\ (leader_log' = leader_log)) /\ (commits' = (commits \cup {rec}))) /\ unch_elect) /\ unch_reads))

\* test_crate::t_send_commit, @SOURCE@:707:1: 707:83 (#0)
t_send_commit(i, ci) ==
    (LET h == hosts[(i) + 1] IN ((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Leader"])) /\ ((1 <= ci) /\ (ci <= h.commit))) /\ (n' = n)) /\ (hosts' = hosts)) /\ (net' = (net \cup {[tag |-> "Commit", term |-> h.term, ci |-> ci, rec |-> h.crec]}))) /\ unch_ghost))

\* test_crate::t_recv_commit, @SOURCE@:720:1: 720:108 (#0)
t_recv_commit(i, ci, mi, rec) ==
    (LET h == hosts[(i) + 1]
         newcommit == (IF (ci > h.commit) THEN ci ELSE h.commit)
         newcrec == (IF (ci > h.commit) THEN rec ELSE h.crec) IN ((((((((((0 <= i) /\ (i < n)) /\ ([tag |-> "Commit", term |-> h.term, ci |-> ci, rec |-> rec] \in net)) /\ ((ci <= mi) /\ (mi <= Len(h.log)))) /\ (1 <= mi)) /\ (h.log[((mi - 1)) + 1].term = h.term)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.commit = newcommit, !.crec = newcrec]])) /\ (net' = net)) /\ unch_ghost))

\* test_crate::t_bump_term, @SOURCE@:741:1: 741:80 (#0)
t_bump_term(i, t) ==
    (LET h == hosts[(i) + 1] IN (((((((0 <= i) /\ (i < n)) /\ (t > h.term)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.term = t, !.vote = [tag |-> "None"], !.role = [tag |-> "Follower"]]])) /\ (net' = net)) /\ unch_ghost))

\* test_crate::t_step_down, @SOURCE@:759:1: 759:72 (#0)
t_step_down(i) ==
    (LET h == hosts[(i) + 1] IN (((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Candidate"])) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.role = [tag |-> "Follower"]]])) /\ (net' = net)) /\ unch_ghost))

\* test_crate::t_restart, @SOURCE@:774:1: 774:78 (#0)
t_restart(i, c) ==
    (LET h == hosts[(i) + 1] IN (((((((0 <= i) /\ (i < n)) /\ (c <= h.commit)) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.role = [tag |-> "Follower"], !.commit = c, !.votes = {}, !.vote_logs = [k__ \in {} |-> k__], !.read_seq = 0]])) /\ (net' = net)) /\ unch_ghost))

\* test_crate::t_submit_read, @SOURCE@:794:1: 794:74 (#0)
t_submit_read(i) ==
    (LET h == hosts[(i) + 1]
         s == (h.read_seq + 1) IN (((((((((((0 <= i) /\ (i < n)) /\ (h.role = [tag |-> "Leader"])) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.read_seq = s]])) /\ (net' = ((net \cup {[tag |-> "Read", term |-> h.term, seq |-> s]}) \cup {[tag |-> "ReadConfirm", v |-> i, term |-> h.term, seq |-> s]}))) /\ (leader_log' = leader_log)) /\ (commits' = commits)) /\ unch_elect) /\ (reads' = (reads \cup {[term |-> h.term, seq |-> s, born |-> commits]}))) /\ (read_hwm' = ((h.term :> s) @@ read_hwm))))

\* test_crate::t_confirm_read, @SOURCE@:813:1: 813:91 (#0)
t_confirm_read(i, t, s) ==
    (LET h == hosts[(i) + 1]
         newvote == (IF (t > h.term) THEN [tag |-> "None"] ELSE h.vote) IN (((((((((0 <= i) /\ (i < n)) /\ ([tag |-> "Read", term |-> t, seq |-> s] \in net)) /\ (t >= h.term)) /\ ~(((h.role = [tag |-> "Leader"]) /\ (t = h.term)))) /\ (n' = n)) /\ (hosts' = [hosts EXCEPT ![(i) + 1] = [h EXCEPT !.term = t, !.vote = newvote, !.role = [tag |-> "Follower"]]])) /\ (net' = (net \cup {[tag |-> "ReadConfirm", v |-> i, term |-> t, seq |-> s]}))) /\ unch_ghost))

\* test_crate::next_step, @SOURCE@:851:1: 851:75 (#0)
next_step(step) ==
    (LET m__ == step IN IF (m__.tag = "Campaign") THEN (LET i == m__.i IN t_campaign(i)) ELSE IF (m__.tag = "Grant") THEN (LET v == m__.v c == m__.c term == m__.term clog == m__.clog IN t_grant(v, c, term, clog)) ELSE IF (m__.tag = "CollectVote") THEN (LET i_2 == m__.i v_2 == m__.v vlog == m__.vlog IN t_collect_vote(i_2, v_2, vlog)) ELSE IF (m__.tag = "BecomeLeader") THEN (LET i_3 == m__.i IN t_become_leader(i_3)) ELSE IF (m__.tag = "Propose") THEN (LET i_4 == m__.i cmd == m__.cmd IN t_propose(i_4, cmd)) ELSE IF (m__.tag = "SendAppend") THEN (LET i_5 == m__.i b == m__.b e == m__.e IN t_send_append(i_5, b, e)) ELSE IF (m__.tag = "RecvAppend") THEN (LET i_6 == m__.i term_2 == m__.term base == m__.base bterm == m__.bterm entries == m__.entries IN t_recv_append(i_6, term_2, base, bterm, entries)) ELSE IF (m__.tag = "SendAck") THEN (LET i_7 == m__.i mi == m__.mi IN t_send_ack(i_7, mi)) ELSE IF (m__.tag = "LeaderCommit") THEN (LET i_8 == m__.i ci == m__.ci q == m__.q IN t_leader_commit(i_8, ci, q)) ELSE IF (m__.tag = "SendCommit") THEN (LET i_9 == m__.i ci_2 == m__.ci IN t_send_commit(i_9, ci_2)) ELSE IF (m__.tag = "RecvCommit") THEN (LET i_10 == m__.i ci_3 == m__.ci mi_2 == m__.mi rec == m__.rec IN t_recv_commit(i_10, ci_3, mi_2, rec)) ELSE IF (m__.tag = "BumpTerm") THEN (LET i_11 == m__.i term_3 == m__.term IN t_bump_term(i_11, term_3)) ELSE IF (m__.tag = "StepDown") THEN (LET i_12 == m__.i IN t_step_down(i_12)) ELSE IF (m__.tag = "Restart") THEN (LET i_13 == m__.i commit == m__.commit IN t_restart(i_13, commit)) ELSE IF (m__.tag = "SubmitRead") THEN (LET i_14 == m__.i IN t_submit_read(i_14)) ELSE IF (m__.tag = "ConfirmRead") THEN (LET i_15 == m__.i term_4 == m__.term seq == m__.seq IN t_confirm_read(i_15, term_4, seq)) ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::next, @SOURCE@:873:1: 873:57 (#0)
next ==
    ((\E i__ \in 0..(n) - 1 : (LET step == [tag |-> "Campaign", i |-> i__] IN next_step(step))) \/ (\E v__ \in 0..(n) - 1 : (\E c__ \in (LET h == hosts[(v__) + 1] IN {m__4.c : m__4 \in {m__3 \in net : m__3.tag = "Campaign"}}) : (\E term__ \in (LET h_2 == hosts[(v__) + 1] IN {x__4 \in {m__8.term : m__8 \in {m__7 \in net : m__7.tag = "Campaign"}} : (x__4 >= 0)}) : (\E clog__ \in (LET h_3 == hosts[(v__) + 1] IN {m__12.clog : m__12 \in {m__11 \in net : m__11.tag = "Campaign"}}) : (LET step == [tag |-> "Grant", v |-> v__, c |-> c__, term |-> term__, clog |-> clog__] IN next_step(step)))))) \/ (\E i__2 \in {m__16.c : m__16 \in {m__15 \in net : m__15.tag = "Vote"}} : (\E v__2 \in (LET h_4 == hosts[(i__2) + 1] IN {m__20.v : m__20 \in {m__19 \in net : m__19.tag = "Vote"}}) : (\E vlog__ \in (LET h_5 == hosts[(i__2) + 1] IN {m__24.vlog : m__24 \in {m__23 \in net : m__23.tag = "Vote"}}) : (LET step == [tag |-> "CollectVote", i |-> i__2, v |-> v__2, vlog |-> vlog__] IN next_step(step))))) \/ (\E i__3 \in 0..(n) - 1 : (LET step == [tag |-> "BecomeLeader", i |-> i__3] IN next_step(step))) \/ (\E i__4 \in 0..(n) - 1 : (\E cmd__ \in ({[tag |-> "None"]} \cup {[tag |-> "Some", v0 |-> v0__] : v0__ \in Dom_Option_Seq_u8_Some_v0}) : (LET step == [tag |-> "Propose", i |-> i__4, cmd |-> cmd__] IN next_step(step)))) \/ (\E i__5 \in 0..(n) - 1 : (\E b__ \in (LET h_7 == hosts[(i__5) + 1] IN 0..Len(h_7.log)) : (\E e__ \in (LET h_8 == hosts[(i__5) + 1] bt == (IF (b__ = 0) THEN 0 ELSE h_8.log[((b__ - 1)) + 1].term) IN (IF (b__) > 0 THEN (b__) ELSE 0)..Len(h_8.log)) : (LET step == [tag |-> "SendAppend", i |-> i__5, b |-> b__, e |-> e__] IN next_step(step))))) \/ (\E i__6 \in 0..(n) - 1 : (\E term__2 \in (LET h_9 == hosts[(i__6) + 1] IN {x__14 \in {m__28.term : m__28 \in {m__27 \in net : m__27.tag = "Append"}} : (x__14 >= 0)}) : (\E base__ \in (LET h_10 == hosts[(i__6) + 1] newvote == (IF (term__2 > h_10.term) THEN [tag |-> "None"] ELSE h_10.vote) IN {x__16 \in {m__32.base : m__32 \in {m__31 \in net : m__31.tag = "Append"}} : (x__16 >= 0)}) : (\E bterm__ \in (LET h_11 == hosts[(i__6) + 1] newvote_2 == (IF (term__2 > h_11.term) THEN [tag |-> "None"] ELSE h_11.vote) IN {x__18 \in {m__36.bterm : m__36 \in {m__35 \in net : m__35.tag = "Append"}} : (x__18 >= 0)}) : (\E entries__ \in (LET h_12 == hosts[(i__6) + 1] newvote_3 == (IF (term__2 > h_12.term) THEN [tag |-> "None"] ELSE h_12.vote) IN {m__40.entries : m__40 \in {m__39 \in net : m__39.tag = "Append"}}) : (LET step == [tag |-> "RecvAppend", i |-> i__6, term |-> term__2, base |-> base__, bterm |-> bterm__, entries |-> entries__] IN next_step(step))))))) \/ (\E i__7 \in 0..(n) - 1 : (\E mi__ \in (LET h_13 == hosts[(i__7) + 1] IN (IF (1) > 0 THEN (1) ELSE 0)..Len(h_13.log)) : (LET step == [tag |-> "SendAck", i |-> i__7, mi |-> mi__] IN next_step(step)))) \/ (\E i__8 \in 0..(n) - 1 : (\E ci__ \in (LET h_14 == hosts[(i__8) + 1] IN (IF (1) > 0 THEN (1) ELSE 0)..Len(h_14.log)) : (\E q__ \in Dom_TStep_LeaderCommit_q : (LET step == [tag |-> "LeaderCommit", i |-> i__8, ci |-> ci__, q |-> q__] IN next_step(step))))) \/ (\E i__9 \in 0..(n) - 1 : (\E ci__2 \in (LET h_16 == hosts[(i__9) + 1] IN (IF (1) > 0 THEN (1) ELSE 0)..h_16.commit) : (LET step == [tag |-> "SendCommit", i |-> i__9, ci |-> ci__2] IN next_step(step)))) \/ (\E i__10 \in 0..(n) - 1 : (\E ci__3 \in (LET h_17 == hosts[(i__10) + 1] IN {x__22 \in {m__44.ci : m__44 \in {m__43 \in net : m__43.tag = "Commit"}} : (x__22 >= 0)}) : (\E mi__2 \in (LET h_18 == hosts[(i__10) + 1] newcommit_2 == (IF (ci__3 > h_18.commit) THEN ci__3 ELSE h_18.commit) IN (IF (1) > 0 THEN (1) ELSE 0)..Len(h_18.log)) : (\E rec__ \in (LET h_19 == hosts[(i__10) + 1] newcommit_3 == (IF (ci__3 > h_19.commit) THEN ci__3 ELSE h_19.commit) IN {m__48.rec : m__48 \in {m__47 \in net : m__47.tag = "Commit"}}) : (LET step == [tag |-> "RecvCommit", i |-> i__10, ci |-> ci__3, mi |-> mi__2, rec |-> rec__] IN next_step(step)))))) \/ (\E i__11 \in 0..(n) - 1 : (\E term__3 \in Dom_TStep_BumpTerm_term : (LET step == [tag |-> "BumpTerm", i |-> i__11, term |-> term__3] IN next_step(step)))) \/ (\E i__12 \in 0..(n) - 1 : (LET step == [tag |-> "StepDown", i |-> i__12] IN next_step(step))) \/ (\E i__13 \in 0..(n) - 1 : (\E commit__ \in (LET h_21 == hosts[(i__13) + 1] IN 0..h_21.commit) : (LET step == [tag |-> "Restart", i |-> i__13, commit |-> commit__] IN next_step(step)))) \/ (\E i__14 \in 0..(n) - 1 : (LET step == [tag |-> "SubmitRead", i |-> i__14] IN next_step(step))) \/ (\E i__15 \in 0..(n) - 1 : (\E term__4 \in (LET h_22 == hosts[(i__15) + 1] IN {x__26 \in {m__52.term : m__52 \in {m__51 \in net : m__51.tag = "Read"}} : (x__26 >= 0)}) : (\E seq__ \in (LET h_23 == hosts[(i__15) + 1] newvote_4 == (IF (term__4 > h_23.term) THEN [tag |-> "None"] ELSE h_23.vote) IN {x__28 \in {m__56.seq : m__56 \in {m__55 \in net : m__55.tag = "Read"}} : (x__28 >= 0)}) : (LET step == [tag |-> "ConfirmRead", i |-> i__15, term |-> term__4, seq |-> seq__] IN next_step(step))))))

\* test_crate::inv_wf, @SOURCE@:940:1: 940:43 (#0)
inv_wf ==
    ((n >= 1) /\ (n = Len(hosts)))

\* test_crate::log_wf, @SOURCE@:924:1: 924:50 (#0)
log_wf(log) ==
    ((\A j \in 0..(Len(log)) - 1 : (((0 <= j) /\ (j < Len(log))) => (log[(j) + 1].term >= 1))) /\ (\A j1 \in 0..(Len(log)) - 1 : (\A j2 \in j1..(Len(log)) - 1 : (((0 <= j1) /\ (j1 <= j2) /\ (j2 < Len(log))) => (log[(j1) + 1].term <= log[(j2) + 1].term)))))

\* test_crate::terms_le, @SOURCE@:930:1: 930:60 (#0)
terms_le(log, t) ==
    (\A j \in 0..(Len(log)) - 1 : (((0 <= j) /\ (j < Len(log))) => (log[(j) + 1].term <= t)))

\* test_crate::pinned_at, @SOURCE@:290:1: 290:87 (#0)
pinned_at(m, log, j) ==
    (LET t == log[(j) + 1].term IN (((t \in DOMAIN m) /\ (j < Len(m[t]))) /\ (\A k \in 0..j : (((0 <= k) /\ (k <= j)) => (log[(k) + 1] = m[t][(k) + 1])))))

\* test_crate::log_pinned, @SOURCE@:298:1: 298:80 (#0)
log_pinned(m, log) ==
    (\A j \in 0..(Len(log)) - 1 : (((0 <= j) /\ (j < Len(log))) => pinned_at(m, log, j)))

\* test_crate::terms_lt, @SOURCE@:935:1: 935:60 (#0)
terms_lt(log, t) ==
    (\A j \in 0..(Len(log)) - 1 : (((0 <= j) /\ (j < Len(log))) => (log[(j) + 1].term < t)))

\* test_crate::host_ok, @SOURCE@:950:1: 950:52 (#0)
host_ok(i) ==
    (LET h == hosts[(i) + 1] IN ((((((log_wf(h.log) /\ terms_le(h.log, h.term)) /\ log_pinned(leader_log, h.log)) /\ (h.votes \subseteq node_ids(n))) /\ (LET m__ == h.vote IN IF (m__.tag = "Some") THEN (LET c == m__.v0 IN ((0 <= c) /\ (c < n))) ELSE TRUE)) /\ ((h.role = [tag |-> "Candidate"]) => ((((((h.term >= 1) /\ (h.vote = [tag |-> "Some", v0 |-> i])) /\ ([tag |-> "Campaign", c |-> i, term |-> h.term, clog |-> h.log] \in net)) /\ terms_lt(h.log, h.term)) /\ (\A v \in h.votes : ((v \in h.votes) => ((v \in DOMAIN h.vote_logs) /\ ([tag |-> "Vote", v |-> v, c |-> i, term |-> h.term, vlog |-> h.vote_logs[v]] \in net))))) /\ ((h.term \in DOMAIN leader_of) => ~((leader_of[h.term] = i)))))) /\ ((h.role = [tag |-> "Leader"]) => (((((((h.term >= 1) /\ (h.vote = [tag |-> "Some", v0 |-> i])) /\ (h.term \in DOMAIN leader_log)) /\ (leader_of[h.term] = i)) /\ (leader_log[h.term] = h.log)) /\ ((h.term \in DOMAIN read_hwm) => (read_hwm[h.term] = h.read_seq))) /\ (~((h.term \in DOMAIN read_hwm)) => (h.read_seq = 0))))))

\* test_crate::inv_hosts, @SOURCE@:986:1: 986:46 (#0)
inv_hosts ==
    (\A i \in 0..(n) - 1 : (((0 <= i) /\ (i < n)) => host_ok(i)))

\* test_crate::campaign_msg_ok, @SOURCE@:997:1: 997:87 (#0)
campaign_msg_ok(c, t, clog) ==
    (((((((0 <= c) /\ (c < n)) /\ (t >= 1)) /\ (hosts[(c) + 1].term >= t)) /\ log_wf(clog)) /\ terms_lt(clog, t)) /\ log_pinned(leader_log, clog))

\* test_crate::vote_msg_ok, @SOURCE@:1011:1: 1011:91 (#0)
vote_msg_ok(v, c, t, vlog) ==
    (((((((((((0 <= v) /\ (v < n)) /\ ((0 <= c) /\ (c < n))) /\ (t >= 1)) /\ (hosts[(v) + 1].term >= t)) /\ ((hosts[(v) + 1].term = t) => (hosts[(v) + 1].vote = [tag |-> "Some", v0 |-> c]))) /\ (hosts[(c) + 1].term >= t)) /\ log_wf(vlog)) /\ terms_le(vlog, t)) /\ log_pinned(leader_log, vlog)) /\ (((hosts[(c) + 1].role = [tag |-> "Candidate"]) /\ (hosts[(c) + 1].term = t)) => up_to_date(hosts[(c) + 1].log, vlog)))

\* test_crate::append_msg_ok, @SOURCE@:1025:1: 1025:97 (#0)
append_msg_ok(t, b, bt, entries) ==
    ((((((t >= 1) /\ (t \in DOMAIN leader_log)) /\ ((b + Len(entries)) <= Len(leader_log[t]))) /\ (\A j \in 0..(Len(entries)) - 1 : (((0 <= j) /\ (j < Len(entries))) => (entries[(j) + 1] = leader_log[t][((b + j)) + 1])))) /\ ((b >= 1) => ((b <= Len(leader_log[t])) /\ (bt = leader_log[t][((b - 1)) + 1].term)))) /\ ((b = 0) => (bt = 0)))

\* test_crate::prefix_eq, @SOURCE@:260:1: 260:75 (#0)
prefix_eq(a, b, i) ==
    (((i <= Len(a)) /\ (i <= Len(b))) /\ (\A j \in 0..(i) - 1 : (((0 <= j) /\ (j < i)) => (a[(j) + 1] = b[(j) + 1]))))

\* test_crate::ack_msg_ok, @SOURCE@:1038:1: 1038:72 (#0)
ack_msg_ok(v, t, mi) ==
    (((((((0 <= v) /\ (v < n)) /\ (t >= 1)) /\ (hosts[(v) + 1].term >= t)) /\ (t \in DOMAIN leader_log)) /\ (mi <= Len(leader_log[t]))) /\ ((hosts[(v) + 1].term = t) => prefix_eq(hosts[(v) + 1].log, leader_log[t], mi)))

\* test_crate::inv_msgs, @SOURCE@:1047:1: 1047:45 (#0)
inv_msgs ==
    ((((((\A c \in {m__2.c : m__2 \in {m__ \in net : m__.tag = "Campaign"}} : (\A t \in {x__2 \in {m__4.term : m__4 \in {m__3 \in net : m__3.tag = "Campaign"}} : (x__2 >= 0)} : (\A clog \in {m__6.clog : m__6 \in {m__5 \in net : m__5.tag = "Campaign"}} : (([tag |-> "Campaign", c |-> c, term |-> t, clog |-> clog] \in net) => campaign_msg_ok(c, t, clog))))) /\ (\A c_2 \in {m__8.c : m__8 \in {m__7 \in net : m__7.tag = "Campaign"}} : (\A t_2 \in {x__5 \in {m__10.term : m__10 \in {m__9 \in net : m__9.tag = "Campaign"}} : (x__5 >= 0)} : (\A l1 \in {m__12.clog : m__12 \in {m__11 \in net : m__11.tag = "Campaign"}} : (\A l2 \in {m__14.clog : m__14 \in {m__13 \in net : m__13.tag = "Campaign"}} : ((([tag |-> "Campaign", c |-> c_2, term |-> t_2, clog |-> l1] \in net) /\ ([tag |-> "Campaign", c |-> c_2, term |-> t_2, clog |-> l2] \in net)) => (l1 = l2))))))) /\ (\A v \in {m__16.v : m__16 \in {m__15 \in net : m__15.tag = "Vote"}} : (\A c_3 \in {m__18.c : m__18 \in {m__17 \in net : m__17.tag = "Vote"}} : (\A t_3 \in {x__10 \in {m__20.term : m__20 \in {m__19 \in net : m__19.tag = "Vote"}} : (x__10 >= 0)} : (\A vlog \in {m__22.vlog : m__22 \in {m__21 \in net : m__21.tag = "Vote"}} : (([tag |-> "Vote", v |-> v, c |-> c_3, term |-> t_3, vlog |-> vlog] \in net) => vote_msg_ok(v, c_3, t_3, vlog))))))) /\ (\A v_2 \in {m__24.v : m__24 \in {m__23 \in net : m__23.tag = "Vote"}} : (\A c1 \in {m__26.c : m__26 \in {m__25 \in net : m__25.tag = "Vote"}} : (\A t_4 \in {x__14 \in {m__28.term : m__28 \in {m__27 \in net : m__27.tag = "Vote"}} : (x__14 >= 0)} : (\A l1_2 \in {m__30.vlog : m__30 \in {m__29 \in net : m__29.tag = "Vote"}} : (\A c2 \in {m__32.c : m__32 \in {m__31 \in net : m__31.tag = "Vote"}} : (\A l2_2 \in {m__34.vlog : m__34 \in {m__33 \in net : m__33.tag = "Vote"}} : ((([tag |-> "Vote", v |-> v_2, c |-> c1, term |-> t_4, vlog |-> l1_2] \in net) /\ ([tag |-> "Vote", v |-> v_2, c |-> c2, term |-> t_4, vlog |-> l2_2] \in net)) => (c1 = c2))))))))) /\ (\A t_5 \in {x__18 \in {m__36.term : m__36 \in {m__35 \in net : m__35.tag = "Append"}} : (x__18 >= 0)} : (\A b \in {x__19 \in {m__38.base : m__38 \in {m__37 \in net : m__37.tag = "Append"}} : (x__19 >= 0)} : (\A bt \in {x__20 \in {m__40.bterm : m__40 \in {m__39 \in net : m__39.tag = "Append"}} : (x__20 >= 0)} : (\A entries \in {m__42.entries : m__42 \in {m__41 \in net : m__41.tag = "Append"}} : (([tag |-> "Append", term |-> t_5, base |-> b, bterm |-> bt, entries |-> entries] \in net) => append_msg_ok(t_5, b, bt, entries))))))) /\ (\A v_3 \in {m__44.v : m__44 \in {m__43 \in net : m__43.tag = "Ack"}} : (\A t_6 \in {x__23 \in {m__46.term : m__46 \in {m__45 \in net : m__45.tag = "Ack"}} : (x__23 >= 0)} : (\A mi \in {x__24 \in {m__48.mi : m__48 \in {m__47 \in net : m__47.tag = "Ack"}} : (x__24 >= 0)} : (([tag |-> "Ack", v |-> v_3, term |-> t_6, mi |-> mi] \in net) => ack_msg_ok(v_3, t_6, mi))))))

\* test_crate::mid_compliant, @SOURCE@:1138:1: 1138:90 (#0)
mid_compliant(m, t, ub, i) ==
    (\A x \in {x__ \in DOMAIN m : (x__ >= 0)} : ((((t < x) /\ (x < ub)) /\ (x \in DOMAIN m)) => prefix_eq(m[x], m[t], i)))

\* test_crate::frozen_persist_at, @SOURCE@:1077:1: 1077:98 (#0)
frozen_persist_at(u, vlog, t, mi) ==
    (\A i \in 0..mi : (((i <= mi) /\ mid_compliant(leader_log, t, u, i)) => prefix_eq(vlog, leader_log[t], i)))

\* test_crate::frozen_persist_ok, @SOURCE@:1082:1: 1082:89 (#0)
frozen_persist_ok(u, vlog, w) ==
    (\A t \in {x__ \in {m__2.term : m__2 \in {m__ \in net : m__.tag = "Ack"}} : (x__ >= 0)} : (\A mi \in {x__2 \in {m__4.mi : m__4 \in {m__3 \in net : m__3.tag = "Ack"}} : (x__2 >= 0)} : (((t < u) /\ ([tag |-> "Ack", v |-> w, term |-> t, mi |-> mi] \in net)) => frozen_persist_at(u, vlog, t, mi))))

\* test_crate::voter_ok, @SOURCE@:1090:1: 1090:61 (#0)
voter_ok(u, x) ==
    (LET vlog == elect_votes[u][x] IN ((((x \in DOMAIN elect_votes[u]) /\ ([tag |-> "Vote", v |-> x, c |-> leader_of[u], term |-> u, vlog |-> vlog] \in net)) /\ up_to_date(elect_log[u], vlog)) /\ frozen_persist_ok(u, vlog, x)))

\* test_crate::lterm_ok, @SOURCE@:1103:1: 1103:53 (#0)
lterm_ok(u) ==
    (LET ll == leader_log[u]
         elog == elect_log[u] IN ((((((((((((((((((u >= 1) /\ (Len(ll) >= 1)) /\ log_wf(ll)) /\ terms_le(ll, u)) /\ log_pinned(leader_log, ll)) /\ (last_term(ll) = u)) /\ ((0 <= leader_of[u]) /\ (leader_of[u] < n))) /\ (hosts[(leader_of[u]) + 1].term >= u)) /\ (u \in DOMAIN voters)) /\ (u \in DOMAIN elect_log)) /\ (u \in DOMAIN elect_votes)) /\ is_quorum(n, voters[u])) /\ prefix_eq(ll, elog, Len(elog))) /\ (Len(elog) < Len(ll))) /\ (ll[(Len(elog)) + 1].term = u)) /\ terms_lt(elog, u)) /\ log_wf(elog)) /\ (\A x \in voters[u] : ((x \in voters[u]) => voter_ok(u, x)))))

\* test_crate::inv_lterms, @SOURCE@:1126:1: 1126:47 (#0)
inv_lterms ==
    (((DOMAIN leader_of = DOMAIN leader_log) /\ (DOMAIN read_hwm \subseteq DOMAIN leader_log)) /\ (\A u \in {x__ \in DOMAIN leader_log : (x__ >= 0)} : ((u \in DOMAIN leader_log) => lterm_ok(u))))

\* test_crate::ack_persist_ok, @SOURCE@:1146:1: 1146:76 (#0)
ack_persist_ok(v, t, mi) ==
    (\A i \in 0..mi : (((i <= mi) /\ mid_compliant(leader_log, t, (hosts[(v) + 1].term + 1), i)) => prefix_eq(hosts[(v) + 1].log, leader_log[t], i)))

\* test_crate::inv_ack_persist, @SOURCE@:1152:1: 1152:52 (#0)
inv_ack_persist ==
    (\A v \in {m__2.v : m__2 \in {m__ \in net : m__.tag = "Ack"}} : (\A t \in {x__2 \in {m__4.term : m__4 \in {m__3 \in net : m__3.tag = "Ack"}} : (x__2 >= 0)} : (\A mi \in {x__3 \in {m__6.mi : m__6 \in {m__5 \in net : m__5.tag = "Ack"}} : (x__3 >= 0)} : (([tag |-> "Ack", v |-> v, term |-> t, mi |-> mi] \in net) => ack_persist_ok(v, t, mi)))))

\* test_crate::vote_persist_ok, @SOURCE@:1161:1: 1161:96 (#0)
vote_persist_ok(u, vlog, t, mi) ==
    (\A i \in 0..mi : (((i <= mi) /\ mid_compliant(leader_log, t, (u + 1), i)) => prefix_eq(vlog, leader_log[t], i)))

\* test_crate::inv_vote_persist, @SOURCE@:1166:1: 1166:53 (#0)
inv_vote_persist ==
    (\A v \in {m__2.v : m__2 \in {m__ \in net : m__.tag = "Vote"}} : (\A c \in {m__4.c : m__4 \in {m__3 \in net : m__3.tag = "Vote"}} : (\A u \in {x__3 \in {m__6.term : m__6 \in {m__5 \in net : m__5.tag = "Vote"}} : (x__3 >= 0)} : (\A vlog \in {m__8.vlog : m__8 \in {m__7 \in net : m__7.tag = "Vote"}} : (\A t \in {x__5 \in {m__10.term : m__10 \in {m__9 \in net : m__9.tag = "Ack"}} : (x__5 >= 0)} : (\A mi \in {x__6 \in {m__12.mi : m__12 \in {m__11 \in net : m__11.tag = "Ack"}} : (x__6 >= 0)} : (((([tag |-> "Vote", v |-> v, c |-> c, term |-> u, vlog |-> vlog] \in net) /\ ([tag |-> "Ack", v |-> v, term |-> t, mi |-> mi] \in net)) /\ (t < u)) => vote_persist_ok(u, vlog, t, mi))))))))

\* test_crate::commit_rec_ok, @SOURCE@:1254:1: 1254:66 (#0)
commit_rec_ok(rec) ==
    (((((rec.term \in DOMAIN leader_log) /\ ((1 <= rec.ci) /\ (rec.ci <= Len(leader_log[rec.term])))) /\ (leader_log[rec.term][((rec.ci - 1)) + 1].term = rec.term)) /\ is_quorum(n, DOMAIN rec.q)) /\ (\A v \in DOMAIN rec.q : ((v \in DOMAIN rec.q) => ((rec.q[v] >= rec.ci) /\ ([tag |-> "Ack", v |-> v, term |-> rec.term, mi |-> rec.q[v]] \in net)))))

\* test_crate::inv_commits, @SOURCE@:1263:1: 1263:48 (#0)
inv_commits ==
    (\A rec \in commits : ((rec \in commits) => commit_rec_ok(rec)))

\* test_crate::inv_leader_completeness, @SOURCE@:1269:1: 1269:60 (#0)
inv_leader_completeness ==
    (\A rec \in commits : (\A u \in {x__2 \in DOMAIN leader_log : (x__2 >= 0)} : ((((rec \in commits) /\ (u \in DOMAIN leader_log)) /\ (u > rec.term)) => prefix_eq(leader_log[u], leader_log[rec.term], rec.ci))))

\* test_crate::commit_msg_ok, @SOURCE@:1278:1: 1278:83 (#0)
commit_msg_ok(t, ci, rec) ==
    ((((((((t >= 1) /\ (ci >= 1)) /\ (t \in DOMAIN leader_log)) /\ (ci <= Len(leader_log[t]))) /\ (rec \in commits)) /\ (rec.ci >= ci)) /\ (rec.term <= t)) /\ prefix_eq(leader_log[t], leader_log[rec.term], ci))

\* test_crate::inv_commit_msgs, @SOURCE@:1289:1: 1289:52 (#0)
inv_commit_msgs ==
    (\A t \in {x__ \in {m__2.term : m__2 \in {m__ \in net : m__.tag = "Commit"}} : (x__ >= 0)} : (\A ci \in {x__2 \in {m__4.ci : m__4 \in {m__3 \in net : m__3.tag = "Commit"}} : (x__2 >= 0)} : (\A rec \in {m__6.rec : m__6 \in {m__5 \in net : m__5.tag = "Commit"}} : (([tag |-> "Commit", term |-> t, ci |-> ci, rec |-> rec] \in net) => commit_msg_ok(t, ci, rec)))))

\* test_crate::host_commit_ok, @SOURCE@:1296:1: 1296:59 (#0)
host_commit_ok(i) ==
    (LET h == hosts[(i) + 1] IN ((h.commit > 0) => ((((h.crec \in commits) /\ (h.crec.ci >= h.commit)) /\ (h.crec.term <= h.term)) /\ prefix_eq(h.log, leader_log[h.crec.term], h.commit))))

\* test_crate::inv_host_commits, @SOURCE@:1306:1: 1306:53 (#0)
inv_host_commits ==
    (\A i \in 0..(n) - 1 : (((0 <= i) /\ (i < n)) => host_commit_ok(i)))

\* test_crate::commit_leader_ok, @SOURCE@:1314:1: 1314:69 (#0)
commit_leader_ok(rec) ==
    (LET l == hosts[(leader_of[rec.term]) + 1] IN (((l.role = [tag |-> "Leader"]) /\ (l.term = rec.term)) => (l.commit >= rec.ci)))

\* test_crate::inv_commit_leaders, @SOURCE@:1319:1: 1319:55 (#0)
inv_commit_leaders ==
    (\A rec \in commits : ((rec \in commits) => commit_leader_ok(rec)))

\* test_crate::read_msg_ok, @SOURCE@:1329:1: 1329:65 (#0)
read_msg_ok(t, sq) ==
    ((t \in DOMAIN read_hwm) /\ ((1 <= sq) /\ (sq <= read_hwm[t])))

\* test_crate::confirm_msg_ok, @SOURCE@:1336:1: 1336:76 (#0)
confirm_msg_ok(v, t, sq) ==
    (((((0 <= v) /\ (v < n)) /\ (hosts[(v) + 1].term >= t)) /\ (t \in DOMAIN read_hwm)) /\ ((1 <= sq) /\ (sq <= read_hwm[t])))

\* test_crate::read_rec_ok, @SOURCE@:1347:1: 1347:60 (#0)
read_rec_ok(r) ==
    (((((1 <= r.seq) /\ (r.term \in DOMAIN read_hwm)) /\ (r.seq <= read_hwm[r.term])) /\ (\A rec \in r.born : ((rec \in r.born) => (rec \in commits)))) /\ (\A rec_2 \in r.born : (\A z \in DOMAIN rec_2.q : (\A sq \in {x__4 \in {m__2.seq : m__2 \in {m__ \in net : m__.tag = "ReadConfirm"}} : (x__4 >= 0)} : (((((rec_2 \in r.born) /\ (rec_2.term > r.term)) /\ (z \in DOMAIN rec_2.q)) /\ ([tag |-> "ReadConfirm", v |-> z, term |-> r.term, seq |-> sq] \in net)) => (sq < r.seq))))))

\* test_crate::inv_reads, @SOURCE@:1359:1: 1359:46 (#0)
inv_reads ==
    (((\A t \in {x__ \in {m__2.term : m__2 \in {m__ \in net : m__.tag = "Read"}} : (x__ >= 0)} : (\A sq \in {x__2 \in {m__4.seq : m__4 \in {m__3 \in net : m__3.tag = "Read"}} : (x__2 >= 0)} : (([tag |-> "Read", term |-> t, seq |-> sq] \in net) => read_msg_ok(t, sq)))) /\ (\A v \in {m__6.v : m__6 \in {m__5 \in net : m__5.tag = "ReadConfirm"}} : (\A t_2 \in {x__4 \in {m__8.term : m__8 \in {m__7 \in net : m__7.tag = "ReadConfirm"}} : (x__4 >= 0)} : (\A sq_2 \in {x__5 \in {m__10.seq : m__10 \in {m__9 \in net : m__9.tag = "ReadConfirm"}} : (x__5 >= 0)} : (([tag |-> "ReadConfirm", v |-> v, term |-> t_2, seq |-> sq_2] \in net) => confirm_msg_ok(v, t_2, sq_2)))))) /\ (\A r \in reads : ((r \in reads) => read_rec_ok(r))))

\* test_crate::inv, @SOURCE@:1367:1: 1367:40 (#0)
inv ==
    (((((((((((inv_wf /\ inv_hosts) /\ inv_msgs) /\ inv_lterms) /\ inv_ack_persist) /\ inv_vote_persist) /\ inv_commits) /\ inv_leader_completeness) /\ inv_commit_msgs) /\ inv_host_commits) /\ inv_commit_leaders) /\ inv_reads)

\* The state's integer fields stay within their types, as in Verus.
TypeOK ==
    /\ (n >= 0)
    /\ (\A i__ \in 1..Len(hosts) : ((hosts[i__].term >= 0) /\ (\A i__2 \in 1..Len(hosts[i__].log) : ((hosts[i__].log[i__2].term >= 0) /\ (hosts[i__].log[i__2].cmd.tag = "Some" => (\A i__3 \in 1..Len(hosts[i__].log[i__2].cmd.v0) : (0 <= hosts[i__].log[i__2].cmd.v0[i__3] /\ hosts[i__].log[i__2].cmd.v0[i__3] <= 255))))) /\ (hosts[i__].commit >= 0) /\ (\A k__ \in DOMAIN hosts[i__].vote_logs : (\A i__4 \in 1..Len(hosts[i__].vote_logs[k__]) : ((hosts[i__].vote_logs[k__][i__4].term >= 0) /\ (hosts[i__].vote_logs[k__][i__4].cmd.tag = "Some" => (\A i__5 \in 1..Len(hosts[i__].vote_logs[k__][i__4].cmd.v0) : (0 <= hosts[i__].vote_logs[k__][i__4].cmd.v0[i__5] /\ hosts[i__].vote_logs[k__][i__4].cmd.v0[i__5] <= 255)))))) /\ ((hosts[i__].crec.term >= 0) /\ (hosts[i__].crec.ci >= 0) /\ (\A k__2 \in DOMAIN hosts[i__].crec.q : (hosts[i__].crec.q[k__2] >= 0))) /\ (hosts[i__].read_seq >= 0)))
    /\ (\A e__2 \in net : ((e__2.tag = "Campaign" => ((e__2.term >= 0) /\ (\A i__6 \in 1..Len(e__2.clog) : ((e__2.clog[i__6].term >= 0) /\ (e__2.clog[i__6].cmd.tag = "Some" => (\A i__7 \in 1..Len(e__2.clog[i__6].cmd.v0) : (0 <= e__2.clog[i__6].cmd.v0[i__7] /\ e__2.clog[i__6].cmd.v0[i__7] <= 255))))))) /\ (e__2.tag = "Vote" => ((e__2.term >= 0) /\ (\A i__8 \in 1..Len(e__2.vlog) : ((e__2.vlog[i__8].term >= 0) /\ (e__2.vlog[i__8].cmd.tag = "Some" => (\A i__9 \in 1..Len(e__2.vlog[i__8].cmd.v0) : (0 <= e__2.vlog[i__8].cmd.v0[i__9] /\ e__2.vlog[i__8].cmd.v0[i__9] <= 255))))))) /\ (e__2.tag = "Append" => ((e__2.term >= 0) /\ (e__2.base >= 0) /\ (e__2.bterm >= 0) /\ (\A i__10 \in 1..Len(e__2.entries) : ((e__2.entries[i__10].term >= 0) /\ (e__2.entries[i__10].cmd.tag = "Some" => (\A i__11 \in 1..Len(e__2.entries[i__10].cmd.v0) : (0 <= e__2.entries[i__10].cmd.v0[i__11] /\ e__2.entries[i__10].cmd.v0[i__11] <= 255))))))) /\ (e__2.tag = "Commit" => ((e__2.term >= 0) /\ (e__2.ci >= 0) /\ ((e__2.rec.term >= 0) /\ (e__2.rec.ci >= 0) /\ (\A k__3 \in DOMAIN e__2.rec.q : (e__2.rec.q[k__3] >= 0))))) /\ (e__2.tag = "Ack" => ((e__2.term >= 0) /\ (e__2.mi >= 0))) /\ (e__2.tag = "Read" => ((e__2.term >= 0) /\ (e__2.seq >= 0))) /\ (e__2.tag = "ReadConfirm" => ((e__2.term >= 0) /\ (e__2.seq >= 0)))))
    /\ (\A k__4 \in DOMAIN leader_log : ((k__4 >= 0) /\ (\A i__12 \in 1..Len(leader_log[k__4]) : ((leader_log[k__4][i__12].term >= 0) /\ (leader_log[k__4][i__12].cmd.tag = "Some" => (\A i__13 \in 1..Len(leader_log[k__4][i__12].cmd.v0) : (0 <= leader_log[k__4][i__12].cmd.v0[i__13] /\ leader_log[k__4][i__12].cmd.v0[i__13] <= 255)))))))
    /\ (\A k__5 \in DOMAIN leader_of : (k__5 >= 0))
    /\ (\A k__6 \in DOMAIN voters : (k__6 >= 0))
    /\ (\A k__7 \in DOMAIN elect_log : ((k__7 >= 0) /\ (\A i__14 \in 1..Len(elect_log[k__7]) : ((elect_log[k__7][i__14].term >= 0) /\ (elect_log[k__7][i__14].cmd.tag = "Some" => (\A i__15 \in 1..Len(elect_log[k__7][i__14].cmd.v0) : (0 <= elect_log[k__7][i__14].cmd.v0[i__15] /\ elect_log[k__7][i__14].cmd.v0[i__15] <= 255)))))))
    /\ (\A k__8 \in DOMAIN elect_votes : ((k__8 >= 0) /\ (\A k__9 \in DOMAIN elect_votes[k__8] : (\A i__16 \in 1..Len(elect_votes[k__8][k__9]) : ((elect_votes[k__8][k__9][i__16].term >= 0) /\ (elect_votes[k__8][k__9][i__16].cmd.tag = "Some" => (\A i__17 \in 1..Len(elect_votes[k__8][k__9][i__16].cmd.v0) : (0 <= elect_votes[k__8][k__9][i__16].cmd.v0[i__17] /\ elect_votes[k__8][k__9][i__16].cmd.v0[i__17] <= 255))))))))
    /\ (\A e__4 \in commits : ((e__4.term >= 0) /\ (e__4.ci >= 0) /\ (\A k__10 \in DOMAIN e__4.q : (e__4.q[k__10] >= 0))))
    /\ (\A e__5 \in reads : ((e__5.term >= 0) /\ (e__5.seq >= 0) /\ (\A e__6 \in e__5.born : ((e__6.term >= 0) /\ (e__6.ci >= 0) /\ (\A k__11 \in DOMAIN e__6.q : (e__6.q[k__11] >= 0))))))
    /\ (\A k__12 \in DOMAIN read_hwm : ((k__12 >= 0) /\ (read_hwm[k__12] >= 0)))
Init == init /\ TypeOK
Next == next /\ TypeOK'
Spec == Init /\ [][Next]_vars
Inv == (inv)
==============================
