---- MODULE GState_tla_trace ----
\* Trace validation for GState_tla, the export of `test_crate` (verus -V tla-export).
\* The log is newline-delimited JSON: a header line naming the module
\* ({"module": "GState_tla", "export": "test_crate"}, optionally "state": the
\* observed initial state; another module or export stops TLC), then one line per step:
\* {"step": "<t_* name>", "params": {...}, "state": {...}}. A step is named by
\* its spec fn's last segment or full path, by the full path alone when two
\* steps share the last segment; a parameter the step does not declare stops
\* TLC. Values are in the export's encoding: a struct or enum value is an
\* object (an enum's with its "tag"), a Seq an array, a Set an array of its
\* elements, a Map an array of [key, value] pairs, a tuple an array, a struct
\* without fields {} (or {"tag": "unit"}). An object
\* observed in the state is partial: only the fields it names are compared, so
\* a ghost field is left out of the log and free in the model (an enum's tag
\* too: its fields are then compared under whichever variant the model has);
\* a key naming no field of its type stops TLC, as one naming no state field
\* does; a Seq may be observed partially as an object keyed by the Verus index
\* ("0", "1", ...; {} observes nothing, [] is the empty Seq; a key
\* that is no index stops TLC). A key a line or the header does not define
\* stops TLC, so a misspelled "state" or "params" never observes nothing.
\* A record inside a Set element, a Map key or a parameter is decoded whole,
\* so it must name every field and an enum its tag (one left out there stops
\* TLC). A parameter left out of "params" ranges over what Next's calls to
\* the step pass it (the bound of the quantifier binding the argument, or the
\* field of a value matched against a pattern, such as a VerusSync step's
\* Dom_Step_<t>_v<i>), else its type's finite domain (not a Dom_<Type> hole,
\* which holds only what a quantifier binds, never a value a call computes);
\* with neither it must be logged, and TraceEnabled leaves the step out (the
\* report's trace steps say which, "enumerated"). A logged parameter outside
\* its domain is a step the model cannot take.
\* TraceNext selects the logged existential arm and its logged parameters.
\* Missing parameters retain their original domains; dispatch guards and
\* TypeOK are preserved. General relations retain their enclosing Next check
\* (listed in trace.general_relation_steps). Unknown names fall back to Next,
\* checking only the observed state sequence (trace.unknown_step).
\* A trace conforms when it reaches TraceAccepted; otherwise the deepest trace_i
\* is the first unexplained step; when TLC finds no initial state (0 states generated, depth 0),
\* the header is rejected.
\* A pass means the observed state sequence is a behaviour of the model.
EXTENDS GState_tla, Json, TLC, Integers, Sequences

CONSTANT TraceLog  \* the log's path
VARIABLE trace_i  \* the next logged step to take

TraceLines == ndJsonDeserialize(TraceLog)
TraceHeader == TraceLines[1]
Trace == SubSeq(TraceLines, 2, Len(TraceLines))

\* Whether a JSON value is an array (TLC holds it as a tuple).
TraceIsArray(j_2) == SubSeq(ToString(j_2), 1, 2) = "<<"
TraceStateOf(e_2) == IF "state" \in DOMAIN e_2 THEN e_2.state ELSE [k_2 \in {} |-> 0]
\* A logged parameter, or the domain it ranges over when left out. The domain
\* holds every value Next passes it, so a logged value outside it is a step
\* the model cannot take.
TraceParam(e_2, k_2, Dec(_), D) ==
    IF "params" \in DOMAIN e_2 /\ k_2 \in DOMAIN e_2.params THEN {Dec(e_2.params[k_2])} \cap D ELSE D
\* The same for a parameter with no domain, which must be logged.
TraceParamUnbounded(e_2, k_2, Dec(_), D) ==
    IF "params" \in DOMAIN e_2 /\ k_2 \in DOMAIN e_2.params THEN {Dec(e_2.params[k_2])} ELSE D
\* Every parameter logged is one of S, the step's declared parameters (an IF,
\* not a disjunction, which TLC would take as two branches of the action).
TraceParamsDeclared(e_2, S) ==
    "params" \in DOMAIN e_2 =>
        \A k_2 \in DOMAIN e_2.params :
            IF k_2 \in S THEN TRUE
            ELSE Assert(FALSE, "trace: " \o e_2.step \o " has no parameter " \o k_2)

\* Every key of a log line is one of S, so a misspelled "state" or
\* "params" stops TLC rather than observing nothing.
TraceKeys(e_2, S, j_2) ==
    \A k_2 \in DOMAIN e_2 :
        IF k_2 \in S THEN TRUE
        ELSE Assert(FALSE, "trace: " \o j_2 \o " has no key " \o k_2)

RECURSIVE TraceDec_AEntry(_), TraceDec_CommitRec(_), TraceDec_MHost(_), TraceDec_MRole(_), TraceDec_Map_int_Seq_AEntry(_), TraceDec_Map_int_nat(_), TraceDec_Map_nat_Map_int_Seq_AEntry(_), TraceDec_Map_nat_Seq_AEntry(_), TraceDec_Map_nat_Set_int(_), TraceDec_Map_nat_int(_), TraceDec_Map_nat_nat(_), TraceDec_Msg(_), TraceDec_Option_Seq_u8(_), TraceDec_Option_int(_), TraceDec_ReadRec(_), TraceDec_Seq_AEntry(_), TraceDec_Seq_MHost(_), TraceDec_Seq_u8(_), TraceDec_Set_CommitRec(_), TraceDec_Set_Msg(_), TraceDec_Set_ReadRec(_), TraceDec_Set_int(_), TraceDec_TStep(_), TraceDec_int(_), TraceDec_nat(_), TraceDec_u8(_), TraceObs_AEntry(_, _), TraceObs_CommitRec(_, _), TraceObs_MHost(_, _), TraceObs_MRole(_, _), TraceObs_Map_int_Seq_AEntry(_, _), TraceObs_Map_int_nat(_, _), TraceObs_Map_nat_Map_int_Seq_AEntry(_, _), TraceObs_Map_nat_Seq_AEntry(_, _), TraceObs_Map_nat_Set_int(_, _), TraceObs_Map_nat_int(_, _), TraceObs_Map_nat_nat(_, _), TraceObs_Msg(_, _), TraceObs_Option_Seq_u8(_, _), TraceObs_Option_int(_, _), TraceObs_ReadRec(_, _), TraceObs_Seq_AEntry(_, _), TraceObs_Seq_MHost(_, _), TraceObs_Seq_u8(_, _), TraceObs_Set_CommitRec(_, _), TraceObs_Set_Msg(_, _), TraceObs_Set_ReadRec(_, _), TraceObs_Set_int(_, _), TraceObs_TStep(_, _), TraceObs_int(_, _), TraceObs_nat(_, _), TraceObs_u8(_, _)

\* nat
TraceDec_nat(j_2) ==
    j_2
TraceObs_nat(v_4, j_2) ==
    v_4 = j_2

\* int
TraceDec_int(j_2) ==
    j_2
TraceObs_int(v_4, j_2) ==
    v_4 = j_2

\* Option_int
TraceDec_Option_int(j_2) ==
    IF "tag" \in DOMAIN j_2
    THEN CASE j_2.tag = "None" -> [tag |-> "None"]
           [] j_2.tag = "Some" -> [tag |-> "Some", v0 |-> TraceDec_int(j_2.v0)]
           [] OTHER -> Assert(FALSE, "trace: Option_int has no variant " \o ToString(j_2.tag))
    ELSE Assert(FALSE, "trace: a Option_int value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Option_int(v_4, j_2) ==
    (IF "tag" \in DOMAIN j_2 THEN v_4.tag = j_2.tag ELSE TRUE) /\ \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE v_4.tag = "Some" /\ k_2 = "v0" -> TraceObs_int(v_4.v0, j_2[k_2])
          [] OTHER -> IF k_2 \in {"v0"} THEN FALSE ELSE Assert(FALSE, "trace: Option_int has no field " \o k_2)

\* MRole
TraceDec_MRole(j_2) ==
    IF "tag" \in DOMAIN j_2
    THEN CASE j_2.tag = "Follower" -> [tag |-> "Follower"]
           [] j_2.tag = "Candidate" -> [tag |-> "Candidate"]
           [] j_2.tag = "Leader" -> [tag |-> "Leader"]
           [] OTHER -> Assert(FALSE, "trace: MRole has no variant " \o ToString(j_2.tag))
    ELSE Assert(FALSE, "trace: a MRole value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_MRole(v_4, j_2) ==
    (IF "tag" \in DOMAIN j_2 THEN v_4.tag = j_2.tag ELSE TRUE) /\ \A k_2 \in DOMAIN j_2 \ {"tag"} :
        Assert(FALSE, "trace: MRole has no field " \o k_2)

\* u8
TraceDec_u8(j_2) ==
    j_2
TraceObs_u8(v_4, j_2) ==
    v_4 = j_2

\* Seq_u8
TraceDec_Seq_u8(j_2) ==
    [p \in 1..Len(j_2) |-> TraceDec_u8(j_2[p])]
TraceObs_Seq_u8(v_4, j_2) ==
    IF TraceIsArray(j_2)
    THEN Len(v_4) = Len(j_2) /\ \A p \in 1..Len(j_2) : TraceObs_u8(v_4[p], j_2[p])
    ELSE \A k_2 \in DOMAIN j_2 :
        IF Len(k_2) > 0 /\ \A p \in 1..Len(k_2) : SubSeq(k_2, p, p) \in {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"}
        THEN \E p \in 1..Len(v_4) : ToString(p - 1) = k_2 /\ TraceObs_u8(v_4[p], j_2[k_2])
        ELSE Assert(FALSE, "trace: a Seq_u8 observed as an object has a key that is no index: " \o k_2)

\* Option_Seq_u8
TraceDec_Option_Seq_u8(j_2) ==
    IF "tag" \in DOMAIN j_2
    THEN CASE j_2.tag = "None" -> [tag |-> "None"]
           [] j_2.tag = "Some" -> [tag |-> "Some", v0 |-> TraceDec_Seq_u8(j_2.v0)]
           [] OTHER -> Assert(FALSE, "trace: Option_Seq_u8 has no variant " \o ToString(j_2.tag))
    ELSE Assert(FALSE, "trace: a Option_Seq_u8 value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Option_Seq_u8(v_4, j_2) ==
    (IF "tag" \in DOMAIN j_2 THEN v_4.tag = j_2.tag ELSE TRUE) /\ \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE v_4.tag = "Some" /\ k_2 = "v0" -> TraceObs_Seq_u8(v_4.v0, j_2[k_2])
          [] OTHER -> IF k_2 \in {"v0"} THEN FALSE ELSE Assert(FALSE, "trace: Option_Seq_u8 has no field " \o k_2)

\* AEntry
TraceDec_AEntry(j_2) ==
    [term |-> TraceDec_nat(j_2.term), cmd |-> TraceDec_Option_Seq_u8(j_2.cmd)]
TraceObs_AEntry(v_4, j_2) ==
    \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] k_2 = "cmd" -> TraceObs_Option_Seq_u8(v_4.cmd, j_2[k_2])
          [] OTHER -> Assert(FALSE, "trace: AEntry has no field " \o k_2)

\* Seq_AEntry
TraceDec_Seq_AEntry(j_2) ==
    [p \in 1..Len(j_2) |-> TraceDec_AEntry(j_2[p])]
TraceObs_Seq_AEntry(v_4, j_2) ==
    IF TraceIsArray(j_2)
    THEN Len(v_4) = Len(j_2) /\ \A p \in 1..Len(j_2) : TraceObs_AEntry(v_4[p], j_2[p])
    ELSE \A k_2 \in DOMAIN j_2 :
        IF Len(k_2) > 0 /\ \A p \in 1..Len(k_2) : SubSeq(k_2, p, p) \in {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"}
        THEN \E p \in 1..Len(v_4) : ToString(p - 1) = k_2 /\ TraceObs_AEntry(v_4[p], j_2[k_2])
        ELSE Assert(FALSE, "trace: a Seq_AEntry observed as an object has a key that is no index: " \o k_2)

\* Set_int
TraceDec_Set_int(j_2) ==
    {TraceDec_int(j_2[p]) : p \in 1..Len(j_2)}
TraceObs_Set_int(v_4, j_2) ==
    v_4 = TraceDec_Set_int(j_2)

\* Map_int_Seq_AEntry
TraceDec_Map_int_Seq_AEntry(j_2) ==
    [k_2 \in {TraceDec_int(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_Seq_AEntry(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_int(j_2[p][1]) = k_2][2])]
TraceObs_Map_int_Seq_AEntry(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_int(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_Seq_AEntry(v_4[TraceDec_int(j_2[p][1])], j_2[p][2])

\* Map_int_nat
TraceDec_Map_int_nat(j_2) ==
    [k_2 \in {TraceDec_int(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_nat(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_int(j_2[p][1]) = k_2][2])]
TraceObs_Map_int_nat(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_int(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_nat(v_4[TraceDec_int(j_2[p][1])], j_2[p][2])

\* CommitRec
TraceDec_CommitRec(j_2) ==
    [term |-> TraceDec_nat(j_2.term), ci |-> TraceDec_nat(j_2.ci), q |-> TraceDec_Map_int_nat(j_2.q)]
TraceObs_CommitRec(v_4, j_2) ==
    \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] k_2 = "ci" -> TraceObs_nat(v_4.ci, j_2[k_2])
          [] k_2 = "q" -> TraceObs_Map_int_nat(v_4.q, j_2[k_2])
          [] OTHER -> Assert(FALSE, "trace: CommitRec has no field " \o k_2)

\* MHost
TraceDec_MHost(j_2) ==
    [term |-> TraceDec_nat(j_2.term), vote |-> TraceDec_Option_int(j_2.vote), role |-> TraceDec_MRole(j_2.role), log |-> TraceDec_Seq_AEntry(j_2.log), commit |-> TraceDec_nat(j_2.commit), votes |-> TraceDec_Set_int(j_2.votes), vote_logs |-> TraceDec_Map_int_Seq_AEntry(j_2.vote_logs), crec |-> TraceDec_CommitRec(j_2.crec), read_seq |-> TraceDec_nat(j_2.read_seq)]
TraceObs_MHost(v_4, j_2) ==
    \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] k_2 = "vote" -> TraceObs_Option_int(v_4.vote, j_2[k_2])
          [] k_2 = "role" -> TraceObs_MRole(v_4.role, j_2[k_2])
          [] k_2 = "log" -> TraceObs_Seq_AEntry(v_4.log, j_2[k_2])
          [] k_2 = "commit" -> TraceObs_nat(v_4.commit, j_2[k_2])
          [] k_2 = "votes" -> TraceObs_Set_int(v_4.votes, j_2[k_2])
          [] k_2 = "vote_logs" -> TraceObs_Map_int_Seq_AEntry(v_4.vote_logs, j_2[k_2])
          [] k_2 = "crec" -> TraceObs_CommitRec(v_4.crec, j_2[k_2])
          [] k_2 = "read_seq" -> TraceObs_nat(v_4.read_seq, j_2[k_2])
          [] OTHER -> Assert(FALSE, "trace: MHost has no field " \o k_2)

\* Seq_MHost
TraceDec_Seq_MHost(j_2) ==
    [p \in 1..Len(j_2) |-> TraceDec_MHost(j_2[p])]
TraceObs_Seq_MHost(v_4, j_2) ==
    IF TraceIsArray(j_2)
    THEN Len(v_4) = Len(j_2) /\ \A p \in 1..Len(j_2) : TraceObs_MHost(v_4[p], j_2[p])
    ELSE \A k_2 \in DOMAIN j_2 :
        IF Len(k_2) > 0 /\ \A p \in 1..Len(k_2) : SubSeq(k_2, p, p) \in {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"}
        THEN \E p \in 1..Len(v_4) : ToString(p - 1) = k_2 /\ TraceObs_MHost(v_4[p], j_2[k_2])
        ELSE Assert(FALSE, "trace: a Seq_MHost observed as an object has a key that is no index: " \o k_2)

\* Msg
TraceDec_Msg(j_2) ==
    IF "tag" \in DOMAIN j_2
    THEN CASE j_2.tag = "Campaign" -> [tag |-> "Campaign", c |-> TraceDec_int(j_2.c), term |-> TraceDec_nat(j_2.term), clog |-> TraceDec_Seq_AEntry(j_2.clog)]
           [] j_2.tag = "Vote" -> [tag |-> "Vote", v |-> TraceDec_int(j_2.v), c |-> TraceDec_int(j_2.c), term |-> TraceDec_nat(j_2.term), vlog |-> TraceDec_Seq_AEntry(j_2.vlog)]
           [] j_2.tag = "Append" -> [tag |-> "Append", term |-> TraceDec_nat(j_2.term), base |-> TraceDec_nat(j_2.base), bterm |-> TraceDec_nat(j_2.bterm), entries |-> TraceDec_Seq_AEntry(j_2.entries)]
           [] j_2.tag = "Commit" -> [tag |-> "Commit", term |-> TraceDec_nat(j_2.term), ci |-> TraceDec_nat(j_2.ci), rec |-> TraceDec_CommitRec(j_2.rec)]
           [] j_2.tag = "Ack" -> [tag |-> "Ack", v |-> TraceDec_int(j_2.v), term |-> TraceDec_nat(j_2.term), mi |-> TraceDec_nat(j_2.mi)]
           [] j_2.tag = "Read" -> [tag |-> "Read", term |-> TraceDec_nat(j_2.term), seq |-> TraceDec_nat(j_2.seq)]
           [] j_2.tag = "ReadConfirm" -> [tag |-> "ReadConfirm", v |-> TraceDec_int(j_2.v), term |-> TraceDec_nat(j_2.term), seq |-> TraceDec_nat(j_2.seq)]
           [] OTHER -> Assert(FALSE, "trace: Msg has no variant " \o ToString(j_2.tag))
    ELSE Assert(FALSE, "trace: a Msg value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Msg(v_4, j_2) ==
    (IF "tag" \in DOMAIN j_2 THEN v_4.tag = j_2.tag ELSE TRUE) /\ \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE v_4.tag = "Campaign" /\ k_2 = "c" -> TraceObs_int(v_4.c, j_2[k_2])
          [] v_4.tag = "Campaign" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Campaign" /\ k_2 = "clog" -> TraceObs_Seq_AEntry(v_4.clog, j_2[k_2])
          [] v_4.tag = "Vote" /\ k_2 = "v" -> TraceObs_int(v_4.v, j_2[k_2])
          [] v_4.tag = "Vote" /\ k_2 = "c" -> TraceObs_int(v_4.c, j_2[k_2])
          [] v_4.tag = "Vote" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Vote" /\ k_2 = "vlog" -> TraceObs_Seq_AEntry(v_4.vlog, j_2[k_2])
          [] v_4.tag = "Append" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Append" /\ k_2 = "base" -> TraceObs_nat(v_4.base, j_2[k_2])
          [] v_4.tag = "Append" /\ k_2 = "bterm" -> TraceObs_nat(v_4.bterm, j_2[k_2])
          [] v_4.tag = "Append" /\ k_2 = "entries" -> TraceObs_Seq_AEntry(v_4.entries, j_2[k_2])
          [] v_4.tag = "Commit" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Commit" /\ k_2 = "ci" -> TraceObs_nat(v_4.ci, j_2[k_2])
          [] v_4.tag = "Commit" /\ k_2 = "rec" -> TraceObs_CommitRec(v_4.rec, j_2[k_2])
          [] v_4.tag = "Ack" /\ k_2 = "v" -> TraceObs_int(v_4.v, j_2[k_2])
          [] v_4.tag = "Ack" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Ack" /\ k_2 = "mi" -> TraceObs_nat(v_4.mi, j_2[k_2])
          [] v_4.tag = "Read" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Read" /\ k_2 = "seq" -> TraceObs_nat(v_4.seq, j_2[k_2])
          [] v_4.tag = "ReadConfirm" /\ k_2 = "v" -> TraceObs_int(v_4.v, j_2[k_2])
          [] v_4.tag = "ReadConfirm" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "ReadConfirm" /\ k_2 = "seq" -> TraceObs_nat(v_4.seq, j_2[k_2])
          [] OTHER -> IF k_2 \in {"c", "term", "clog", "v", "vlog", "base", "bterm", "entries", "ci", "rec", "mi", "seq"} THEN FALSE ELSE Assert(FALSE, "trace: Msg has no field " \o k_2)

\* Set_Msg
TraceDec_Set_Msg(j_2) ==
    {TraceDec_Msg(j_2[p]) : p \in 1..Len(j_2)}
TraceObs_Set_Msg(v_4, j_2) ==
    v_4 = TraceDec_Set_Msg(j_2)

\* Map_nat_Seq_AEntry
TraceDec_Map_nat_Seq_AEntry(j_2) ==
    [k_2 \in {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_Seq_AEntry(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_nat(j_2[p][1]) = k_2][2])]
TraceObs_Map_nat_Seq_AEntry(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_Seq_AEntry(v_4[TraceDec_nat(j_2[p][1])], j_2[p][2])

\* Map_nat_int
TraceDec_Map_nat_int(j_2) ==
    [k_2 \in {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_int(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_nat(j_2[p][1]) = k_2][2])]
TraceObs_Map_nat_int(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_int(v_4[TraceDec_nat(j_2[p][1])], j_2[p][2])

\* Map_nat_Set_int
TraceDec_Map_nat_Set_int(j_2) ==
    [k_2 \in {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_Set_int(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_nat(j_2[p][1]) = k_2][2])]
TraceObs_Map_nat_Set_int(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_Set_int(v_4[TraceDec_nat(j_2[p][1])], j_2[p][2])

\* Map_nat_Map_int_Seq_AEntry
TraceDec_Map_nat_Map_int_Seq_AEntry(j_2) ==
    [k_2 \in {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_Map_int_Seq_AEntry(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_nat(j_2[p][1]) = k_2][2])]
TraceObs_Map_nat_Map_int_Seq_AEntry(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_Map_int_Seq_AEntry(v_4[TraceDec_nat(j_2[p][1])], j_2[p][2])

\* Set_CommitRec
TraceDec_Set_CommitRec(j_2) ==
    {TraceDec_CommitRec(j_2[p]) : p \in 1..Len(j_2)}
TraceObs_Set_CommitRec(v_4, j_2) ==
    v_4 = TraceDec_Set_CommitRec(j_2)

\* ReadRec
TraceDec_ReadRec(j_2) ==
    [term |-> TraceDec_nat(j_2.term), seq |-> TraceDec_nat(j_2.seq), born |-> TraceDec_Set_CommitRec(j_2.born)]
TraceObs_ReadRec(v_4, j_2) ==
    \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] k_2 = "seq" -> TraceObs_nat(v_4.seq, j_2[k_2])
          [] k_2 = "born" -> TraceObs_Set_CommitRec(v_4.born, j_2[k_2])
          [] OTHER -> Assert(FALSE, "trace: ReadRec has no field " \o k_2)

\* Set_ReadRec
TraceDec_Set_ReadRec(j_2) ==
    {TraceDec_ReadRec(j_2[p]) : p \in 1..Len(j_2)}
TraceObs_Set_ReadRec(v_4, j_2) ==
    v_4 = TraceDec_Set_ReadRec(j_2)

\* Map_nat_nat
TraceDec_Map_nat_nat(j_2) ==
    [k_2 \in {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} |-> TraceDec_nat(j_2[CHOOSE p \in 1..Len(j_2) : TraceDec_nat(j_2[p][1]) = k_2][2])]
TraceObs_Map_nat_nat(v_4, j_2) ==
    DOMAIN v_4 = {TraceDec_nat(j_2[p][1]) : p \in 1..Len(j_2)} /\ \A p \in 1..Len(j_2) : TraceObs_nat(v_4[TraceDec_nat(j_2[p][1])], j_2[p][2])

\* TStep
TraceDec_TStep(j_2) ==
    IF "tag" \in DOMAIN j_2
    THEN CASE j_2.tag = "Campaign" -> [tag |-> "Campaign", i |-> TraceDec_int(j_2.i)]
           [] j_2.tag = "Grant" -> [tag |-> "Grant", v |-> TraceDec_int(j_2.v), c |-> TraceDec_int(j_2.c), term |-> TraceDec_nat(j_2.term), clog |-> TraceDec_Seq_AEntry(j_2.clog)]
           [] j_2.tag = "CollectVote" -> [tag |-> "CollectVote", i |-> TraceDec_int(j_2.i), v |-> TraceDec_int(j_2.v), vlog |-> TraceDec_Seq_AEntry(j_2.vlog)]
           [] j_2.tag = "BecomeLeader" -> [tag |-> "BecomeLeader", i |-> TraceDec_int(j_2.i)]
           [] j_2.tag = "Propose" -> [tag |-> "Propose", i |-> TraceDec_int(j_2.i), cmd |-> TraceDec_Option_Seq_u8(j_2.cmd)]
           [] j_2.tag = "SendAppend" -> [tag |-> "SendAppend", i |-> TraceDec_int(j_2.i), b |-> TraceDec_nat(j_2.b), e |-> TraceDec_nat(j_2.e)]
           [] j_2.tag = "RecvAppend" -> [tag |-> "RecvAppend", i |-> TraceDec_int(j_2.i), term |-> TraceDec_nat(j_2.term), base |-> TraceDec_nat(j_2.base), bterm |-> TraceDec_nat(j_2.bterm), entries |-> TraceDec_Seq_AEntry(j_2.entries)]
           [] j_2.tag = "SendAck" -> [tag |-> "SendAck", i |-> TraceDec_int(j_2.i), mi |-> TraceDec_nat(j_2.mi)]
           [] j_2.tag = "LeaderCommit" -> [tag |-> "LeaderCommit", i |-> TraceDec_int(j_2.i), ci |-> TraceDec_nat(j_2.ci), q |-> TraceDec_Map_int_nat(j_2.q)]
           [] j_2.tag = "SendCommit" -> [tag |-> "SendCommit", i |-> TraceDec_int(j_2.i), ci |-> TraceDec_nat(j_2.ci)]
           [] j_2.tag = "RecvCommit" -> [tag |-> "RecvCommit", i |-> TraceDec_int(j_2.i), ci |-> TraceDec_nat(j_2.ci), mi |-> TraceDec_nat(j_2.mi), rec |-> TraceDec_CommitRec(j_2.rec)]
           [] j_2.tag = "BumpTerm" -> [tag |-> "BumpTerm", i |-> TraceDec_int(j_2.i), term |-> TraceDec_nat(j_2.term)]
           [] j_2.tag = "StepDown" -> [tag |-> "StepDown", i |-> TraceDec_int(j_2.i)]
           [] j_2.tag = "Restart" -> [tag |-> "Restart", i |-> TraceDec_int(j_2.i), commit |-> TraceDec_nat(j_2.commit)]
           [] j_2.tag = "SubmitRead" -> [tag |-> "SubmitRead", i |-> TraceDec_int(j_2.i)]
           [] j_2.tag = "ConfirmRead" -> [tag |-> "ConfirmRead", i |-> TraceDec_int(j_2.i), term |-> TraceDec_nat(j_2.term), seq |-> TraceDec_nat(j_2.seq)]
           [] OTHER -> Assert(FALSE, "trace: TStep has no variant " \o ToString(j_2.tag))
    ELSE Assert(FALSE, "trace: a TStep value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_TStep(v_4, j_2) ==
    (IF "tag" \in DOMAIN j_2 THEN v_4.tag = j_2.tag ELSE TRUE) /\ \A k_2 \in DOMAIN j_2 \ {"tag"} :
        CASE v_4.tag = "Campaign" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "Grant" /\ k_2 = "v" -> TraceObs_int(v_4.v, j_2[k_2])
          [] v_4.tag = "Grant" /\ k_2 = "c" -> TraceObs_int(v_4.c, j_2[k_2])
          [] v_4.tag = "Grant" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "Grant" /\ k_2 = "clog" -> TraceObs_Seq_AEntry(v_4.clog, j_2[k_2])
          [] v_4.tag = "CollectVote" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "CollectVote" /\ k_2 = "v" -> TraceObs_int(v_4.v, j_2[k_2])
          [] v_4.tag = "CollectVote" /\ k_2 = "vlog" -> TraceObs_Seq_AEntry(v_4.vlog, j_2[k_2])
          [] v_4.tag = "BecomeLeader" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "Propose" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "Propose" /\ k_2 = "cmd" -> TraceObs_Option_Seq_u8(v_4.cmd, j_2[k_2])
          [] v_4.tag = "SendAppend" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "SendAppend" /\ k_2 = "b" -> TraceObs_nat(v_4.b, j_2[k_2])
          [] v_4.tag = "SendAppend" /\ k_2 = "e" -> TraceObs_nat(v_4.e, j_2[k_2])
          [] v_4.tag = "RecvAppend" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "RecvAppend" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "RecvAppend" /\ k_2 = "base" -> TraceObs_nat(v_4.base, j_2[k_2])
          [] v_4.tag = "RecvAppend" /\ k_2 = "bterm" -> TraceObs_nat(v_4.bterm, j_2[k_2])
          [] v_4.tag = "RecvAppend" /\ k_2 = "entries" -> TraceObs_Seq_AEntry(v_4.entries, j_2[k_2])
          [] v_4.tag = "SendAck" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "SendAck" /\ k_2 = "mi" -> TraceObs_nat(v_4.mi, j_2[k_2])
          [] v_4.tag = "LeaderCommit" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "LeaderCommit" /\ k_2 = "ci" -> TraceObs_nat(v_4.ci, j_2[k_2])
          [] v_4.tag = "LeaderCommit" /\ k_2 = "q" -> TraceObs_Map_int_nat(v_4.q, j_2[k_2])
          [] v_4.tag = "SendCommit" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "SendCommit" /\ k_2 = "ci" -> TraceObs_nat(v_4.ci, j_2[k_2])
          [] v_4.tag = "RecvCommit" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "RecvCommit" /\ k_2 = "ci" -> TraceObs_nat(v_4.ci, j_2[k_2])
          [] v_4.tag = "RecvCommit" /\ k_2 = "mi" -> TraceObs_nat(v_4.mi, j_2[k_2])
          [] v_4.tag = "RecvCommit" /\ k_2 = "rec" -> TraceObs_CommitRec(v_4.rec, j_2[k_2])
          [] v_4.tag = "BumpTerm" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "BumpTerm" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "StepDown" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "Restart" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "Restart" /\ k_2 = "commit" -> TraceObs_nat(v_4.commit, j_2[k_2])
          [] v_4.tag = "SubmitRead" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "ConfirmRead" /\ k_2 = "i" -> TraceObs_int(v_4.i, j_2[k_2])
          [] v_4.tag = "ConfirmRead" /\ k_2 = "term" -> TraceObs_nat(v_4.term, j_2[k_2])
          [] v_4.tag = "ConfirmRead" /\ k_2 = "seq" -> TraceObs_nat(v_4.seq, j_2[k_2])
          [] OTHER -> IF k_2 \in {"i", "v", "c", "term", "clog", "vlog", "cmd", "b", "e", "base", "bterm", "entries", "mi", "ci", "q", "rec", "commit", "seq"} THEN FALSE ELSE Assert(FALSE, "trace: TStep has no field " \o k_2)

TraceObservedKey(k_2, j_2) ==
    CASE k_2 = "n" -> TraceObs_nat(n, j_2)
      [] k_2 = "hosts" -> TraceObs_Seq_MHost(hosts, j_2)
      [] k_2 = "net" -> TraceObs_Set_Msg(net, j_2)
      [] k_2 = "leader_log" -> TraceObs_Map_nat_Seq_AEntry(leader_log, j_2)
      [] k_2 = "leader_of" -> TraceObs_Map_nat_int(leader_of, j_2)
      [] k_2 = "voters" -> TraceObs_Map_nat_Set_int(voters, j_2)
      [] k_2 = "elect_log" -> TraceObs_Map_nat_Seq_AEntry(elect_log, j_2)
      [] k_2 = "elect_votes" -> TraceObs_Map_nat_Map_int_Seq_AEntry(elect_votes, j_2)
      [] k_2 = "commits" -> TraceObs_Set_CommitRec(commits, j_2)
      [] k_2 = "reads" -> TraceObs_Set_ReadRec(reads, j_2)
      [] k_2 = "read_hwm" -> TraceObs_Map_nat_nat(read_hwm, j_2)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k_2)
TraceObserved(j_2) == \A k_2 \in DOMAIN j_2 : TraceObservedKey(k_2, j_2[k_2])
\* The same of the next state: its variables primed, never the log's index.
TraceObservedKeyNext(k_2, j_2) ==
    CASE k_2 = "n" -> TraceObs_nat(n', j_2)
      [] k_2 = "hosts" -> TraceObs_Seq_MHost(hosts', j_2)
      [] k_2 = "net" -> TraceObs_Set_Msg(net', j_2)
      [] k_2 = "leader_log" -> TraceObs_Map_nat_Seq_AEntry(leader_log', j_2)
      [] k_2 = "leader_of" -> TraceObs_Map_nat_int(leader_of', j_2)
      [] k_2 = "voters" -> TraceObs_Map_nat_Set_int(voters', j_2)
      [] k_2 = "elect_log" -> TraceObs_Map_nat_Seq_AEntry(elect_log', j_2)
      [] k_2 = "elect_votes" -> TraceObs_Map_nat_Map_int_Seq_AEntry(elect_votes', j_2)
      [] k_2 = "commits" -> TraceObs_Set_CommitRec(commits', j_2)
      [] k_2 = "reads" -> TraceObs_Set_ReadRec(reads', j_2)
      [] k_2 = "read_hwm" -> TraceObs_Map_nat_nat(read_hwm', j_2)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k_2)
TraceObservedNext(j_2) == \A k_2 \in DOMAIN j_2 : TraceObservedKeyNext(k_2, j_2[k_2])

TraceIdentity(j_2) == j_2
TraceArm_t_become_leader(e_2, trace_decode_0(_)) == TraceParamsDeclared(e_2, {"i"}) /\ ((\E i__3 \in TraceParam(e_2, "i", trace_decode_0, 0..(n) - 1) : (LET step == [tag |-> "BecomeLeader", i |-> i__3] IN next_step(step)))) /\ TypeOK'
TraceArm_t_bump_term(e_2, trace_decode_0_2(_), trace_decode_1(_)) == TraceParamsDeclared(e_2, {"i", "t"}) /\ ((\E i__11 \in TraceParam(e_2, "i", trace_decode_0_2, 0..(n) - 1) : (\E term__3 \in TraceParam(e_2, "t", trace_decode_1, Dom_TStep_BumpTerm_term) : (LET step == [tag |-> "BumpTerm", i |-> i__11, term |-> term__3] IN next_step(step))))) /\ TypeOK'
TraceArm_t_campaign(e_2, trace_decode_0_3(_)) == TraceParamsDeclared(e_2, {"i"}) /\ ((\E i__ \in TraceParam(e_2, "i", trace_decode_0_3, 0..(n) - 1) : (LET step == [tag |-> "Campaign", i |-> i__] IN next_step(step)))) /\ TypeOK'
TraceArm_t_propose(e_2, trace_decode_0_4(_), trace_decode_1_2(_)) == TraceParamsDeclared(e_2, {"i", "cmd"}) /\ ((\E i__4 \in TraceParam(e_2, "i", trace_decode_0_4, 0..(n) - 1) : (\E cmd__ \in TraceParam(e_2, "cmd", trace_decode_1_2, ({[tag |-> "None"]} \cup {[tag |-> "Some", v0 |-> v0__] : v0__ \in Dom_Option_Seq_u8_Some_v0})) : (LET step == [tag |-> "Propose", i |-> i__4, cmd |-> cmd__] IN next_step(step))))) /\ TypeOK'
TraceArm_t_step_down(e_2, trace_decode_0_5(_)) == TraceParamsDeclared(e_2, {"i"}) /\ ((\E i__12 \in TraceParam(e_2, "i", trace_decode_0_5, 0..(n) - 1) : (LET step == [tag |-> "StepDown", i |-> i__12] IN next_step(step)))) /\ TypeOK'
TraceArm_t_submit_read(e_2, trace_decode_0_6(_)) == TraceParamsDeclared(e_2, {"i"}) /\ ((\E i__14 \in TraceParam(e_2, "i", trace_decode_0_6, 0..(n) - 1) : (LET step == [tag |-> "SubmitRead", i |-> i__14] IN next_step(step)))) /\ TypeOK'
TraceStep(e_2) ==
    CASE e_2.step \in {"next_step", "test_crate::next_step"} -> Next /\ TraceParamsDeclared(e_2, {"step"}) /\ Assert(FALSE, "trace: next_step cannot be checked independently because its domain requires caller guards; log next instead")
      [] e_2.step \in {"t_become_leader", "test_crate::t_become_leader"} -> TraceArm_t_become_leader(e_2, TraceDec_int)
      [] e_2.step \in {"t_bump_term", "test_crate::t_bump_term"} -> TraceArm_t_bump_term(e_2, TraceDec_int, TraceDec_nat)
      [] e_2.step \in {"t_campaign", "test_crate::t_campaign"} -> TraceArm_t_campaign(e_2, TraceDec_int)
      [] e_2.step \in {"t_collect_vote", "test_crate::t_collect_vote"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "v", "vlog"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_collect_vote leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "v", TraceDec_int, Assert(FALSE, "trace: t_collect_vote leaves out its parameter v, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a3_ \in TraceParamUnbounded(e_2, "vlog", TraceDec_Seq_AEntry, Assert(FALSE, "trace: t_collect_vote leaves out its parameter vlog, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_collect_vote(a1_, a2_, a3_)
      [] e_2.step \in {"t_confirm_read", "test_crate::t_confirm_read"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "t", "s"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_confirm_read leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "t", TraceDec_nat, Assert(FALSE, "trace: t_confirm_read leaves out its parameter t, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a3_ \in TraceParamUnbounded(e_2, "s", TraceDec_nat, Assert(FALSE, "trace: t_confirm_read leaves out its parameter s, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_confirm_read(a1_, a2_, a3_)
      [] e_2.step \in {"t_grant", "test_crate::t_grant"} ->
           Next /\ TraceParamsDeclared(e_2, {"v", "c", "t", "clog"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "v", TraceDec_int, Assert(FALSE, "trace: t_grant leaves out its parameter v, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "c", TraceDec_int, Assert(FALSE, "trace: t_grant leaves out its parameter c, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a3_ \in TraceParamUnbounded(e_2, "t", TraceDec_nat, Assert(FALSE, "trace: t_grant leaves out its parameter t, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a4_ \in TraceParamUnbounded(e_2, "clog", TraceDec_Seq_AEntry, Assert(FALSE, "trace: t_grant leaves out its parameter clog, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_grant(a1_, a2_, a3_, a4_)
      [] e_2.step \in {"t_leader_commit", "test_crate::t_leader_commit"} -> Next /\ TraceParamsDeclared(e_2, {"i", "ci", "q"}) /\ Assert(FALSE, "trace: t_leader_commit cannot be checked independently because its domain requires caller guards; log next instead")
      [] e_2.step \in {"t_propose", "test_crate::t_propose"} -> TraceArm_t_propose(e_2, TraceDec_int, TraceDec_Option_Seq_u8)
      [] e_2.step \in {"t_recv_append", "test_crate::t_recv_append"} -> Next /\ TraceParamsDeclared(e_2, {"i", "t", "b", "bt", "entries"}) /\ Assert(FALSE, "trace: t_recv_append cannot be checked independently because its domain requires caller guards; log next instead")
      [] e_2.step \in {"t_recv_commit", "test_crate::t_recv_commit"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "ci", "mi", "rec"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_recv_commit leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "ci", TraceDec_nat, Assert(FALSE, "trace: t_recv_commit leaves out its parameter ci, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a3_ \in TraceParamUnbounded(e_2, "mi", TraceDec_nat, Assert(FALSE, "trace: t_recv_commit leaves out its parameter mi, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a4_ \in TraceParamUnbounded(e_2, "rec", TraceDec_CommitRec, Assert(FALSE, "trace: t_recv_commit leaves out its parameter rec, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_recv_commit(a1_, a2_, a3_, a4_)
      [] e_2.step \in {"t_restart", "test_crate::t_restart"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "c"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_restart leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "c", TraceDec_nat, Assert(FALSE, "trace: t_restart leaves out its parameter c, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_restart(a1_, a2_)
      [] e_2.step \in {"t_send_ack", "test_crate::t_send_ack"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "mi"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_send_ack leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "mi", TraceDec_nat, Assert(FALSE, "trace: t_send_ack leaves out its parameter mi, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_send_ack(a1_, a2_)
      [] e_2.step \in {"t_send_append", "test_crate::t_send_append"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "b", "e"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_send_append leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "b", TraceDec_nat, Assert(FALSE, "trace: t_send_append leaves out its parameter b, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a3_ \in TraceParamUnbounded(e_2, "e", TraceDec_nat, Assert(FALSE, "trace: t_send_append leaves out its parameter e, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_send_append(a1_, a2_, a3_)
      [] e_2.step \in {"t_send_commit", "test_crate::t_send_commit"} ->
           Next /\ TraceParamsDeclared(e_2, {"i", "ci"}) /\ \E a1_ \in TraceParamUnbounded(e_2, "i", TraceDec_int, Assert(FALSE, "trace: t_send_commit leaves out its parameter i, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")), a2_ \in TraceParamUnbounded(e_2, "ci", TraceDec_nat, Assert(FALSE, "trace: t_send_commit leaves out its parameter ci, which has no domain to range over (Next passes it no bounded variable, and its type has no finite domain)")) : t_send_commit(a1_, a2_)
      [] e_2.step \in {"t_step_down", "test_crate::t_step_down"} -> TraceArm_t_step_down(e_2, TraceDec_int)
      [] e_2.step \in {"t_submit_read", "test_crate::t_submit_read"} -> TraceArm_t_submit_read(e_2, TraceDec_int)
      [] OTHER -> Next

TraceInit ==
    /\ TraceKeys(TraceHeader, {"module", "export", "state"}, "the log's header")
    /\ Assert("module" \in DOMAIN TraceHeader /\ TraceHeader.module = "GState_tla",
              "trace: the log's header does not name the module GState_tla")
    /\ Assert("export" \in DOMAIN TraceHeader /\ TraceHeader.export = "test_crate",
              "trace: the log's header does not name the export test_crate")
    /\ Init
    /\ trace_i = 1
    /\ TraceObserved(TraceStateOf(TraceHeader))

TraceNext ==
    /\ trace_i <= Len(Trace)
    /\ LET e_2 == Trace[trace_i] IN
           /\ TraceKeys(e_2, {"step", "params", "state"}, "a step line")
           /\ Assert("step" \in DOMAIN e_2, "trace: a step line names no step")
           /\ TraceStep(e_2)
           /\ TraceObservedNext(TraceStateOf(e_2))
    /\ trace_i' = trace_i + 1

TraceSpec == TraceInit /\ [][TraceNext]_<<n, hosts, net, leader_log, leader_of, voters, elect_log, elect_votes, commits, reads, read_hwm, trace_i>>
\* The whole log was followed.
TraceAccepted == trace_i = Len(Trace) + 1

TraceStepAt == Trace[trace_i]
\* The model's steps enabled in the current state, with their parameters
\* (a step whose parameter has no finite domain is not enumerated).
TraceEnabled ==
    {}
\* At a state where the log's next step cannot be taken: whether the logged
\* step is enabled at all, and which observed fields no successor by it matches.
TraceDiagnosis ==
    LET e_2 == TraceStepAt IN
    [ step_enabled |-> ENABLED (Next /\ TraceStep(e_2)),
      unmatched |-> {k_2 \in DOMAIN TraceStateOf(e_2) :
                        ~ENABLED (Next /\ TraceStep(e_2) /\ TraceObservedKeyNext(k_2, TraceStateOf(e_2)[k_2]))} ]
====================================

\* VERUS_TRACE_POLICY {"module":"GState_tla_trace","index_variable":"trace_i","observables":["n","hosts","net","leader_log","leader_of","voters","elect_log","elect_votes","commits","reads","read_hwm"],"steps":[{"step":"next_step","function":"test_crate::next_step","operator":"next_step","short_name_shared":false,"params":[{"name":"step","typ":"TStep","domain":null}],"enumerated":false},{"step":"t_become_leader","function":"test_crate::t_become_leader","operator":"t_become_leader","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null}],"enumerated":false},{"step":"t_bump_term","function":"test_crate::t_bump_term","operator":"t_bump_term","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"t","typ":"nat","domain":null}],"enumerated":false},{"step":"t_campaign","function":"test_crate::t_campaign","operator":"t_campaign","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null}],"enumerated":false},{"step":"t_collect_vote","function":"test_crate::t_collect_vote","operator":"t_collect_vote","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"v","typ":"int","domain":null},{"name":"vlog","typ":"Seq_AEntry","domain":null}],"enumerated":false},{"step":"t_confirm_read","function":"test_crate::t_confirm_read","operator":"t_confirm_read","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"t","typ":"nat","domain":null},{"name":"s","typ":"nat","domain":null}],"enumerated":false},{"step":"t_grant","function":"test_crate::t_grant","operator":"t_grant","short_name_shared":false,"params":[{"name":"v","typ":"int","domain":null},{"name":"c","typ":"int","domain":null},{"name":"t","typ":"nat","domain":null},{"name":"clog","typ":"Seq_AEntry","domain":null}],"enumerated":false},{"step":"t_leader_commit","function":"test_crate::t_leader_commit","operator":"t_leader_commit","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"ci","typ":"nat","domain":null},{"name":"q","typ":"Map_int_nat","domain":null}],"enumerated":false},{"step":"t_propose","function":"test_crate::t_propose","operator":"t_propose","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"cmd","typ":"Option_Seq_u8","domain":null}],"enumerated":false},{"step":"t_recv_append","function":"test_crate::t_recv_append","operator":"t_recv_append","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"t","typ":"nat","domain":null},{"name":"b","typ":"nat","domain":null},{"name":"bt","typ":"nat","domain":null},{"name":"entries","typ":"Seq_AEntry","domain":null}],"enumerated":false},{"step":"t_recv_commit","function":"test_crate::t_recv_commit","operator":"t_recv_commit","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"ci","typ":"nat","domain":null},{"name":"mi","typ":"nat","domain":null},{"name":"rec","typ":"CommitRec","domain":null}],"enumerated":false},{"step":"t_restart","function":"test_crate::t_restart","operator":"t_restart","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"c","typ":"nat","domain":null}],"enumerated":false},{"step":"t_send_ack","function":"test_crate::t_send_ack","operator":"t_send_ack","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"mi","typ":"nat","domain":null}],"enumerated":false},{"step":"t_send_append","function":"test_crate::t_send_append","operator":"t_send_append","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"b","typ":"nat","domain":null},{"name":"e","typ":"nat","domain":null}],"enumerated":false},{"step":"t_send_commit","function":"test_crate::t_send_commit","operator":"t_send_commit","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null},{"name":"ci","typ":"nat","domain":null}],"enumerated":false},{"step":"t_step_down","function":"test_crate::t_step_down","operator":"t_step_down","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null}],"enumerated":false},{"step":"t_submit_read","function":"test_crate::t_submit_read","operator":"t_submit_read","short_name_shared":false,"params":[{"name":"i","typ":"int","domain":null}],"enumerated":false}],"general_relation_steps":["next_step","t_collect_vote","t_confirm_read","t_grant","t_leader_commit","t_recv_append","t_recv_commit","t_restart","t_send_ack","t_send_append","t_send_commit"],"unknown_step":"Next (state-only conformance; logged name and parameters are not checked)"}
