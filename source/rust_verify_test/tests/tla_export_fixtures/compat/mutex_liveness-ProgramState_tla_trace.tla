---- MODULE ProgramState_tla_trace ----
\* Trace validation for ProgramState_tla, the export of `test_crate` (verus -V tla-export).
\* The log is newline-delimited JSON: a header line naming the module
\* ({"module": "ProgramState_tla", "export": "test_crate"}, optionally "state": the
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
EXTENDS ProgramState_tla, Json, TLC, Integers, Sequences

CONSTANT TraceLog  \* the log's path
VARIABLE trace_i  \* the next logged step to take

TraceLines == ndJsonDeserialize(TraceLog)
TraceHeader == TraceLines[1]
Trace == SubSeq(TraceLines, 2, Len(TraceLines))

\* Whether a JSON value is an array (TLC holds it as a tuple).
TraceIsArray(j) == SubSeq(ToString(j), 1, 2) = "<<"
TraceStateOf(e) == IF "state" \in DOMAIN e THEN e.state ELSE [k \in {} |-> 0]
\* A logged parameter, or the domain it ranges over when left out. The domain
\* holds every value Next passes it, so a logged value outside it is a step
\* the model cannot take.
TraceParam(e, k, Dec(_), D) ==
    IF "params" \in DOMAIN e /\ k \in DOMAIN e.params THEN {Dec(e.params[k])} \cap D ELSE D
\* The same for a parameter with no domain, which must be logged.
TraceParamUnbounded(e, k, Dec(_), D) ==
    IF "params" \in DOMAIN e /\ k \in DOMAIN e.params THEN {Dec(e.params[k])} ELSE D
\* Every parameter logged is one of S, the step's declared parameters (an IF,
\* not a disjunction, which TLC would take as two branches of the action).
TraceParamsDeclared(e, S) ==
    "params" \in DOMAIN e =>
        \A k \in DOMAIN e.params :
            IF k \in S THEN TRUE
            ELSE Assert(FALSE, "trace: " \o e.step \o " has no parameter " \o k)

\* Every key of a log line is one of S, so a misspelled "state" or
\* "params" stops TLC rather than observing nothing.
TraceKeys(e, S, j) ==
    \A k \in DOMAIN e :
        IF k \in S THEN TRUE
        ELSE Assert(FALSE, "trace: " \o j \o " has no key " \o k)

RECURSIVE TraceDec_Map_Tid_ThreadState(_), TraceDec_ThreadState(_), TraceDec_Tid(_), TraceDec_bool(_), TraceObs_Map_Tid_ThreadState(_, _), TraceObs_ThreadState(_, _), TraceObs_Tid(_, _), TraceObs_bool(_, _)

\* bool
TraceDec_bool(j) ==
    j
TraceObs_bool(v, j) ==
    v = j

\* Tid
TraceDec_Tid(j) ==
    IF "tag" \in DOMAIN j
    THEN CASE j.tag = "A" -> [tag |-> "A"]
           [] j.tag = "B" -> [tag |-> "B"]
           [] OTHER -> Assert(FALSE, "trace: Tid has no variant " \o ToString(j.tag))
    ELSE Assert(FALSE, "trace: a Tid value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Tid(v, j) ==
    (IF "tag" \in DOMAIN j THEN v.tag = j.tag ELSE TRUE) /\ \A k \in DOMAIN j \ {"tag"} :
        Assert(FALSE, "trace: Tid has no field " \o k)

\* ThreadState
TraceDec_ThreadState(j) ==
    IF "tag" \in DOMAIN j
    THEN CASE j.tag = "Waiting" -> [tag |-> "Waiting"]
           [] j.tag = "Holding" -> [tag |-> "Holding"]
           [] j.tag = "Terminated" -> [tag |-> "Terminated"]
           [] OTHER -> Assert(FALSE, "trace: ThreadState has no variant " \o ToString(j.tag))
    ELSE Assert(FALSE, "trace: a ThreadState value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_ThreadState(v, j) ==
    (IF "tag" \in DOMAIN j THEN v.tag = j.tag ELSE TRUE) /\ \A k \in DOMAIN j \ {"tag"} :
        Assert(FALSE, "trace: ThreadState has no field " \o k)

\* Map_Tid_ThreadState
TraceDec_Map_Tid_ThreadState(j) ==
    [k \in {TraceDec_Tid(j[p][1]) : p \in 1..Len(j)} |-> TraceDec_ThreadState(j[CHOOSE p \in 1..Len(j) : TraceDec_Tid(j[p][1]) = k][2])]
TraceObs_Map_Tid_ThreadState(v, j) ==
    DOMAIN v = {TraceDec_Tid(j[p][1]) : p \in 1..Len(j)} /\ \A p \in 1..Len(j) : TraceObs_ThreadState(v[TraceDec_Tid(j[p][1])], j[p][2])

TraceObservedKey(k, j) ==
    CASE k = "lock" -> TraceObs_bool(lock, j)
      [] k = "threads" -> TraceObs_Map_Tid_ThreadState(threads, j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObserved(j) == \A k \in DOMAIN j : TraceObservedKey(k, j[k])
\* The same of the next state: its variables primed, never the log's index.
TraceObservedKeyNext(k, j) ==
    CASE k = "lock" -> TraceObs_bool(lock', j)
      [] k = "threads" -> TraceObs_Map_Tid_ThreadState(threads', j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObservedNext(j) == \A k \in DOMAIN j : TraceObservedKeyNext(k, j[k])

TraceAction_thread_acquires_lock(trace_input) == thread_acquires_lock(trace_input)
TraceAction_thread_releases_lock(trace_input_2) == thread_releases_lock(trace_input_2)
TraceAction_stutter == stutter
TraceIdentity(j) == j
TraceStep(e) ==
    CASE e.step \in {"next", "test_crate::next"} ->
           Next /\ TraceParamsDeclared(e, {}) /\ next
      [] e.step \in {"thread_acquires_lock", "test_crate::thread_acquires_lock"} ->
           Next /\ TraceParamsDeclared(e, {"input"}) /\ \E a1_ \in TraceParam(e, "input", TraceDec_Tid, (({[tag |-> "A"]} \cup {[tag |-> "B"]}))) : TraceAction_thread_acquires_lock(a1_)
      [] e.step \in {"thread_releases_lock", "test_crate::thread_releases_lock"} ->
           Next /\ TraceParamsDeclared(e, {"input"}) /\ \E a1_ \in TraceParam(e, "input", TraceDec_Tid, (({[tag |-> "A"]} \cup {[tag |-> "B"]}))) : TraceAction_thread_releases_lock(a1_)
      [] e.step \in {"stutter", "test_crate::stutter"} ->
           TraceParamsDeclared(e, {}) /\ TraceAction_stutter
      [] OTHER -> Next

TraceInit ==
    /\ TraceKeys(TraceHeader, {"module", "export", "state"}, "the log's header")
    /\ Assert("module" \in DOMAIN TraceHeader /\ TraceHeader.module = "ProgramState_tla",
              "trace: the log's header does not name the module ProgramState_tla")
    /\ Assert("export" \in DOMAIN TraceHeader /\ TraceHeader.export = "test_crate",
              "trace: the log's header does not name the export test_crate")
    /\ Init
    /\ trace_i = 1
    /\ TraceObserved(TraceStateOf(TraceHeader))

TraceNext ==
    /\ trace_i <= Len(Trace)
    /\ LET e == Trace[trace_i] IN
           /\ TraceKeys(e, {"step", "params", "state"}, "a step line")
           /\ Assert("step" \in DOMAIN e, "trace: a step line names no step")
           /\ TraceStep(e)
           /\ TraceObservedNext(TraceStateOf(e))
    /\ trace_i' = trace_i + 1

TraceSpec == TraceInit /\ [][TraceNext]_<<lock, threads, trace_i>>
\* The whole log was followed.
TraceAccepted == trace_i = Len(Trace) + 1

TraceStepAt == Trace[trace_i]
\* The model's steps enabled in the current state, with their parameters
\* (a step whose parameter has no finite domain is not enumerated).
TraceEnabled ==
    (IF ENABLED (Next /\ next) THEN {[step |-> "next"]} ELSE {})
    \cup {r \in {[step |-> "thread_acquires_lock", params |-> [input |-> a1_]] : a1_ \in (({[tag |-> "A"]} \cup {[tag |-> "B"]}))} :
        ENABLED (Next /\ TraceAction_thread_acquires_lock(r.params.input))}
    \cup {r \in {[step |-> "thread_releases_lock", params |-> [input |-> a1_]] : a1_ \in (({[tag |-> "A"]} \cup {[tag |-> "B"]}))} :
        ENABLED (Next /\ TraceAction_thread_releases_lock(r.params.input))}
    \cup (IF ENABLED (TraceAction_stutter) THEN {[step |-> "stutter"]} ELSE {})
\* At a state where the log's next step cannot be taken: whether the logged
\* step is enabled at all, and which observed fields no successor by it matches.
TraceDiagnosis ==
    LET e == TraceStepAt IN
    [ step_enabled |-> ENABLED (Next /\ TraceStep(e)),
      unmatched |-> {k \in DOMAIN TraceStateOf(e) :
                        ~ENABLED (Next /\ TraceStep(e) /\ TraceObservedKeyNext(k, TraceStateOf(e)[k]))} ]
==========================================

\* VERUS_TRACE_POLICY {"module":"ProgramState_tla_trace","index_variable":"trace_i","observables":["lock","threads"],"steps":[{"step":"next","function":"test_crate::next","operator":"next","short_name_shared":false,"params":[],"enumerated":true},{"step":"thread_acquires_lock","function":"test_crate::thread_acquires_lock","operator":"TraceAction_thread_acquires_lock","short_name_shared":false,"params":[{"name":"input","typ":"Tid","domain":"(({[tag |-> \"A\"]} \\cup {[tag |-> \"B\"]}))"}],"enumerated":true},{"step":"thread_releases_lock","function":"test_crate::thread_releases_lock","operator":"TraceAction_thread_releases_lock","short_name_shared":false,"params":[{"name":"input","typ":"Tid","domain":"(({[tag |-> \"A\"]} \\cup {[tag |-> \"B\"]}))"}],"enumerated":true},{"step":"stutter","function":"test_crate::stutter","operator":"TraceAction_stutter","short_name_shared":false,"params":[],"enumerated":true}],"general_relation_steps":["next","thread_acquires_lock","thread_releases_lock"],"unknown_step":"Next (state-only conformance; logged name and parameters are not checked)"}
