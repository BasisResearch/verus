---- MODULE State_tla_trace ----
\* Trace validation for State_tla, the export of `test_crate` (verus -V tla-export).
\* The log is newline-delimited JSON: a header line naming the module
\* ({"module": "State_tla", "export": "test_crate"}, optionally "state": the
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
EXTENDS State_tla, Json, TLC, Integers, Sequences

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

RECURSIVE TraceDec_Step(_), TraceDec_nat(_), TraceObs_Step(_, _), TraceObs_nat(_, _)

\* nat
TraceDec_nat(j) ==
    j
TraceObs_nat(v, j) ==
    v = j

\* Step
TraceDec_Step(j) ==
    IF "tag" \in DOMAIN j
    THEN CASE j.tag = "Inc" -> [tag |-> "Inc"]
           [] j.tag = "Dbl" -> [tag |-> "Dbl"]
           [] OTHER -> Assert(FALSE, "trace: Step has no variant " \o ToString(j.tag))
    ELSE Assert(FALSE, "trace: a Step value decoded whole (a parameter, a Set element or a Map key) must name its tag")
TraceObs_Step(v, j) ==
    (IF "tag" \in DOMAIN j THEN v.tag = j.tag ELSE TRUE) /\ \A k \in DOMAIN j \ {"tag"} :
        Assert(FALSE, "trace: Step has no field " \o k)

TraceObservedKey(k, j) ==
    CASE k = "x" -> TraceObs_nat(x, j)
      [] k = "y" -> TraceObs_nat(y, j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObserved(j) == \A k \in DOMAIN j : TraceObservedKey(k, j[k])
\* The same of the next state: its variables primed, never the log's index.
TraceObservedKeyNext(k, j) ==
    CASE k = "x" -> TraceObs_nat(x', j)
      [] k = "y" -> TraceObs_nat(y', j)
      [] OTHER -> Assert(FALSE, "trace: the state has no field " \o k)
TraceObservedNext(j) == \A k \in DOMAIN j : TraceObservedKeyNext(k, j[k])

TraceIdentity(j) == j
TraceArm_t_dbl(e) == TraceParamsDeclared(e, {}) /\ ((LET step == [tag |-> "Dbl"] IN next_step(step))) /\ TypeOK'
TraceArm_t_inc(e) == TraceParamsDeclared(e, {}) /\ ((LET step == [tag |-> "Inc"] IN next_step(step))) /\ TypeOK'
TraceStep(e) ==
    CASE e.step \in {"next_step", "test_crate::next_step"} ->
           TraceParamsDeclared(e, {"step"}) /\ \E a1_ \in TraceParam(e, "step", TraceDec_Step, ({[tag |-> "Inc"]} \cup {[tag |-> "Dbl"]})) : next_step(a1_) /\ TypeOK'
      [] e.step \in {"t_dbl", "test_crate::t_dbl"} -> TraceArm_t_dbl(e)
      [] e.step \in {"t_inc", "test_crate::t_inc"} -> TraceArm_t_inc(e)
      [] OTHER -> Next

TraceInit ==
    /\ TraceKeys(TraceHeader, {"module", "export", "state"}, "the log's header")
    /\ Assert("module" \in DOMAIN TraceHeader /\ TraceHeader.module = "State_tla",
              "trace: the log's header does not name the module State_tla")
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

TraceSpec == TraceInit /\ [][TraceNext]_<<x, y, trace_i>>
\* The whole log was followed.
TraceAccepted == trace_i = Len(Trace) + 1

TraceStepAt == Trace[trace_i]
\* The model's steps enabled in the current state, with their parameters
\* (a step whose parameter has no finite domain is not enumerated).
TraceEnabled ==
    {r \in {[step |-> "next_step", params |-> [step |-> a1_]] : a1_ \in ({[tag |-> "Inc"]} \cup {[tag |-> "Dbl"]})} :
        ENABLED (next_step(r.params.step) /\ TypeOK')}
    \cup (IF ENABLED (LET r == [step |-> "t_dbl"] IN TraceArm_t_dbl(r)) THEN {[step |-> "t_dbl"]} ELSE {})
    \cup (IF ENABLED (LET r == [step |-> "t_inc"] IN TraceArm_t_inc(r)) THEN {[step |-> "t_inc"]} ELSE {})
\* At a state where the log's next step cannot be taken: whether the logged
\* step is enabled at all, and which observed fields no successor by it matches.
TraceDiagnosis ==
    LET e == TraceStepAt IN
    [ step_enabled |-> ENABLED (Next /\ TraceStep(e)),
      unmatched |-> {k \in DOMAIN TraceStateOf(e) :
                        ~ENABLED (Next /\ TraceStep(e) /\ TraceObservedKeyNext(k, TraceStateOf(e)[k]))} ]
===================================

\* VERUS_TRACE_POLICY {"module":"State_tla_trace","index_variable":"trace_i","observables":["x","y"],"steps":[{"step":"next_step","function":"test_crate::next_step","operator":"next_step","short_name_shared":false,"params":[{"name":"step","typ":"Step","domain":"({[tag |-> \"Inc\"]} \\cup {[tag |-> \"Dbl\"]})"}],"enumerated":true},{"step":"t_dbl","function":"test_crate::t_dbl","operator":"t_dbl","short_name_shared":false,"params":[],"enumerated":true},{"step":"t_inc","function":"test_crate::t_inc","operator":"t_inc","short_name_shared":false,"params":[],"enumerated":true}],"general_relation_steps":[],"unknown_step":"Next (state-only conformance; logged name and parameters are not checked)"}
