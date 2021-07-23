---- MODULE trace ----

EXTENDS Naturals, Sequences

\* simple counter specification

---- MODULE counter ----

VARIABLE x

TypeOK == x \in Nat

Init == x = 0

Next == x' = x + 1

Safety == Init /\ [][Next]_x

Spec == Safety /\ WF_x(Next)

========================

\* module for checking multiple traces

---- MODULE TracesReader ----

EXTENDS TLC

CONSTANT Traces

VARIABLE x

Model == INSTANCE counter

VARIABLES
    log,
    i

\* trace from [log]
Trace == Traces[log]

\* Read the [log] record at index i
Read == x = Trace[i]

\* Read the next [log] record (index i')
ReadNext == x' = Trace[i']

Init ==
    /\ log \in DOMAIN Traces
    /\ i = 1
    /\ Read

Next ==
    /\ i < Len(Trace)
    /\ i' = i + 1
    /\ UNCHANGED log \* each trace follows a single log

TraceBehavior == Init /\ [][Next]_<<log, i, x>>

THEOREM TraceBehavior => Model!Safety

=============================

\* instantiate the parser and Trace
INSTANCE trace_def

VARIABLES x, i

tvars == <<x, i>>

Read == x = Trace[i]

ReadNext == x' = Trace[i']

InitTrace ==
    /\ i = 1
    /\ Read

NextTrace ==
    /\ i' = i + 1
    /\ ReadNext

---- MODULE TraceReader ----

Compose(NextA, varsA, NextB, varsB) ==
    \/ NextA /\ NextB
    \/ UNCHANGED varsB /\ NextA
    \/ UNCHANGED varsA /\ NextB

VARIABLE xx

Model == INSTANCE counter

ComposedSpec ==
    /\ Model!Init
    /\ InitTrace
    /\ [][Compose(Model!Next, xx, NextTrace, tvars)]_<<xx, tvars>>

TraceFinished == i >= Len(Trace)

NotTraceFinished == ~TraceFinished

\* This should not be a theorem
Check == ComposedSpec => []NotTraceFinished

\* To check this, we declare NotTraceFinished as an invariant and expect an error/counterexample

============================

INSTANCE TraceReader WITH xx <- x

======================
