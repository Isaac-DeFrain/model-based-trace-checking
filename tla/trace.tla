---- MODULE trace ----

EXTENDS Naturals, Sequences, TLC

\* simple counter specification

---- MODULE counter ----

CONSTANT a

VARIABLE x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in Nat
    /\ y \in BOOLEAN \cup {a}

Init ==
    /\ x = 0
    /\ y = a

A ==
    /\ x <= 20
    /\ x' = x + 1
    /\ UNCHANGED y

B ==
    /\ x > 20
    /\ x' = x + 1
    /\ y' = (x % 2 = 0)

Next == A \/ B

Safety == Init /\ [][Next]_vars

Spec == Safety /\ WF_vars(Next)

========================

\* module for checking multiple traces

---- MODULE TracesReader ----

EXTENDS TLC

CONSTANTS a, Traces

VARIABLE x, y

Model == INSTANCE counter

VARIABLES
    log,    \* log file index
    i       \* line index within a log file

\* trace from [log]
Trace == Traces[log]

\* Read the [log] record at index i
Read ==
    LET Rec == Trace[i] IN
    /\ x = Rec[1]
    /\ y = Rec[2]

\* Read the next [log] record (index i')
ReadNext ==
    LET Rec == Trace[i'] IN
    /\ x' = Rec[1]
    /\ y' = Rec[2]

Init ==
    /\ log \in DOMAIN Traces
    /\ i = 1
    /\ Read

Next ==
    /\ i < Len(Trace)
    /\ i' = i + 1
    /\ ReadNext
    /\ UNCHANGED log \* each trace follows a single log

TraceBehavior == Init /\ [][Next]_<<log, i, x, y>>

THEOREM TraceBehavior => Model!Safety

=============================

\* instantiate the parser and Trace
INSTANCE trace_def

CONSTANT a

VARIABLES x, y, i

tvars == <<x, y, i>>

Read ==
    LET Rec == Trace[i] IN
    /\ x = Rec[1]
    /\ y = Rec[2]

ReadNext ==
    LET Rec == Trace[i'] IN
    /\ x' = Rec[1]
    /\ y' = Rec[2]

InitTrace ==
    /\ i = 1
    /\ Read

NextTrace ==
    /\ i < Len(Trace)
    /\ i' = i + 1
    /\ ReadNext

---- MODULE TraceReader ----

Compose(NextA, varsA, NextB, varsB) ==
    \/ NextA /\ NextB
    \/ UNCHANGED varsB /\ NextA
    \/ UNCHANGED varsA /\ NextB

VARIABLE xx, yy

vars == <<xx, yy>>

Model == INSTANCE counter

ComposedSpec ==
    /\ Model!Init
    /\ InitTrace
    /\ [][Compose(Model!Next, vars, NextTrace, tvars)]_<<vars, tvars>>

TraceFinished == i >= Len(Trace)

NotTraceFinished == ~TraceFinished

\* This should not be a theorem
Check == ComposedSpec => []NotTraceFinished

\* To check this, we declare NotTraceFinished as an invariant and expect an error/counterexample

============================

INSTANCE TraceReader WITH xx <- x, yy <- y

======================
