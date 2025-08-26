---- MODULE AbstractRaft ----
\*
\* Towards a logless variant of the Raft consensus algorithm.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC


CONSTANTS Server
CONSTANTS Secondary, Primary, Nil
CONSTANT InitTerm

VARIABLE currentTerm
VARIABLE state
VARIABLE log
VARIABLE committed

vars == <<currentTerm, state, log, committed>>

\*
\* Helper operators.
\*

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Node 'i' gets a new log from node 'j'.
\* This single action compacts all of the incremental log append and rollback machinery into
\* a single, atomic action.
\* MergeEntries(i, j) ==
\*     /\ state[i] = Secondary
\*     /\ \* Log append/merge.
\*        \/ /\ IsPrefix(log[i], log[j]) 
\*           /\ Len(log[i]) < Len(log[j])
\*        \* Log divergence cleanup (rollback).
\*        \/ /\ ~IsPrefix(log[i], log[j])
\*           /\ LastTerm(log[j]) > LastTerm(log[i])
\*     /\ log' = [log EXCEPT ![i] = log[j]]
\*     /\ UNCHANGED <<committed, currentTerm, state>>


MergeEntries(i, j) ==
    /\ state[i] = Secondary
    /\ \* Log append/merge.
       \/ /\ LastTerm(log[j]) = LastTerm(log[i]) 
          /\ Len(log[i]) < Len(log[j])
       \* Log divergence cleanup (rollback).
       \/ LastTerm(log[j]) > LastTerm(log[i])
    /\ log' = [log EXCEPT ![i] = log[j]]
    /\ UNCHANGED <<committed, currentTerm, state>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ UNCHANGED <<log, committed>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c[1] = ind /\ c[2] = currentTerm[i] 
    /\ committed' = committed \cup {<<ind, currentTerm[i], currentTerm[i]>>}
    /\ UNCHANGED <<currentTerm, state, log>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, committed>>

Init == 
    /\ currentTerm = [i \in Server |-> InitTerm]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ committed = {}

Next == 
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i, j \in Server : MergeEntries(i, j)
    \/ \E i \in Server : \E Q \in Quorums(Server) : BecomeLeader(i, Q)
    \/ \E i \in Server :  \E Q \in Quorums(Server) : CommitEntry(i, Q)
    \/ \E i, j \in Server : UpdateTerms(i, j)

Spec == Init /\ [][Next]_vars

NextUnchanged == UNCHANGED vars

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

H_OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c[3] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))

\* \* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in committed : (c1[1] = c2[1]) => (c1 = c2)

LogEdges(s) == {<< <<i, log[s][i]>>, <<i+1, log[s][i+1]>> >> : i \in (DOMAIN log[s] \ {Len(log[s])})}
LogTreeEdges == UNION {LogEdges(s) : s \in Server}
LogNodes(s) == {<<i, log[s][i]>> : i \in DOMAIN log[s]}
LogTreeNodes == UNION {LogNodes(s) : s \in Server}


------------------------------------

\* 
\* Model checking parameters.
\* 

CONSTANT MaxTerm, MaxLogLen

Symmetry == Permutations(Server)

StateConstraint == 
    /\ \A i \in Server : currentTerm[i] <= MaxTerm
    /\ \A i \in Server : Len(log[i]) <= MaxLogLen

\* SomeLogs == (\E s \in Server : Len(log[s]) < 6)
\* SomeLogs == TLCGet("level") < 40





------------------------------------
\* 
\* Visualizations.
\* 


SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")


NodeIsServer(n) == \E s \in Server : ToString(s) = n

\* Graphviz attributes
nodeAttrsFn(n) == [
    label |-> IF NodeIsServer(n) THEN n ELSE "(" \o n \o ")",
    style |-> IF NodeIsServer(n) THEN "none" ELSE "filled",
    color |-> IF NodeIsServer(n) THEN "none" ELSE "black",
    fillcolor |-> IF NodeIsServer(n) THEN "none" ELSE "white",
    fontsize |-> IF NodeIsServer(n) THEN "6" ELSE "10",
    shape |-> "rect"
    \* fillcolor |-> IF n \in CommittedTxns(txnHistory) THEN "lightgreen" ELSE "lightgray"
]

edgeAttrsFn(e) == [
    label |-> "",
    color |-> "black"
    \* fontsize |-> "8"
]

LogTreeNodeStr(n) == ToString(n[1]) \o "_" \o ToString(n[2])
LogTreeNodesStr == {LogTreeNodeStr(n) : n \in LogTreeNodes}
\* LogTreeNodesStr == {LogTreeNodeStr(n) : n \in LogTreeNodes} \cup {ToString(s) : s \in Server}
LogTreeEdgesStr == {<<LogTreeNodeStr(e[1]), LogTreeNodeStr(e[2])>> : e \in LogTreeEdges}
\* LogTreeEdgesStr == {<<LogTreeNodeStr(e[1]), LogTreeNodeStr(e[2])>> : e \in LogTreeEdges} \cup {<<ToString(s), LogTreeNodeStr(<<Len(log[s]), log[s][Len(log[s])]>>)>> : s \in Server}

AnimView == Group(<<DiGraph(LogTreeNodesStr,LogTreeEdgesStr,[n \in LogTreeNodesStr |-> nodeAttrsFn(n)], [e \in LogTreeEdgesStr |-> edgeAttrsFn(e)])>>, [transform |-> "translate(40, 40) scale(1.25)"])


=============================================================================
