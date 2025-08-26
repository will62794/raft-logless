---- MODULE RaftLogless ----
\*
\* Logless variant of the Raft consensus algorithm.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Server
CONSTANTS Secondary, Primary, Nil, Value

VARIABLE currentTerm
VARIABLE state
VARIABLE valVersion
VARIABLE valTerm
VARIABLE val

vars == <<currentTerm, state, valVersion, valTerm, val>>

\*
\* Helper operators.
\*

\* The set of all majority quorums of a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Do all quorums of two sets intersect.
QuorumsOverlap(x, y) == \A qx \in Quorums(x), qy \in Quorums(y) : qx \cap qy # {}

\* Is the val of node i considered 'newer' than the val of node j. This is the condition for
\* node j to accept the val of node i.
IsNewerVal(i, j) ==
    \/ valTerm[i] > valTerm[j]
    \/ /\ valTerm[i] = valTerm[j]
       /\ valVersion[i] > valVersion[j]

IsNewerOrEqualVal(i, j) ==
    \/ /\ valTerm[i] = valTerm[j]
       /\ valVersion[i] = valVersion[j]
    \/ IsNewerVal(i, j)

\* Compares two vals given as <<valVersion, valTerm>> tuples.
NewerVal(ci, cj) ==
    \* Compare valTerm first.
    \/ ci[2] > cj[2] 
    \* Compare valVersion if terms are equal.
    \/ /\ ci[2] = cj[2]
       /\ ci[1] > cj[1]  

\* Compares two vals given as <<valVersion, valTerm>> tuples.
NewerOrEqualVal(ci, cj) == NewerVal(ci, cj) \/ ci = cj

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForVal(i, j, term) ==
    /\ currentTerm[i] < term
    /\ IsNewerOrEqualVal(j, i)
    
\* A quorum of servers in the val of server i have i's val.
ValQuorumCheck(i) ==
    \E Q \in Quorums(Server) : \A t \in Q : 
        /\ valVersion[t] = valVersion[i]
        /\ valTerm[t] = valTerm[i]

\* A quorum of servers in the val of server i have the term of i.
TermQuorumCheck(i) ==
    \E Q \in Quorums(Server) : \A t \in Q : currentTerm[t] = currentTerm[i]    

-------------------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Update terms if node 'i' has a newer term than node 'j' and ensure 'j' reverts to Secondary state.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]

UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<valVersion, valTerm, val>>

BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current valuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum
    /\ \A v \in voteQuorum : CanVoteForVal(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    \* Update val's term on step-up.
    /\ valTerm' = [valTerm EXCEPT ![i] = newTerm]
    /\ UNCHANGED <<val, valVersion>>    

\* A reval occurs on node i. The node must currently be a leader.
WriteNewVal(i, newval) ==
    /\ state[i] = Primary
    /\ ValQuorumCheck(i)
    /\ TermQuorumCheck(i)
    /\ valTerm' = [valTerm EXCEPT ![i] = currentTerm[i]]
    /\ valVersion' = [valVersion EXCEPT ![i] = valVersion[i] + 1]
    /\ val' = [val EXCEPT ![i] = newval]
    /\ UNCHANGED <<currentTerm, state>>

\* Node i sends its current val to node j.
SendVal(i, j) ==
    /\ state[j] = Secondary
    /\ IsNewerVal(i, j)
    /\ valVersion' = [valVersion EXCEPT ![j] = valVersion[i]]
    /\ valTerm' = [valTerm EXCEPT ![j] = valTerm[i]]
    /\ val' = [val EXCEPT ![j] = val[i]]
    /\ UNCHANGED <<currentTerm, state>>

Init == 
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Secondary]
    /\ valVersion =  [i \in Server |-> 1]
    /\ valTerm    =  [i \in Server |-> 0]
    /\ \E initval \in SUBSET Server :
        /\ initval # {}
        /\ val = [i \in Server |-> initval]

Next ==
    \/ \E s \in Server, newval \in Value : WriteNewVal(s, newval)
    \/ \E s,t \in Server : SendVal(s, t)
    \/ \E i \in Server : \E Q \in Quorums(Server) :  BecomeLeader(i, Q)
    \/ \E s,t \in Server : UpdateTerms(s,t)

Spec == Init /\ [][Next]_vars

------------------------------------

\* 
\* Model checking parameters.
\* 

CONSTANT MaxTerm, MaxVersion

Symmetry == Permutations(Server) \cup Permutations(Value)

StateConstraint == 
    /\ \A i \in Server : currentTerm[i] <= MaxTerm
    /\ \A i \in Server : valVersion[i] <= MaxVersion

=============================================================================