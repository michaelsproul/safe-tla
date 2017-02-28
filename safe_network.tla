---------------------------- MODULE safe_network ----------------------------

(* Naming convention:
 * UpperCase: sets, modules, operators, predicates
 * lowerCase: variables
*)
EXTENDS Naturals, Sequences, FiniteSets, TLC


(* --------- Utility functions -------------- *)
(* Sum of a set of natural numbers *)
(* From: https://github.com/jameshfisher/tlaplus/blob/master/examples/CarTalkPuzzle/CarTalkPuzzle.tla *)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                      ELSE LET x == CHOOSE x \in S : TRUE
                           IN f[x] + Sum(f, S \ {x})

(* Choose n arbitrary elements of a set *)
RECURSIVE ChooseN(_, _)
ChooseN(S, n) == IF n = 0 THEN {} ELSE
   LET chosen == CHOOSE x \in S : TRUE
   IN UNION {{chosen}, ChooseN(S\{chosen}, n - 1)}


(* --------------- The model --------------------- *)
CONSTANT numSeedNodes, maxNodes

(* FIXME: could maybe get rid of prefixes and just use DOMAIN sections *)
VARIABLE nodes, sections, nodeCount
vars == <<nodes, sections, nodeCount>>

(* Fixed values *)
MaxPrefixLen == 6 \* Maximum length of any prefix
MinSectionSize == 8 \* Minimum section size

(* Typing rules *)
(* Set of all prefixes up to a finite length *)
Prefixes == UNION {[1..n -> {0, 1}] : n \in 0..MaxPrefixLen}

IsRT(rt) == \A prefix \in DOMAIN rt:
    /\ prefix \in Prefixes
    /\ \A node \in rt[prefix]: node \in Nat

SectionsOK == \A prefix \in DOMAIN sections:
    /\ prefix \in Prefixes
    /\ IsRT(sections[prefix])

NodesOK == \A node \in DOMAIN nodes:
    /\ node \in Nat
    /\ nodes[node] \in Prefixes
    /\ nodes[node] \in DOMAIN sections

(* Type invariant *)
TypeOK == /\ numSeedNodes \in Nat
          /\ SectionsOK
          /\ NodesOK

(* Next-step relations *)

(* TODO: section splitting based on XOR metric? *)
SplitThreshold == MinSectionSize * 2 + 2
CanSplit(section) == Cardinality(section) > SplitThreshold

(* Step which adds a node to a section *)
(* FIXME: re-enable this
AddNode == \E p \in prefixes :
    /\ nodeCount' = nodeCount + 1
    /\ sections' = [sections EXCEPT ![p] = UNION {sections[p], {nodeCount + 1}}]
    /\ nodeCount < maxNodes
    /\ CanSplit(sections[p]) = FALSE
    /\ UNCHANGED prefixes
*)

SplitSection == \E prefix \in DOMAIN sections:
    LET ourSection == sections[prefix][prefix] IN
    LET leftPrefix == Append(prefix, 0) IN
    LET rightPrefix == Append(prefix, 1) IN
    LET newPrefixes == UNION {(DOMAIN sections)\{prefix}, {leftPrefix, rightPrefix}} IN
    LET newSectionSize == MinSectionSize + 1 IN
    LET leftSection == ChooseN(ourSection, newSectionSize) IN
    LET rightSection == ourSection\leftSection IN
    LET updatedRT == [q \in newPrefixes |->
        IF q = leftPrefix THEN leftSection
        ELSE IF q = rightPrefix THEN rightSection
        ELSE sections[prefix][q]
    ] IN
    /\ CanSplit(ourSection)
    (* TODO: delete sections that we're now disconnected from *)
    /\ sections' = [q \in newPrefixes |->
        IF q = leftPrefix THEN updatedRT
        ELSE IF q = rightPrefix THEN updatedRT
        ELSE sections[q]]
    (* TODO: send section update to neighbours *)
    /\ nodes' = [n \in DOMAIN nodes |->
        IF n \in leftSection THEN leftPrefix
        ELSE IF n \in rightSection THEN rightPrefix
        ELSE nodes[n]]
    /\ UNCHANGED nodeCount

(* Initial conditions *)
Init == /\ nodeCount = numSeedNodes
        /\ LET initRT == [p \in {<<>>} |-> (1..nodeCount)] IN
           sections = [p \in {<<>>} |-> initRT]
        /\ nodes = [n \in (1..nodeCount) |-> <<>>]

(* Step relation *)
Next == \/ SplitSection
        \/ UNCHANGED vars \* Allows stuttering termination... I think.

(* ------- Invariants -------- *)

(* Network size invariant: number of nodes in all sections = total node count *)
\* NetworkSizeInv == Sum([p \in prefixes |-> Cardinality(sections[p])], prefixes) = nodeCount

(* Num sections invariant: number of sections is less than floor(nodeCount/MinSectionSize) *)
\* NumSectionsInv == Cardinality(prefixes) <= (nodeCount \div MinSectionSize)

\* FIXME: restore invariants
MainInvariant == TRUE
=============================================================================
\* Modification History
\* Last modified Tue Feb 28 17:23:34 AEDT 2017 by michael
\* Created Mon Feb 27 13:40:49 AEDT 2017 by michael
