---------------------------- MODULE safe_network ----------------------------

(* Naming convention:
 * UpperCase: sets, modules, operators, predicates
 * lowerCase: variables
*)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT numSeedNodes, maxNodes

(* FIXME: could maybe get rid of prefixes and just use DOMAIN sections *)
VARIABLE prefixes, sections, nodeCount

vars == <<prefixes, sections, nodeCount>>

(* Maximum length of any prefix *)
MaxPrefixLen == 4

(* Minimum section size *)
MinSectionSize == 8

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

(* Set of all prefixes upto a finite length *)
Prefixes == UNION {[1..n -> {0, 1}] : n \in 0..MaxPrefixLen}

(* Set of natural numbers representing a set of node IDs *)
NodeNames == SUBSET Nat

(* TODO: section splitting based on XOR metric? *)
SplitThreshold == MinSectionSize * 2 + 2
CanSplit(section) == Cardinality(section) > SplitThreshold

TypeOK == /\ numSeedNodes \in Nat
          /\ prefixes \in SUBSET Prefixes
          /\ sections \in [prefixes -> NodeNames]

(* Step which adds a node to a section *)
AddNode == \E p \in prefixes :
    /\ nodeCount' = nodeCount + 1
    /\ sections' = [sections EXCEPT ![p] = UNION {sections[p], {nodeCount + 1}}]
    /\ nodeCount < maxNodes
    /\ CanSplit(sections[p]) = FALSE
    /\ UNCHANGED prefixes

(* Step which splits a section once it has become too large *)
SplitSection == \E p \in prefixes :
    LET leftPrefix == Append(p, 0) IN
    LET rightPrefix == Append(p, 1) IN
    LET newSectionSize == MinSectionSize + 1 IN
    LET leftSection == ChooseN(sections[p], newSectionSize) IN
    LET rightSection == sections[p]\leftSection IN
    /\ CanSplit(sections[p])
    /\ prefixes' = UNION {prefixes\{p}, {leftPrefix, rightPrefix}}
    /\ sections' = [q \in prefixes' |->
        IF q = leftPrefix THEN leftSection
        ELSE IF q = rightPrefix THEN rightSection
        ELSE sections[q]]
    /\ UNCHANGED nodeCount

(* Initial conditions *)
Init == /\ prefixes = {<<>>}
        /\ nodeCount = numSeedNodes
        /\ sections = [p \in prefixes |-> 1..nodeCount]

(* Step relation *)
Next == \/ AddNode
        \/ SplitSection
        \/ UNCHANGED vars \* Allows stuttering termination... I think.

(* ------- Invariants -------- *)

(* Network size invariant: number of nodes in all sections = total node count *)
NetworkSizeInv == Sum([p \in prefixes |-> Cardinality(sections[p])], prefixes) = nodeCount

(* Num sections invariant: number of sections is less than floor(nodeCount/MinSectionSize) *)
NumSectionsInv == Cardinality(prefixes) <= (nodeCount \div MinSectionSize)

MainInvariant == /\ NetworkSizeInv
                 /\ NumSectionsInv
=============================================================================
\* Modification History
\* Last modified Mon Feb 27 17:00:55 AEDT 2017 by michael
\* Created Mon Feb 27 13:40:49 AEDT 2017 by michael
