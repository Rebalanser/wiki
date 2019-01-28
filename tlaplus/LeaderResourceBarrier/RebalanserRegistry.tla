------------------------- MODULE RebalanserRegistry -------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANTS R \* the set of all possible resources that could exist. 
VARIABLES reg_resources,      \* the set of resources in the register.
          reg_rVersion,       \* the current version of the resources. Incremented every time a resource is added or removed.
          reg_nodeIds,        \* the set of nodes ids.
          reg_nVersion,       \* the current version of the nodes. Incremented every time a node is added or removed.
          reg_allocations,    \* the resource to node allocations (a function of nodes to resources).
          reg_aVersion,       \* the current version of the allocations. Incremented each time a new allocations is set.
          reg_barrier,        \* the resource barriers. A function of resource to node id.
          reg_term,           \* the leadership term. Incremented each time a leader is elected.
          reg_nextId,         \* a counter used to assign an id to a node. Increments each time a node is added.
          reg_unreachableIds  \* the set of nodes that are isolated from the registry

RRInit == 
  /\ reg_resources = R
  /\ reg_rVersion = 0
  /\ reg_nodeIds = {}
  /\ reg_nVersion = 0
  /\ reg_nextId = 1
  /\ reg_allocations = << >>
  /\ reg_aVersion = 0
  /\ reg_term = 0
  /\ reg_barrier = [r \in R |-> 0]
  /\ reg_unreachableIds = {}
  
(* The resource allocations are balanced if there is not a difference in the number
   of resources assigned between two nodes that is greater than 1 *)
NoImbalancedAllocations ==
  \/ Cardinality(DOMAIN reg_allocations) <= 1
  \/ /\ Cardinality(DOMAIN reg_allocations) > 1
     /\ \A n,m \in DOMAIN reg_allocations : Cardinality(reg_allocations[n]) - Cardinality(reg_allocations[m]) \in {-1, 0, 1}
  
RRInvariant ==
  /\ reg_resources \subseteq R
  /\ reg_rVersion \in Nat
  /\ reg_nodeIds \in SUBSET Nat
  /\ reg_nVersion \in Nat
  /\ reg_nextId \in Nat
  /\ reg_aVersion \in Nat
  /\ reg_barrier \in [R -> Nat]
  /\ reg_term \in Nat
  /\ NoImbalancedAllocations

(* Adds a resource to the resources set and additionally the rVersion variable is incremented to signal a change in the resources *)
RRAdminAddResource(r) == 
  /\ reg_resources' = reg_resources \cup {r}
  /\ reg_rVersion' = reg_rVersion + 1

(* Adds a resource from the resources set and additionally the rVersion variable is incremented to signal a change in the resources *)
RRAdminRemoveResource(r) ==
  /\ reg_resources' = reg_resources \ {r}
  /\ reg_rVersion' = reg_rVersion + 1
  
(* Adds a resource from the resources set and additionally the rVersion variable is incremented to signal a change in the resources *)
RRAdminRemoveResourceWithViolation(r) ==
  /\ RRAdminRemoveResource(r)
  /\ reg_barrier' = [reg_barrier EXCEPT ![r] = 0] \* this line introduces a violation

(* Adds a barrier to each of the resources of the argument res
   iff there is already no barrier on each of these resources.
   If there is an existing barrier then the action does not take place.
   The barrier consists of the node id of the node that is placing the barrier. *)
RRAddBarriers(nodeId, res) ==
  /\ \A r \in res : reg_barrier[r] = 0
  /\ reg_barrier' = [rb \in DOMAIN reg_barrier |->
                       IF rb \in res 
                          THEN nodeId 
                          ELSE reg_barrier[rb]]
  
(* Searches through all of the barriers to find one or more barriers owned by the given node id.
   Any matches it finds, it removes the barrier (by setting it to 0) *)
RRRemoveBarriers(nodeId) ==
  reg_barrier' = [rb \in DOMAIN reg_barrier |-> 
                    IF reg_barrier[rb] = nodeId 
                       THEN 0 
                       ELSE reg_barrier[rb]]
  
(* The id models a monotonically incrementing id which guarantees that each node
   in the cluster has a unique id and older nodes have lower ids than newer nodes *)
RRIncrementNextId ==
  reg_nextId' = reg_nextId + 1

(* Adds a node to the nodes set and a new node id.
   Additionally the nVersion variable is incremented to signal a change in the cluster *)
RRAddNode == 
  /\ reg_nodeIds' = reg_nodeIds \cup {reg_nextId}
  /\ RRIncrementNextId
  /\ reg_nVersion' = reg_nVersion + 1
  
(* Removes a node from the nodes set and removes its node id.
   Additionally the nVersion variable is incremented to signal a change in the cluster *)
RRRemoveNode(nodeId) ==
  /\ reg_nodeIds' = reg_nodeIds \ {nodeId}
  /\ reg_nVersion' = reg_nVersion + 1
  /\ reg_unreachableIds' = reg_unreachableIds \ {nodeId}
  /\ RRRemoveBarriers(nodeId)

(* Having the lowest id in the cluster makes a node the leader *)
HasMinId(nodeId) == 
  \A x \in reg_nodeIds : nodeId <= x

(* Assigns a new allocations function and increments the allocations version. *)
RRSetAllocations(a) ==
  /\ reg_allocations' = a
  /\ reg_aVersion' = reg_aVersion + 1

(* Iff the node is not currently unreachable then add the node id to the unreachable ids *)
RRIsolateNode(nodeId) == 
  /\ nodeId \in reg_nodeIds
  /\ nodeId \notin reg_unreachableIds
  /\ reg_unreachableIds' = reg_unreachableIds \cup {nodeId}
  
(* Iff the node is unreachable then move all trace of it *)
RRExpireNode(nodeId) ==
  /\ nodeId \in reg_unreachableIds
  /\ RRRemoveNode(nodeId)
  
RRIsIsolated(nodeId) ==
  nodeId \in reg_unreachableIds
  
=============================================================================
\* Modification History
\* Last modified Mon Jan 28 13:19:48 CET 2019 by Jack
\* Created Tue Jan 22 09:41:47 CET 2019 by Jac

