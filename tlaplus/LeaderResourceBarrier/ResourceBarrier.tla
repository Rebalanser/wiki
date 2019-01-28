-------------------------- MODULE ResourceBarrier --------------------------
EXTENDS Integers, FiniteSets, TLC, RebalanserRegistry
CONSTANTS N \* the set of all possible nodes that could exist.
VARIABLES node_data,           \* data in each node
          node_ldr,            \* data stored by the current leader
          node_disconnected,   \* set of all nodes isolated from the registry
          isolationEventCtr,   \* a counter of the number isolation events. Used by the model checker to limit the number of events
          resourceAccess       \* A simulation of the real resources. Not part of the Rebalanser system directly, used for verifying an invariant.

Phase == { "-", "stopped", "started" }
Role == { "offline", "none", "follower", "leader" }

RebalancingStats == [aVersion : Nat, inScopeResources : SUBSET R, inScopeNodeIds : SUBSET N]
NoStats == [aVersion |-> 0, inScopeResources |-> {}, inScopeNodeIds |-> {}]

LeaderData == [ nodeId : Nat, nVersion : Nat, rVersion : Nat, term : Nat, rbStats : RebalancingStats]
NoLeader == [ nodeId |-> 0, nVersion |-> 0, rVersion |-> 0, term |-> 0, rbStats |-> NoStats]

NodeData == [id : Nat, role : Role, aVersion : Nat, rbPhase : Phase]
NoNode == [id |-> 0, role |-> "offline", aVersion |-> 0, rbPhase |-> "-"]

vars_regIsolation == << reg_unreachableIds >>
vars_regResources == << reg_resources, reg_rVersion >>
vars_regNodes == << reg_nodeIds, reg_nVersion, reg_nextId >>
vars_regAlloc == << reg_allocations, reg_aVersion >>
vars_regMisc == << reg_term, reg_barrier >>
vars_registry == << vars_regNodes, vars_regResources, vars_regIsolation, vars_regAlloc, vars_regMisc >>

vars_nodeIsolation == << node_disconnected, isolationEventCtr >>
vars_nodeData == << node_data, node_ldr >>
vars_node == << vars_nodeIsolation, vars_nodeData >>

vars == << vars_registry, node_ldr, vars_node, resourceAccess >>

---------------------------------------------------------
(* RESOURCE ACCESS MONITORING *)
(* The actual resources lie outside of the control of this system. 
   The system cannot know whether resources are really being accessed or not, 
   the system can only instruct the starting and stopping of access. 
   What is modelled here is the invariant that two nodes cannot both 
   think they should concurrently access the same resource. *)

RAInit ==
  resourceAccess = [r \in R |-> {}]

RAInvariant ==
  \A ra \in DOMAIN resourceAccess : Cardinality(resourceAccess[ra]) < 2

RAStopAllAccess(n) ==
  resourceAccess' = [ra \in DOMAIN resourceAccess |-> 
                        IF resourceAccess[ra] \cap {n} # {} 
                          THEN resourceAccess[ra] \ {n}
                          ELSE resourceAccess[ra]]

RAStartAccess(n, res) ==
  resourceAccess' = [ra \in DOMAIN resourceAccess |->  
                        IF ra \in res 
                          THEN resourceAccess[ra] \cup {n}
                          ELSE resourceAccess[ra]]

---------------------------------------------------------
(* SYSTEM INIT AND INVARIANTS *)

(* The system starts with no live nodes *)
RBInit == 
  /\ RRInit
  /\ RAInit
  /\ node_ldr = NoLeader
  /\ node_data = [n \in N |-> NoNode]
  /\ node_disconnected = {}
  /\ isolationEventCtr = 0

LiveNodes ==
  { n \in DOMAIN node_data : node_data[n].role # "offline"}
  
LiveNodeIds ==
  { node_data[n].id : n \in { nd \in DOMAIN node_data : node_data[nd].role # "offline"}}

(* True iff an allocation has taken place and all nodes are:
   - in the started phase
   - their started phase applies to the current allocation version *)
RebalancingComplete ==
  /\ reg_aVersion > 0
  /\ \A nodeId \in DOMAIN reg_allocations : nodeId \in LiveNodeIds
  /\ \A n \in LiveNodes : /\ node_data[n].aVersion = reg_aVersion
                          /\ node_data[n].rbPhase = "started"

(* True iff all resources are found in the allocations function *)
AllInScopeResourcesAllocated ==
  \A r \in node_ldr.rbStats.inScopeResources : 
                    \E a \in DOMAIN reg_allocations : r \in reg_allocations[a]

(* True iff all resources are being accessed *)
AllInScopeResourcesAccessed ==
  \A r \in node_ldr.rbStats.inScopeResources : 
                    \E ra \in DOMAIN resourceAccess : /\ r = ra
                                                      /\ resourceAccess[ra] # {}

(* True iff no allocation has yet taken place, or rebalancing is in progress,
   or rebalancing has completed with no unallocated resources. *)
NoUnallocatedResourcesOnRbComplete ==
  \/ reg_aVersion = 0    \* no allocation has been made yet
  \/ node_ldr.nodeId = 0 \* the leader has failed, meaning that we cannot verify this invariant
  \/ /\ reg_aVersion > 0
     /\ \/ /\ RebalancingComplete
           /\ AllInScopeResourcesAllocated
           /\ AllInScopeResourcesAccessed
        \/ ~RebalancingComplete

RBInvariant ==
  /\ NoUnallocatedResourcesOnRbComplete
  /\ node_data \in [N -> NodeData]

------------------------------------------------------
(* CHANGES TO NODES OR RESOURCES *)

(* A resource can be added or removed from the registry. The registry only
   contains meta data about the resource, not the resource itself *)
ResourceChange ==
  /\ \/ \E r \in R \ reg_resources : RRAdminAddResource(r)
     \/ /\ Cardinality(reg_resources) > 1
        /\ \E r \in reg_resources : RRAdminRemoveResource(r)
  /\ UNCHANGED << vars_node, vars_regNodes, vars_regIsolation, vars_regAlloc, vars_regMisc, resourceAccess >> 

(* This version of the resource change provokes the double resource access violation
   caused by removing barriers on removal of resources *)
ResourceChangeForRAInvViolation ==
  /\ \/ /\ \E r \in R \ reg_resources : RRAdminAddResource(r)
        /\ UNCHANGED reg_barrier
     \/ /\ Cardinality(reg_resources) > 1
        /\ \E r \in reg_resources : RRAdminRemoveResourceWithViolation(r)

StartNode(n) ==
  /\ RRAddNode
  /\ node_data' = [node_data EXCEPT ![n] = [id |-> reg_nextId, 
                                            role |-> "none", 
                                            aVersion |-> reg_aVersion, 
                                            rbPhase |-> "-" ]]
  /\ UNCHANGED << node_ldr, vars_nodeIsolation, vars_regResources, vars_regIsolation, vars_regAlloc, vars_regMisc, resourceAccess >>
  
(* A controlled shutdown of a connected node:
   - all resource access stops
   - removed from the registry
   - any barriers it has in the registry are removed
   - all data wiped from node side of model *)
StopConnectedNode(n) ==
  /\ n \notin node_disconnected
  /\ RRRemoveNode(node_data[n].id)
  /\ RAStopAllAccess(n)
  /\ IF node_data[n].id = node_ldr.nodeId 
       THEN node_ldr' = NoLeader 
       ELSE node_ldr' = node_ldr
  /\ node_data' = [node_data EXCEPT ![n] = NoNode]
  /\ UNCHANGED << vars_nodeIsolation, reg_nextId, vars_regResources, vars_regAlloc, reg_term >>

(* A controlled shutdown of an isolated node:
   - all resource access stops
   - all data wiped from node side of model 
   - unable to modify data in the registry*)
StopIsolatedNode(n) ==
  /\ n \in node_disconnected
  /\ RAStopAllAccess(n)
  /\ IF node_data[n].id = node_ldr.nodeId 
       THEN node_ldr' = NoLeader 
       ELSE node_ldr' = node_ldr
  /\ node_data' = [node_data EXCEPT ![n] = NoNode]
  /\ node_disconnected' = node_disconnected \ {n} 
  /\ UNCHANGED << isolationEventCtr, reg_nextId, vars_regNodes, vars_regResources, vars_regIsolation, vars_regAlloc, vars_regMisc >>

(* The registry expires a node in its isolated list, which removes any
   barriers still owned by the node *)
ExpireNode(n) ==
  /\ RRExpireNode(node_data[n].id)
  /\ UNCHANGED << vars_node, reg_nextId, vars_regResources, vars_regAlloc, reg_term, resourceAccess >>

(* A node can be added, removed or expired from the registry. The registry only
   contains meta data about the node, not the node itself.
   The node itself is represented by a node_data record *)    
ClusterChange ==
  \/ \E nd \in N \ LiveNodes : StartNode(nd)
  \/ \E nd \in LiveNodes : \/ StopConnectedNode(nd)
                           \/ StopIsolatedNode(nd)
                           \/ ExpireNode(nd)

EnvironmentChange ==
  \/ ClusterChange
  \/ ResourceChange

-------------------------------------------------------
(* CONNECTIVITY *)

IsConnected(n) ==
  /\ n \notin node_disconnected

-------------------------------------------------------
(* LEADER RESOURCE ALLOCATION*)

LeaderExists == 
  node_ldr.nodeId > 0

(* Rebalancing (a new allocation) is triggered when there is a leader to coordinate it
   and the leader's cached node and resource versions differ from that of the registry *)
ShouldRebalance ==
  /\ LeaderExists
  /\ \/ node_ldr.nVersion # reg_nVersion
     \/ node_ldr.rVersion # reg_rVersion

(* Refresh the leader's cached version numbers *)
UpdateLeaderData ==
  node_ldr' = [node_ldr EXCEPT !.term = reg_term,
                               !.nVersion = reg_nVersion,
                               !.rVersion = reg_rVersion,
                               !.rbStats = [ aVersion |-> reg_aVersion, 
                                             inScopeResources |-> reg_resources,
                                             inScopeNodeIds |-> reg_nodeIds]]

(* True iff the allocations are balanced. Balanced means that:
  - the number of resources assigned to each node matches matches the lower or upper bound
  - no resource has been allocated twice, to different nodes
  - all resources have been allocated *) 
IsBalanced(alloc, lowerBound) ==
  /\ \A n \in reg_nodeIds : Cardinality(alloc[n]) \in {lowerBound, lowerBound+1}
  /\ \A m,n \in reg_nodeIds : m=n \/ alloc[m] \cap alloc[n] = {}
  /\ \A r \in reg_resources : \E n \in reg_nodeIds : r \in alloc[n]

(* Produce a set of allocations, allocationsToCheck, where the resource count per node satisfies lower and upper bound counts.
   Not all allocations will be valid, but the number of allocations to check is much less than SUBSET reg_resources making
   model checking faster.
   For example, if there are 3 nodes and 7 resources, then the lower bound is 2 and the upper bound is 3 
   and a valid allocation would be n1 -> {r1, r2}, n2 -> {r3, r4}, n3 -> {r5, r6, r7}
   There could be many, many permutations of valid allocations. Of those valid allocations, it chooses one.
   By using CHOOSE we greatly reduce the state explosion making model checking faster at the loss of many valid permutations. *)
FindBalancedAllocation ==
  LET lowerBound == Cardinality(reg_resources) \div Cardinality(reg_nodeIds)
      allocationsToCheck == { S \in SUBSET reg_resources : Cardinality(S) \in {lowerBound, lowerBound+1} }
  IN CHOOSE alloc \in [reg_nodeIds -> allocationsToCheck] : IsBalanced(alloc, lowerBound)

(* Write the new allocations to the registry *)
Allocate ==
  RRSetAllocations(FindBalancedAllocation)

(* Perform a new rebalancing (resource allocation) *)  
LeaderRebalance ==
  /\ ShouldRebalance
  /\ UpdateLeaderData
  /\ Allocate
  /\ UNCHANGED << node_data, vars_nodeIsolation, vars_regNodes, vars_regResources, vars_regIsolation, vars_regMisc, resourceAccess >>

(* On becoming a leader, the new leader performs a rebalancing *)
NewLeaderRebalance == 
  Allocate
  
------------------------------------------------------
(* CHANGES TO ROLES *)

(* Having the lowest id and not currently being leader enables the action.
   The role is updated to leader and the term is incremented. The term indicates
   a new leadership period and does not change as long as the new leader continues being the leader*)
BecomeLeader(n) == 
  /\ HasMinId(node_data[n].id)
  /\ node_data[n].role /= "leader"
  /\ node_data' = [node_data EXCEPT ![n].role = "leader"]
  /\ node_ldr' = [nodeId |-> node_data[n].id, term |-> reg_term + 1, nVersion |-> reg_nVersion, rVersion |-> reg_rVersion, rbStats |-> NoStats]
  /\ reg_term' = reg_term + 1
  /\ NewLeaderRebalance
  /\ UNCHANGED << vars_nodeIsolation, vars_regNodes, vars_regResources, vars_regIsolation, reg_barrier, resourceAccess >>

(* Not having the lowest id and not already being a follower enables this action.
   The role is updated to follower. *)
BecomeFollower(n) == 
  /\ ~HasMinId(node_data[n].id)
  /\ node_data[n].role /= "follower"
  /\ node_data' = [node_data EXCEPT ![n].role = "follower"]
  /\ UNCHANGED << node_ldr, vars_nodeIsolation, vars_registry, resourceAccess >>

RoleChange(n) == 
  /\ IsConnected(n)
  /\ BecomeLeader(n) \/ BecomeFollower(n)

-------------------------------------------------------
(* NODE RESPONSE TO NEW ALLOCATION 
   It is important to note that the spec models rebalancing as two phases. This is adequate
   for model checking but any implementation should ensure that:
    - in phase one: before removing barriers, resource access is stopped
    - in phase two: before accessing resources, that the barriers are placed.
   Else the invariant will not hold for the implementation.
*)

StopActivity(n) ==
  RAStopAllAccess(n)

(* iff the node is included in the allocations, then it can start accessing its assigned resources *)
StartActivity(n) ==
  \/ node_data[n].id \notin DOMAIN reg_allocations
  \/ /\ node_data[n].id \in DOMAIN reg_allocations
     /\ RAStartAccess(n, reg_allocations[node_data[n].id])

RemoveBarriers(n) ==
  RRRemoveBarriers(node_data[n].id)

(* iff the node is included in the allocations, then it can add its barriers to its assigned resources *)
AddBarriers(n) ==
  \/ node_data[n].id \notin DOMAIN reg_allocations
  \/ /\ node_data[n].id \in DOMAIN reg_allocations
     /\ RRAddBarriers(node_data[n].id, reg_allocations[node_data[n].id])

(* A node executes phase one of rebalancing when its cached allocation version 
   does not match the version in the registry. When the versions differ, it is
   because the leader has written a new allocation to the registry. In phase one, 
   a node stops all resource access. The action takes place regardless of whether 
   the node is currently accessing a resource or not.
   The node updates its cached allocation version to be the same as in the registry
   and sets its rebalancing phase to stopped.
   *)
PhaseOne(n) == \* First phase - Stop resource access and remove barriers
  LET nd == node_data[n]
  IN /\ nd.aVersion # reg_aVersion    
     /\ StopActivity(n)
     /\ RemoveBarriers(n)
     /\ node_data' = [node_data EXCEPT ![n] = [nd EXCEPT !.rbPhase = "stopped",
                                                         !.aVersion = reg_aVersion]]

(* A node executes phase two of rebalancing when:
   - it is in the stopped phase
   - the allocation version has not changed again since it entered the stopped phase.
     A difference in allocation version would signal that the current rebalancing should be baorted,
     by taking no further steps.
   - no barriers exist on its assigned resources (it may have 0 resources).
   
   If no barriers are preventing phase two then it now adds barriers to any resources 
   it might have been allocated. If there are more nodes than resources then it might not 
   have been assigned any. 
   
   Once the barriers have been added it changes its phase to started can starts to access the resources.
   Note that in the case of 0 allocated resources, it simply changes to the started phase.*)
PhaseTwo(n) == \* Second phase - Add new resource barriers and start resource access
  LET nd == node_data[n]
  IN /\ nd.aVersion = reg_aVersion    
     /\ nd.rbPhase = "stopped"  
     /\ AddBarriers(n)
     /\ StartActivity(n)
     /\ node_data' = [node_data EXCEPT ![n] = [nd EXCEPT !.rbPhase = "started"]]

(* During rebalancing, each node may not have started or be in a different phase.
   Only once a node has assumed a follower or leader role can it carry out its phases. *)                      
RebalancingAction(n) ==
  /\ IsConnected(n)
  /\ node_data[n].role \in { "follower", "leader" }
  /\ \/ PhaseOne(n)
     \/ PhaseTwo(n)
  /\ UNCHANGED << node_ldr, vars_nodeIsolation, vars_regNodes, vars_regResources, vars_regIsolation, vars_regAlloc, reg_term >>
  
------------------------------------------------------
(* NODE FAILURE 
   When a node fails "abruptly" it does so without being able to cleanly
   shutdown and update the registry of its going away. As such, the only
   update to the registry is the addition of its node id to the
   unreachable list which will lead to the expiry and removal of that id.
*)

IfLeaderWipeData(n) ==
  \/ /\ node_data[n].id # node_ldr.nodeId
     /\ node_ldr' = node_ldr
  \/ /\ node_data[n].id = node_ldr.nodeId
     /\ node_ldr' = NoLeader

AbruptNodeFailure(n) ==
  /\ StopActivity(n)
  /\ node_data' = [node_data EXCEPT ![n] = NoNode]
  /\ IfLeaderWipeData(n)
  /\ node_disconnected' = node_disconnected \ {n} \* the node may or may not have been disconnected
  /\ reg_unreachableIds' = reg_unreachableIds \cup {node_data[n].id} \* from the perspective of the registry, it is now simply unreachable
  /\ UNCHANGED << isolationEventCtr, vars_regNodes, vars_regResources, vars_regAlloc, vars_regMisc >>

-------------------------------------------------------
(* NETWORK PARTITIONS 
   In this specification, short term disconnections are ignored. The terms disconnected, unreachable
   and isolated refer to a longer term disconnection that the registry deems long enough to expire
   the meta-data of the affected node. Because the registry must expire the data on disconnection,
   nodes immediately stop any resourcess access and revert to the "none" role and wait for
   the establishment of connectivity again, at which point they will register a new node id with the registry.
*)

RevertToNoRole(n) ==
  /\ StopActivity(n)
  /\ node_data' = [node_data EXCEPT ![n] = [node_data[n] EXCEPT !.role = "none",
                                                                !.id = 0]]
  /\ IfLeaderWipeData(n)

IsolateNode(n) ==
  /\ RRIsolateNode(node_data[n].id)
  /\ RevertToNoRole(n)
  /\ node_disconnected' = node_disconnected \cup {n}
  /\ isolationEventCtr' = isolationEventCtr + 1
  /\ UNCHANGED << vars_regNodes, vars_regResources, vars_regAlloc, vars_regMisc >>

(* By the definition of isolation/disconnection of this spec, the registry has already
   or is pending the removal of the previous id of this node. On reestablishment of
   connectivity, the node establishes a new id *)
UnisolateNode(n) ==
  /\ n \in node_disconnected
  /\ RRAddNode
  /\ node_data' = [node_data EXCEPT ![n] = [id |-> reg_nextId, 
                                            role |-> "none", 
                                            aVersion |-> reg_aVersion, 
                                            rbPhase |-> "-" ]]
  /\ node_disconnected' = node_disconnected \ {n}
  /\ isolationEventCtr' = isolationEventCtr + 1
  /\ UNCHANGED << node_ldr, vars_regResources, vars_regAlloc, vars_regMisc, resourceAccess, reg_unreachableIds >>

-------------------------------------------------------
(* NEXT and TEMPORAL STUFF *)

(* Reactive actions by nodes come down to either assuming a role, being a leader and
   allocating resources, or being any node and executing the four phases of
   rebalancing.  *)
ReactiveNodeAction ==
  \/ \E n \in LiveNodes : \/ RoleChange(n)
                          \/ RebalancingAction(n)
  \/ LeaderRebalance

(* Failures can be loss of network or node failure *)
FailureNodeAction ==
  \E n \in LiveNodes : \/ IsolateNode(n)
                       \/ UnisolateNode(n)
                       \/ AbruptNodeFailure(n)
  
(* Either the environment changes or nodes are reacting to those changes *)
RBNext ==
  \/ EnvironmentChange
  \/ ReactiveNodeAction
  \/ FailureNodeAction
  
(* Temporal forumla - Interrupting resource/node changes*)
RBFairness ==
  /\ WF_vars(EnvironmentChange) \* Environment changes are always enabled and must take place
  /\ SF_vars(ReactiveNodeAction) \* reactive node actions are enabled/disabled repeatedly and must occur repeatedly
  
RBSpec == RBInit /\ [][RBNext]_vars /\ RBFairness

THEOREM RBSpec => []RBInvariant /\ []RRInvariant /\ []RAInvariant

=============================================================================
\* Modification Histo
\* Last modified Thu Jan 24 07:35:57 CET 2019 by Jackck
\* Created Sat Jan 12 20:48:00 CET 2019 by Jack
