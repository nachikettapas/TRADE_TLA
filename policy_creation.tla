-------------------------- MODULE policy_creation --------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE policyPool
CONSTANT POLICIES
VARIABLE policySource

\* Organization variables
CONSTANT Organization
VARIABLE oState
VARIABLE oBuffer

\* Organization states
CONSTANT O_Waiting, O_CreatePolicy, O_Final

\* Identity blockchain variables
VARIABLE itxPool
VARIABLE iblockTx
CONSTANT TX_POLICY

tempVars == << policyPool, policySource >>
organizationVars == << oState, oBuffer >>
identityBlockchainVars == << itxPool, iblockTx >>

vars == << tempVars, organizationVars, identityBlockchainVars >>

\* Add data
Post(m) == policyPool' = Append(policyPool, m)

\* Transactions to the identity blockchain
blockchainPolicyTxn(r, pid, pprofile) ==
  itxPool' = itxPool \cup {[type |-> TX_POLICY, who |-> r, data |-> << pid, pprofile >>]}

\* Initial states
InitPolicies ==
  /\ policyPool = <<>>
  /\ policySource = POLICIES

InitOrganization ==
  /\ oState = [ o \in Organization |-> O_Waiting ]
  /\ oBuffer = [ o \in Organization |-> <<>> ]
  
InitIdentityBlockchain ==
  /\ itxPool = {}
  /\ iblockTx = {}
 
Init ==
  /\ InitPolicies /\ InitIdentityBlockchain /\ InitOrganization

setup == 
  \E <<pid, ppolicy>> \in policySource:
    LET
      id == pid
      profile == ppolicy
    IN
    /\ policySource' = policySource \ {<<pid, ppolicy>>}
    /\ Post(<<pid, ppolicy>>)
    /\ UNCHANGED << organizationVars, identityBlockchainVars >>
    
Preparation(o) ==
  /\ oState[o] = O_Waiting
  /\ IF Len(policyPool) > 0 THEN
       /\ oBuffer' = [ oBuffer EXCEPT ![o] = Head(policyPool) ]
       /\ oState' = [ oState EXCEPT ![o] = O_CreatePolicy ]
       /\ policyPool' = Tail(policyPool)
       /\ UNCHANGED << policySource, identityBlockchainVars >>
     ELSE
       /\ oState' = [ oState EXCEPT ![o] = O_Final ]
       /\ UNCHANGED << oBuffer, tempVars, identityBlockchainVars >>
       
CreatePolicy(o) ==
  /\ oState[o] = O_CreatePolicy
  /\ blockchainPolicyTxn(o, oBuffer[o][1], oBuffer[o][2])
  /\ oState' = [ oState EXCEPT ![o] = O_Waiting ]
  /\ UNCHANGED << tempVars, oBuffer, iblockTx >>
          
 ConfirmReceipt == 
  \E receiptTx \in itxPool:
    /\ receiptTx.type = TX_POLICY
    /\ itxPool' = itxPool \ { receiptTx }
    /\ iblockTx' = iblockTx \cup { receiptTx }
    /\ UNCHANGED << organizationVars, tempVars >>
    
Termination ==
  /\ \A o \in Organization : oState[o] = O_Final
  /\ UNCHANGED vars
  
Next == 
  \/ setup
  \/ \E o \in Organization :
       \/ Preparation(o) \/ CreatePolicy(o)
  \/ ConfirmReceipt
  \/ Termination
  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Sat Feb 13 13:54:30 CET 2021 by nachi
\* Created Sat Feb 13 12:52:27 CET 2021 by nachi
