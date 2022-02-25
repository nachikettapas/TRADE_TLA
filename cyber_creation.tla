--------------------------- MODULE cyber_creation ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE cyberPool
CONSTANT CYBERTHREATS
VARIABLE cyberSource

CONSTANT POLICY_ID

\* Organization variables
CONSTANT Organization
VARIABLE oState
VARIABLE oBuffer

\* Organization states
CONSTANT O_Waiting, O_Insert, O_AssociatePolicy, O_Final

\* Server variables
CONSTANT Server
VARIABLE sState
VARIABLE sBuffer

\* Registrar states
CONSTANT S_Waiting, S_Final 

\* Identity blockchain variables
VARIABLE atxPool
VARIABLE ablockTx
CONSTANT ATX_CYBER_THREAT

\* Communication channel
VARIABLE channel
CONSTANT M_Insertion, M_OK, M_NO, M_PolicyAssociation

tempVars == << cyberPool, cyberSource >>
organizationVars == << oState, oBuffer >>
serverVars == << sState, sBuffer >>
commVars == << channel >>
activityBlockchainVars == << atxPool, ablockTx >>

vars == << tempVars, organizationVars, serverVars, commVars, activityBlockchainVars >>

\* Add data
Post(m) == cyberPool' = Append(cyberPool, m)

\* Send message to the channel
Send(m) == channel' = channel \cup {m}
RecvInadditionSend(c, m) == channel' = ( channel \ {c} ) \cup {m}

\* Transactions to the identity blockchain
blockchainPolicyTxn(r, cid, cinfo) ==
  /\ atxPool' = atxPool \cup {[type |-> ATX_CYBER_THREAT, who |-> r, data |-> << cid, cinfo >>]}

\* Verification function
InsertCTI(id, info) ==
  TRUE
  
\* Initial states
InitTemp ==
  /\ cyberPool = <<>>
  /\ cyberSource = CYBERTHREATS

InitOrganization ==
  /\ oState = [ o \in Organization |-> O_Waiting ]
  /\ oBuffer = [ o \in Organization |-> <<>> ]
  
InitServer ==
  /\ sState = [ s \in Server |-> S_Waiting ]
  /\ sBuffer = [ s \in Server |-> <<>> ]

InitIdentityBlockchain ==
  /\ atxPool = {}
  /\ ablockTx = {}
 
Init ==
  /\ InitTemp /\ InitOrganization /\ InitServer 
  /\ InitIdentityBlockchain /\ channel = {} 

setup == 
  \E <<cid, cinfo>> \in cyberSource:
    LET
      id == cid
      info == cinfo
    IN
    /\ cyberSource' = cyberSource \ {<<cid, cinfo>>}
    /\ Post(<<id, info>>)
    /\ UNCHANGED << organizationVars, serverVars, commVars, activityBlockchainVars >>

Preparation(o) ==
  /\ oState[o] = O_Waiting
  /\ IF Len(cyberPool) > 0 THEN
       /\ oBuffer' = [ oBuffer EXCEPT ![o] = Head(cyberPool) ]
       /\ oState' = [ oState EXCEPT ![o] = O_Insert ]
       /\ cyberPool' = Tail(cyberPool)
       /\ UNCHANGED << cyberSource, serverVars, commVars, activityBlockchainVars >>
     ELSE
       /\ oState' = [ oState EXCEPT ![o] = O_Final ]
       /\ UNCHANGED << tempVars, oBuffer, serverVars, commVars, activityBlockchainVars >>
             
InsertCyberInformation(o) ==
  /\ oState[o] = O_Insert
  /\ \E s \in Server :
    /\ sState[s] = S_Waiting
    /\ LET 
         m == oBuffer[o]
       IN 
         Send([src |-> o, dst |-> s, type |-> M_Insertion, data |-> <<o, m[1], m[2]>>])
  /\ oState' = [ oState EXCEPT ![o] = O_AssociatePolicy ]
  /\ UNCHANGED << tempVars, oBuffer, serverVars, activityBlockchainVars >>

Insertion(s) ==
  \E c \in channel:
    /\ c.dst = s
    /\ c.type = M_Insertion
    /\ sState[s] = S_Waiting
    /\ IF InsertCTI(c.data[2], c.data[3]) THEN
         /\ RecvInadditionSend(c, [src |-> s, dst |-> c.data[1], type |-> M_OK, data |-> << >> ])
         /\ UNCHANGED << tempVars, organizationVars, serverVars, activityBlockchainVars >>
       ELSE
         /\ RecvInadditionSend(c, [src |-> s, dst |-> c.data[1], type |-> M_NO, data |-> << >> ])
         /\ UNCHANGED << tempVars, organizationVars, serverVars, activityBlockchainVars >>
           
 InsertionFailed(o) ==
  \E c \in channel:
    /\ c.dst = o
    /\ c.type = M_NO
    /\ oState' = [ oState EXCEPT ![o] = O_Final ]
    /\ UNCHANGED << tempVars, oBuffer, serverVars, commVars, activityBlockchainVars >> 
 
 PolicyAssociation(o) ==
  \E c \in channel:
    /\ c.dst = o
    /\ c.type = M_OK
    /\ oState' = [ oState EXCEPT ![o] = O_Waiting ]
    /\ LET 
         m == oBuffer[o]
         pid == POLICY_ID
       IN 
         blockchainPolicyTxn(o, m[1], pid)
    /\ UNCHANGED << tempVars, oBuffer, serverVars, commVars, ablockTx >> 
           
 ConfirmReceipt == 
  \E receiptTx \in atxPool:
    /\ receiptTx.type = ATX_CYBER_THREAT 
    /\ atxPool' = atxPool \ { receiptTx }
    /\ ablockTx' = ablockTx \cup { receiptTx }
    /\ UNCHANGED << tempVars, organizationVars, serverVars, commVars >>
    
Termination ==
  /\ \A o \in Organization : oState[o] = O_Final
  /\ UNCHANGED vars
  
Next == 
  \/ setup
  \/ \E o \in Organization :
       \/ Preparation(o) \/ InsertCyberInformation(o) \/ InsertionFailed(o) \/ PolicyAssociation(o)
  \/ \E s \in Server :
       \/ Insertion(s)  
  \/ ConfirmReceipt
  \/ Termination
  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Sat Feb 13 16:41:31 CET 2021 by nachi
\* Created Sat Feb 13 13:57:07 CET 2021 by nachi
