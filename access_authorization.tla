------------------------ MODULE access_authorization ------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE accessPool
CONSTANT ACCESSREQUESTS
VARIABLE accessSource
CONSTANT ORGANIZATION
CONSTANT CID
CONSTANT CINFO
VARIABLE ctiInfo
CONSTANT BADGEID
CONSTANT BADGE

\* Organization variables
CONSTANT Consumer
VARIABLE cState
VARIABLE cBuffer

\* Organization states
CONSTANT C_Waiting, C_RequestMetaData, C_CreateBadge, C_RequestToken, C_AccessServer, C_ValidateAccess, C_Final

\* Registrar variables
CONSTANT Server
VARIABLE sState
VARIABLE sBuffer

\* Registrar states
CONSTANT S_Waiting, S_Final 

\* Identity blockchain variables
VARIABLE itxPool
VARIABLE iblockTx
CONSTANT ITX_BADGE

\* Activity blockchain variables
VARIABLE atxPool
VARIABLE ablockTx
CONSTANT ATX_CYBER_THREAT, ATX_ACCESS_TOKEN
CONSTANT TOKEN

\* Communication channel
VARIABLE channel
CONSTANT M_Access, M_OK, M_NO

tempVars == << accessPool, accessSource, ctiInfo >>
consumerVars == << cState, cBuffer >>
serverVars == << sState, sBuffer >>
commVars == << channel >>
identityBlockchainVars == << itxPool, iblockTx >>
activityBlockchainVars == << atxPool, ablockTx >>

vars == << tempVars, consumerVars, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >>

\* Add data
Post(m) == accessPool' = Append(accessPool, m)

\* Send message to the channel
Send(m) == channel' = channel \cup {m}
RecvInadditionSend(c, m) == channel' = ( channel \ {c} ) \cup {m}

\* Transactions to the identity blockchain
blockchainIdentityTxn(r, bgid, badge) ==
  /\ itxPool' = itxPool \cup {[type |-> ITX_BADGE, who |-> r, data |-> << bgid, badge >>]}
blockchainActivityTxn(r, bgid) ==
  /\ atxPool' = atxPool \cup {[type |-> ATX_ACCESS_TOKEN, who |-> r, data |-> << bgid, TOKEN >>]}

VerifyAccess(token, cid) ==
  TRUE
 
ValidateBadge(bgid) ==
  FALSE
   
\* Initial states
InitTemp ==
  /\ accessPool = <<>>
  /\ accessSource = ACCESSREQUESTS
  /\ ctiInfo = [ c \in Consumer |-> <<>> ]

InitConsumer ==
  /\ cState = [ c \in Consumer |-> C_Waiting ]
  /\ cBuffer = [ c \in Consumer |-> <<>> ]
  
InitServer ==
  /\ sState = [ s \in Server |-> S_Waiting ]
  /\ sBuffer = [ s \in Server |-> <<>> ]

InitIdentityBlockchain ==
  /\ itxPool = {}
  /\ iblockTx = {}

InitActivityBlockchain ==
  /\ atxPool = {}
  /\ ablockTx = {[type |-> ATX_CYBER_THREAT, who |-> ORGANIZATION, data |-> << CID, CINFO >>]}
 
Init ==
  /\ InitTemp /\ InitConsumer /\ InitServer 
  /\ InitIdentityBlockchain /\ InitActivityBlockchain /\ channel = {} 

setup == 
  \E <<aid, resource>> \in accessSource:
    LET
      id == aid
      profile == resource
    IN
    /\ accessSource' = accessSource \ {<<aid, resource>>}
    /\ Post(<<id, profile>>)
    /\ UNCHANGED << ctiInfo, consumerVars, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >>
    
Preparation(c) ==
  /\ cState[c] = C_Waiting
  /\ Len(accessPool) > 0
  /\ cBuffer' = [ cBuffer EXCEPT ![c] = Head(accessPool) ]
  /\ cState' = [ cState EXCEPT ![c] = C_RequestMetaData ]
  /\ accessPool' = Tail(accessPool)
  /\ UNCHANGED << accessSource, ctiInfo, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >> 
  
RequestMetaData(c) ==
  \E tx \in ablockTx:
    /\ cState[c] = C_RequestMetaData
    /\ tx.type = ATX_CYBER_THREAT
    /\ tx.who = ORGANIZATION
    /\ ctiInfo' = [ ctiInfo EXCEPT ![c] = tx.data ]
    /\ cState' = [ cState EXCEPT ![c] = C_CreateBadge ]
    /\ UNCHANGED << cBuffer, accessPool, accessSource, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >>

 CreateBadge(c) == 
   /\ cState[c] = C_CreateBadge
   /\ LET
        bgid == BADGEID
        badge == BADGE
      IN
        blockchainIdentityTxn(c, bgid, badge)
   /\ cState' = [ cState EXCEPT ![c] = C_RequestToken ]
   /\ UNCHANGED << ctiInfo, iblockTx, cBuffer, accessPool, accessSource, serverVars, commVars, activityBlockchainVars >>
 
 RequestToken(c) == 
   /\ cState[c] = C_RequestToken
   /\ LET
        bgid == BADGEID
      IN
        IF ValidateBadge(bgid) THEN
          /\ blockchainActivityTxn(c, bgid)
          /\ cState' = [ cState EXCEPT ![c] = C_AccessServer ]
          /\ UNCHANGED << ctiInfo, ablockTx, cBuffer, accessPool, accessSource, serverVars, commVars, identityBlockchainVars >>
        ELSE
          /\ cState' = [ cState EXCEPT ![c] = C_Final ]
          /\ UNCHANGED << ctiInfo, cBuffer, accessPool, accessSource, serverVars, commVars, activityBlockchainVars, identityBlockchainVars >>
    
 AccessServer(c) ==
   \E s \in Server :
     /\ cState[c] = C_AccessServer
     /\ LET 
          token == TOKEN
          cid == CID
        IN 
          Send([src |-> c, dst |-> s, type |-> M_Access, data |-> <<token, cid>>])
   /\ cState' = [ cState EXCEPT ![c] = C_ValidateAccess ]
   /\ UNCHANGED << ctiInfo, ablockTx, cBuffer, accessPool, accessSource, serverVars, atxPool, identityBlockchainVars >>
 
 ValidateRequest(s) ==
   \E c \in channel:
    /\ c.dst = s
    /\ c.type = M_Access
    /\ sState[s] = S_Waiting
    /\ IF VerifyAccess(c.data[1], c.data[2]) THEN
         /\ RecvInadditionSend(c, [src |-> s, dst |-> c.src, type |-> M_OK, data |-> << >> ])
       ELSE
         /\ RecvInadditionSend(c, [src |-> s, dst |-> c.src, type |-> M_NO, data |-> << >> ])
    /\ sState' = [ sState EXCEPT ![s] = S_Waiting ]
    /\ UNCHANGED << tempVars, consumerVars, sBuffer, identityBlockchainVars, activityBlockchainVars >>
                    
 IConfirmReceipt == 
  \E receiptTx \in itxPool:
    /\ receiptTx.type = ITX_BADGE
    /\ itxPool' = itxPool \ { receiptTx }
    /\ iblockTx' = iblockTx \cup { receiptTx }
    /\ UNCHANGED << consumerVars, serverVars, commVars, accessPool, accessSource, ctiInfo, activityBlockchainVars >>

 AConfirmReceipt == 
  \E receiptTx \in atxPool:
    /\ receiptTx.type = ATX_ACCESS_TOKEN 
    /\ atxPool' = atxPool \ { receiptTx }
    /\ ablockTx' = ablockTx \cup { receiptTx }
    /\ UNCHANGED << consumerVars, serverVars, commVars, identityBlockchainVars, accessPool, accessSource, ctiInfo >>
 
 VerificationFailed(c) ==
  \E ch \in channel:
    /\ ch.dst = c
    /\ ch.type = M_NO
    /\ cState' = [ cState EXCEPT ![c] = C_Final ]
    /\ UNCHANGED << tempVars, cBuffer, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >> 
 
 AccessCTI(c) ==
  \E ch \in channel:
    /\ ch.dst = c
    /\ ch.type = M_OK
    /\ cState' = [ cState EXCEPT ![c] = C_Final ]
    /\ UNCHANGED << tempVars, cBuffer, serverVars, commVars, identityBlockchainVars, activityBlockchainVars >>     

Termination ==
  /\ \A c \in Consumer : cState[c] = C_Final
  /\ UNCHANGED vars
  
Next == 
  \/ setup
  \/ \E c \in Consumer :
       \/ Preparation(c) \/ RequestMetaData(c) \/ CreateBadge(c) \/ RequestToken(c) 
       \/ AccessServer(c) \/ VerificationFailed(c) \/ AccessCTI(c) 
  \/ \E s \in Server :
       \/ ValidateRequest(s)  
  \/ IConfirmReceipt
  \/ AConfirmReceipt
  \/ Termination
  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Wed Feb 17 20:16:21 CET 2021 by nachi
\* Created Sat Feb 13 14:59:13 CET 2021 by nachi
