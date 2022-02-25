----------------------- MODULE organization_creation -----------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE patchPool
CONSTANT REGKEYS
VARIABLE regKey

\* Organization profile constants
CONSTANT PROFILE_ID
CONSTANT PROFILE

\* Organization profile constants
CONSTANT BLOCKCHAIN_ID
CONSTANT BLOCKCHAIN_PROFILE
CONSTANT BLOCKCHAIN_ADDRESS

\* Organization variables
CONSTANT Organization
VARIABLE oState
VARIABLE oBuffer

\* Organization states
CONSTANT O_Waiting, O_Register, O_VerificationWaiting, O_ReceiveBlockchainIdentity, O_Final

\* Registrar variables
CONSTANT Registrar
VARIABLE rState
VARIABLE rBuffer

\* Registrar states
CONSTANT R_Waiting, R_Verification, R_BlockchainIdentityCreation, R_SaveMapping, R_Final 

\* Identity blockchain variables
VARIABLE itxPool
VARIABLE iblockTx
CONSTANT TX_ORIGINAL, TX_BLOCKCHAIN

\* Communication channel
VARIABLE channel
CONSTANT M_Verification, M_OK, M_NO, M_Identity, M_Request, M_IdentityCreation

tempVars == << patchPool, regKey >>
organizationVars == << oState, oBuffer >>
registrarVars == << rState, rBuffer >>
commVars == << channel >>
identityBlockchainVars == << itxPool, iblockTx >>

vars == << tempVars, organizationVars, registrarVars, commVars, identityBlockchainVars >>

\* Add data
Post(m) == patchPool' = Append(patchPool, m)

\* Send message to the channel
Send(m) == channel' = channel \cup {m}
RecvInadditionSend(c, m) == channel' = ( channel \ {c} ) \cup {m}

\* Transactions to the identity blockchain
blockchainIdentityTxn(r, bid, bprofile) ==
  /\ itxPool' = itxPool \cup {[type |-> TX_BLOCKCHAIN, who |-> r, data |-> << bid, bprofile >>]}

\* Verification function
VerifyProfile(id, profile) ==
  TRUE
  
\* Initial states
InitTemp ==
  /\ patchPool = <<>>
  /\ regKey = REGKEYS

InitOrganization ==
  /\ oState = [ o \in Organization |-> O_Waiting ]
  /\ oBuffer = [ o \in Organization |-> <<>> ]
  
InitRegistrar ==
  /\ rState = [ r \in Registrar |-> R_Waiting ]
  /\ rBuffer = [ r \in Registrar |-> <<>> ]

InitIdentityBlockchain ==
  /\ itxPool = {}
  /\ iblockTx = {}
 
Init ==
  /\ InitTemp /\ InitOrganization /\ InitRegistrar 
  /\ InitIdentityBlockchain /\ channel = {} 

setup == 
  \E <<oid, oprofile>> \in regKey:
    LET
      id == oid
      profile == oprofile
    IN
    /\ regKey' = regKey \ {<<oid, oprofile>>}
    /\ Post(<<id, profile>>)
    /\ UNCHANGED << organizationVars, registrarVars, commVars, identityBlockchainVars >>
    
Preparation(o) ==
  /\ oState[o] = O_Waiting
  /\ Len(patchPool) > 0
  /\ oBuffer' = [ oBuffer EXCEPT ![o] = Head(patchPool) ]
  /\ oState' = [ oState EXCEPT ![o] = O_Register ]
  /\ patchPool' = Tail(patchPool)
  /\ UNCHANGED << regKey, registrarVars, commVars, identityBlockchainVars >> 
  
Register(o) ==
  /\ oState[o] = O_Register
  /\ \E r \in Registrar :
    /\ rState[r] = R_Waiting
    /\ LET 
         m == oBuffer[o]
       IN 
         Send([src |-> o, dst |-> r, type |-> M_Verification, data |-> <<o, m[1], m[2]>>])
  /\ oState' = [ oState EXCEPT ![o] = O_ReceiveBlockchainIdentity ]
  /\ UNCHANGED << tempVars, oBuffer, registrarVars, identityBlockchainVars >> 

Verification(r) ==
  \E c \in channel:
    /\ c.dst = r
    /\ c.type = M_Verification
    /\ rState[r] = R_Waiting
    /\ IF VerifyProfile(c.data[2], c.data[3]) THEN
         /\ rBuffer' = [ rBuffer EXCEPT ![r] = c.data ]
         /\ rState' = [ rState EXCEPT ![r] = R_BlockchainIdentityCreation ]
         /\ RecvInadditionSend(c, [src |-> r, dst |-> c.data[1], type |-> M_OK, data |-> << >> ])
         /\ UNCHANGED << tempVars, organizationVars, identityBlockchainVars >>
       ELSE
         /\ rState' = [ rState EXCEPT ![r] = R_Waiting ]
         /\ RecvInadditionSend(c, [src |-> r, dst |-> c.data[1], type |-> M_NO, data |-> << >> ])
         /\ UNCHANGED << tempVars, organizationVars, rBuffer, identityBlockchainVars >>
           
 VerificationFailed(o) ==
  \E c \in channel:
    /\ c.dst = o
    /\ c.type = M_NO
    /\ oState' = [ oState EXCEPT ![o] = O_Final ]
    /\ UNCHANGED << tempVars, oBuffer, registrarVars, commVars, identityBlockchainVars >> 
 
 CreateIdentity(o) ==
  \E c \in channel:
    /\ c.dst = o
    /\ c.type = M_OK
    /\ oState' = [ oState EXCEPT ![o] = O_ReceiveBlockchainIdentity ]
    /\ LET 
         m == oBuffer[o]
       IN 
         RecvInadditionSend(c, [src |-> o, dst |-> c.src, type |-> M_IdentityCreation, data |-> <<o, m[1], m[2]>>])
    /\ UNCHANGED << tempVars, oBuffer, registrarVars, identityBlockchainVars >> 
 
 BlockchainIdentityCreation(r) ==
   \E c \in channel:
     /\ c.dst = r
     /\ c.type = M_IdentityCreation
     /\ rState[r] = R_BlockchainIdentityCreation
     /\ rState' = [ rState EXCEPT ![r] = R_SaveMapping ]
     /\ c.data[1] = rBuffer[r][1]
     /\ blockchainIdentityTxn( r, BLOCKCHAIN_ID, BLOCKCHAIN_PROFILE )
     /\ channel' = channel \ {c}
     /\ UNCHANGED << tempVars, organizationVars, rBuffer, iblockTx >>  

 SaveMapping(r) ==
  /\ rState[r] = R_SaveMapping
  /\ LET
       data == rBuffer[r]
     IN
       Send([src |-> r, dst |-> data[1], type |-> M_Identity, data |-> << BLOCKCHAIN_ADDRESS >> ])
  /\ rState' = [ rState EXCEPT ![r] = R_Final ]
  /\ UNCHANGED << tempVars, organizationVars, rBuffer, identityBlockchainVars >>

 ReceiveBlockchainIdentity(o) ==
  \E c \in channel:
    /\ c.dst = o
    /\ c.type = M_Identity
    /\ oState[o] = O_ReceiveBlockchainIdentity
    /\ IF Len(patchPool) = 0 THEN
         oState' = [ oState EXCEPT ![o] = O_Final ]
       ELSE
         oState' = [ oState EXCEPT ![o] = O_Register ]
    /\ UNCHANGED << tempVars, oBuffer, registrarVars, commVars, identityBlockchainVars >> 
          
 ConfirmReceipt == 
  \E receiptTx \in itxPool:
    /\ ( receiptTx.type = TX_ORIGINAL \/ receiptTx.type = TX_BLOCKCHAIN )
    /\ itxPool' = itxPool \ { receiptTx }
    /\ iblockTx' = iblockTx \cup { receiptTx }
    /\ UNCHANGED << tempVars, organizationVars, registrarVars, commVars>>
    
Termination ==
  /\ \A o \in Organization : oState[o] = O_Final
  /\ UNCHANGED vars
  
Next == 
  \/ setup
  \/ \E o \in Organization :
       \/ Preparation(o) \/ Register(o) \/ VerificationFailed(o) \/ ReceiveBlockchainIdentity(o) \/ CreateIdentity(o)
  \/ \E r \in Registrar :
       \/ Verification(r) \/ BlockchainIdentityCreation(r) \/ SaveMapping(r) 
  \/ ConfirmReceipt
  \/ Termination
  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================