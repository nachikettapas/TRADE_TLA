------------------------------ MODULE sharing ------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLE patchPool
VARIABLE pTime

CONSTANT NODE_TYPE

CONSTANT Transporter
VARIABLE tState
VARIABLE tBuffer

CONSTANT T_Waiting, T_Delivering, T_VerificationWaiting, T_ReceiptWaiting, T_MiningWaiting, T_Final

CONSTANT Recipient
VARIABLE rState
VARIABLE rBuffer

CONSTANT R_Waiting, R_Verifying, R_RequestWaiting, R_Paying, R_Final

VARIABLE balance
VARIABLE txPool
VARIABLE blockTx
CONSTANT TX_In, TX_Out

VARIABLE channel
CONSTANT M_Package, M_OK, M_NO, M_ReceiptRequest

CONSTANT KHASH
CONSTANT EPAYLOAD
CONSTANT DPAYLOAD
CONSTANT REGKEYS
CONSTANT SIGNVERIFY
CONSTANT GETPUBLICKEY
VARIABLE checksumId
VARIABLE checksum

VARIABLE regKey

CONSTANT Fee
CONSTANT InitBalance

providerVars == << patchPool, regKey, pTime, checksum, checksumId >>
transporterVars == << tState, tBuffer >>
recipientVars == << rState, rBuffer >>
commVars == << channel >>
blockchainVars == << txPool, blockTx, balance >>

vars == << providerVars, transporterVars, recipientVars, commVars, blockchainVars >>

Post(m) == patchPool' = Append(patchPool, m)

VerifyMeta(p, tu, cid) == checksum[cid] = << tu, p >>

Send(m) == channel'= channel \cup {m}
RecvInadditionSend(c, m) == channel' = ( channel \ {c} ) \cup {m}

Pledge(r, keyhash, sign, beneficiary) ==
  txPool' = txPool \cup {[ type |-> TX_In, who |-> r, data |-> <<keyhash, sign, beneficiary>>]}
Proof(t, key) ==
  txPool' = txPool \cup {[ type |-> TX_Out, who |-> t, data |-> <<key>>]}
  
ValidateReceipt(t, receipt) ==
  t = receipt[3]
  
InitProvider ==
  /\ patchPool = <<>>
  /\ pTime = 0
  /\ checksumId = 0
  /\ checksum = [ k \in checksumId .. (checksumId + Cardinality(REGKEYS) - 1) |-> <<>> ]
  /\ regKey = REGKEYS
  
InitTransporter ==
  /\ tState = [ t \in Transporter |-> T_Waiting ]
  /\ tBuffer = [ t \in Transporter |-> <<>> ]

InitRecipient ==
  /\ rState = [ r \in Recipient |-> R_Waiting ]
  /\ rBuffer = [ r \in Recipient |-> <<>> ]

InitBlockchain ==
  /\ txPool = {}
  /\ blockTx = {}
  /\ balance = [ c \in Transporter \cup Recipient |-> InitBalance ]
  
Init ==
  /\ InitProvider /\ InitTransporter /\ InitRecipient /\ InitBlockchain /\ channel = {}
  
Preparation ==
  \E <<pk, h, sign>> \in regKey:
    LET
      keyHash == h
      payload == EPAYLOAD[pk]
      target_node == NODE_TYPE
    IN
      /\ regKey' = regKey \ {<<pk, h, sign>>}
      /\ Post(<<pk, keyHash, payload, target_node, pTime, checksumId, sign>>)
      /\ checksum' = [ checksum EXCEPT ![checksumId] = <<pTime, payload>> ]
      /\ checksumId' = checksumId + 1
      /\ pTime' = pTime + 1 
      /\ UNCHANGED << transporterVars, recipientVars, commVars, blockchainVars >>
      
Pickup(t) ==
  /\ tState[t] = T_Waiting
  /\ Len(patchPool) > 0
  /\ tBuffer' = [ tBuffer EXCEPT ![t] = Head(patchPool) ]
  /\ tState' = [ tState EXCEPT ![t] = T_Delivering ]
  /\ patchPool' = Tail(patchPool)
  /\ UNCHANGED << regKey, pTime, checksum, checksumId, recipientVars, commVars, blockchainVars >>
  
Delivery(t) ==
  /\ tState[t] = T_Delivering
  /\ \E r \in Recipient:
    /\ rState[r] = R_Waiting
    /\ LET m == tBuffer[t] IN
         Send([ src |-> t, dst |-> r, type |-> M_Package, data |-> << m[2], m[3], m[4], m[5], m[6], m[7] >>])
  /\ tState' = [ tState EXCEPT ![t] = T_VerificationWaiting ]
  /\ UNCHANGED << providerVars, tBuffer, recipientVars, blockchainVars >>

Verification(r) ==
  \E c \in channel:
    /\ c.dst = r
    /\ c.type = M_Package
    /\ rState[r] = R_Waiting
    /\ LET
         recvPayload == c.data[2]
         recvTime == c.data[4] 
         recvChecksumId == c.data[5]
       IN
         IF VerifyMeta(recvPayload, recvTime, recvChecksumId) /\ r \in c.data[3] THEN
           /\ rState' = [ rState EXCEPT ![r] = R_RequestWaiting ]
           /\ rBuffer' = [ rBuffer EXCEPT ![r] = c.data ]
           /\ RecvInadditionSend(c, [src |-> r, dst |-> c.src, type |-> M_OK, data |-> <<>>])
           /\ UNCHANGED << providerVars, transporterVars, blockchainVars >>
         ELSE
           /\ RecvInadditionSend(c, [src |-> r, dst |-> c.src, type |-> M_NO, data |-> <<>>])
           /\ UNCHANGED << providerVars, transporterVars, recipientVars, blockchainVars >>

RejectPackage(r) ==
  \E c \in channel:
    /\ c.dst = r
    /\ c.type = M_Package
    /\ rState[r] /= R_Waiting
    /\ RecvInadditionSend(c, [src |-> r, dst |-> c.src, type |-> M_NO, data |-> <<>>])
    /\ UNCHANGED << providerVars, transporterVars, recipientVars, blockchainVars >>

ReceiptRequest(t) ==
  \E c \in channel:
    /\ c.dst = t
    /\ c.type = M_OK
    /\ tState' = [ tState EXCEPT ![t] = T_ReceiptWaiting ]
    /\ LET
         keyHash == tBuffer[t][2]
         sign == tBuffer[t][7]
       IN
         RecvInadditionSend(c, [src |-> t, dst |-> c.src, type |-> M_ReceiptRequest, data |-> <<keyHash, sign>>])
    /\ UNCHANGED << providerVars, tBuffer, recipientVars, blockchainVars >>

TryAnother(t) ==
  \E c \in channel:
    /\ c.dst = t
    /\ c.type = M_NO
    /\ tState[t] = T_VerificationWaiting
    /\ tState' = [ tState EXCEPT ![t] = T_Delivering ]
    /\ channel' = channel \ {c}
    /\ UNCHANGED << providerVars, tBuffer, recipientVars, blockchainVars >>
    
Receipt(r) ==
  \E c \in channel:
    /\ c.dst = r
    /\ c.type = M_ReceiptRequest
    /\ rState[r] = R_RequestWaiting
    /\ rState' = [ rState EXCEPT ![r] = R_Paying ]
    /\ c.data[1] = rBuffer[r][1] 
    /\ Pledge(r, c.data[1], c.data[2], c.src) 
    /\ channel' = channel \ {c}
    /\ UNCHANGED << balance, blockTx, rBuffer, providerVars, transporterVars >>
    
KeyRedeem(t) ==
  \E tx \in blockTx:
    /\ tState[t] /= T_Waiting
    /\ tState[t] /= T_Final
    /\ LET 
         keyHash == tBuffer[t][2] 
       IN
         tx.data[1] = keyHash
    /\ ValidateReceipt(t, tx.data)
    /\ LET
         pu == GETPUBLICKEY[tBuffer[t][1]]
       IN
         Proof(t, pu)
    /\ tState' = [ tState EXCEPT ![t] = T_MiningWaiting ]
    /\ UNCHANGED << balance, blockTx, tBuffer, providerVars, commVars, recipientVars >>

ConfirmReceipt ==
  \E receiptTx \in txPool:
    /\ receiptTx.type = TX_In
    /\ LET 
         r == receiptTx.who 
       IN
         balance[r] >= Fee
    /\ txPool' = txPool \ {receiptTx}
    /\ blockTx' = blockTx \cup {receiptTx}
    /\ UNCHANGED << balance, providerVars, transporterVars, commVars, recipientVars >>

ConfirmProof ==
  \E proofTx \in txPool : \E receiptTx \in blockTx :
    LET 
      r == receiptTx.who
      t == proofTx.who
      pu == proofTx.data[1] 
    IN
      /\ receiptTx.type = TX_In
      /\ proofTx.type = TX_Out
      /\ pu \in DOMAIN KHASH
      /\ receiptTx.data[1] = KHASH[pu]
      /\ SIGNVERIFY[receiptTx.data[2]] = pu
      /\ rBuffer[r][1] = receiptTx.data[1]
      /\ DPAYLOAD[pu] = rBuffer[r][2]
      /\ tState' = [ tState EXCEPT ![t] = T_Final ]
      /\ rState' = [ rState EXCEPT ![r] = R_Final ]
      /\ txPool' = txPool \ {proofTx}
      /\ blockTx' = blockTx \cup {proofTx}
      /\ LET
           beneficiary == receiptTx.data[3]
         IN
           balance' = [ balance EXCEPT ![beneficiary] = balance[beneficiary] + Fee, 
                                       ![r] = balance[r] - Fee ]       
      /\ UNCHANGED << tBuffer, rBuffer, providerVars, commVars >>

FaithfulDelivery ==
  \/ \A r \in Recipient : rState[r] = R_Final
  \/ Cardinality({r \in Recipient : rState[r] = R_Final}) = Cardinality(REGKEYS)
  
AuthenticatedOrigin == 
  \A q \in {r \in Recipient : rState[r] = R_Final} : 
  rBuffer[q][2] \in {EPAYLOAD[k] : k \in DOMAIN EPAYLOAD}
  
RECURSIVE Sum(_,_)
Sum(f,S) == 
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})
    
TotalBalanceInvariance ==
  Sum(balance, DOMAIN balance) = InitBalance * Cardinality(Transporter \cup Recipient)
  
NoUnpaidFee ==
  \A r \in Recipient:
    /\ rState[r] = R_Final => balance[r] <= InitBalance - Fee

NoDoubleIncome ==
  \A bTx \in blockTx : \A pTx \in txPool : bTx.data /= pTx.data
  
PackageUniqueness ==
  \/ Cardinality(Recipient) = Cardinality({rBuffer[r][1]:r \in Recipient}) 
  
Termination ==
  /\ FaithfulDelivery
  /\ AuthenticatedOrigin
  /\ PackageUniqueness
  /\ Print(balance, TRUE)
  /\ Print(checksum, TRUE)
  /\ UNCHANGED vars
  
Next ==
  \/ Preparation
  \/ \E t \in Transporter:
    \/ Pickup(t) \/ Delivery(t) \/ KeyRedeem(t)
    \/ ReceiptRequest(t) \/ TryAnother(t)
  \/ \E r \in Recipient:
    \/ Verification(r) \/ Receipt(r) \/ RejectPackage(r)
  \/ ConfirmReceipt \/ ConfirmProof
  \/ Termination
  
Spec == Init /\ [][Next]_vars       
=============================================================================
\* Modification History
\* Last modified Sat Feb 13 11:10:20 CET 2021 by nachi
\* Created Thu Feb 11 13:06:11 CET 2021 by nachi
