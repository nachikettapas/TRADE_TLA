--------------------------- MODULE function_test ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

\* Verification function
getMetaData(txid, uid) ==
  \E tx \in ablockTx:
    /\ tx.type = txid
    /\ tx.who = uid
=============================================================================
\* Modification History
\* Last modified Sat Feb 13 18:04:23 CET 2021 by nachi
\* Created Sat Feb 13 18:02:53 CET 2021 by nachi
