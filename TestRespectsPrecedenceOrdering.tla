------------------- MODULE TestRespectsPrecedenceOrdering -------------------
EXTENDS LinQueue

L == INSTANCE Linearizability

TestNoChange ==
\* Two overlapping 
    LET H == <<
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"D", proc|-> "B"],
            [op|->"Ok", val|->"x", proc|->"B"],
            [op|->"Ok", proc|->"A"]>>
    IN L!RespectsPrecedenceOrdering(H, H)

\* This should be false
TestReverseOrderingViolatesPrecedence == 
    LET H1 == <<
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"Ok", proc|->"A"],
            [op|->"D", proc|-> "B"],
            [op|->"Ok", val|->"x", proc|->"B"]>>
        H2 == <<
            [op|->"D", proc|-> "B"],
            [op|->"Ok", val|->"x", proc|->"B"],
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"Ok", proc|->"A"]
        >>
    IN \/ L!RespectsPrecedenceOrdering(H1, H2)
       \/ L!RespectsPrecedenceOrdering(H2, H1)

TestMovingOverlapIsFine ==
    \* This is Figure 1, H2(b)
    LET H1 == <<
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"Ok", proc|->"A"],
            [op|->"E", val|->"y", proc|->"B"],
            [op|->"D", proc|-> "A"],
            [op|->"Ok", proc|->"B"],
            [op|->"Ok", val|->"y", proc|->"A"]>>
        H2 == <<
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"Ok", proc|->"A"],
            [op|->"E", val|->"y", proc|->"B"],
            [op|->"Ok", proc|->"B"],
            [op|->"D", proc|-> "A"],
            [op|->"Ok", val|->"y", proc|->"A"]>>
        H3 == <<
            [op|->"E", val|->"x", proc|->"A"],
            [op|->"Ok", proc|->"A"],
            [op|->"D", proc|-> "A"],
            [op|->"Ok", val|->"y", proc|->"A"],
            [op|->"E", val|->"y", proc|->"B"],
            [op|->"Ok", proc|->"B"]>>
    IN /\ L!RespectsPrecedenceOrdering(H1, H2)
       /\ L!RespectsPrecedenceOrdering(H1, H3)
       /\ ~L!RespectsPrecedenceOrdering(H2, H3)

=============================================================================
\* Modification History
\* Last modified Sun Oct 21 10:25:30 PDT 2018 by lhochstein
\* Created Sun Oct 21 10:20:03 PDT 2018 by lhochstein
