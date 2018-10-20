------------------------ MODULE TestLinearizability ------------------------
PossibleResponses(e) == {}

Matches(H, i, j) == FALSE

L == INSTANCE Linearizability

H3 == <<
    [op|->"E", val|->"x", proc|->"A"],
    [op|->"D", proc|-> "B"],
    [op|->"Ok", val|->"x", proc|->"B"]
>>

TestCollect == L!Collect({
    {[op|->"Ok", proc|->"A"]},
    {[op|->"Ok", proc|->"B", val|->"x"], [op|->"Ok", proc|->"B", val|->"y"]}}) = 
    {
        {[op|->"Ok", proc|->"A"], [op|->"Ok", proc|->"B", val|->"x"]},
        {[op|->"Ok", proc|->"A"], [op|->"Ok", proc|->"B", val|->"y"]}
    }

TestInvocationsWithoutResponse == L!InvocationsWithoutResponses(H3) = {[op|->"E", val|->"x", proc|->"A"]}

Test == TestInvocationsWithoutResponse

\* The only possible extension for H3 is completing the enqueue
ExtH3 == L!Extensions(H3) = {[op|->"Ok", proc|->"A"]}


=============================================================================
\* Modification History
\* Last modified Sat Oct 20 14:11:55 PDT 2018 by lhochstein
\* Created Sat Oct 20 13:43:05 PDT 2018 by lhochstein
