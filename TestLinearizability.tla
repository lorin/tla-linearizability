------------------------ MODULE TestLinearizability ------------------------
EXTENDS Naturals 


opInvocations == {"E", "D"}
opResponse == "Ok"

values == {"x", "y"} 

PossibleResponses(e) ==
    CASE e.op = "E" -> {[op|->"Ok", proc|->e.proc]}
      [] e.op = "D" -> [op:{"Ok"}, proc:{e.proc}, val:values]

IsLegalSequentialHistory(H) == FALSE \* TODO, this will be defined elsewhere

IsInvocation(e) == e.op \in opInvocations

Matches(H, i, j) ==
    /\ H[i].proc = H[j].proc
    /\ H[i].op \in opInvocations
    /\ H[j].op = opResponse
    /\ ~\E k \in (i+1)..(j-1) : H[k].proc = H[i].proc

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

TestExtensions ==
    LET H == <<[op|->"E", val|->"x", proc|->"A"], [op|->"D", proc|-> "B"]>>
    IN L!Extensions(H) = {
        {[op|->"Ok", proc|->"A"], [op|->"Ok", proc|->"B", val|->"x"]},
        {[op|->"Ok", proc|->"A"], [op|->"Ok", proc|->"B", val|->"y"]}
    }
    

TestExtendedHistories ==
    LET H == <<[op|->"E", val|->"x", proc|->"A"], [op|->"D", proc|-> "B"]>>
    IN L!ExtendedHistories(H) = {
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"]>>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "y", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"], [op |-> "Ok", val |-> "x", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"], [op |-> "Ok", val |-> "y", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"], [op |-> "Ok", proc |-> "A"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "y", proc |-> "B"], [op |-> "Ok", proc |-> "A"] >>
}

TestSubseq == L!Subseq(<<"a", "b", "c", "d", "e">>, {2,3,5}) = <<"b", "c", "e">>

TestSubsequences == L!Subsequences(<<"a", "b", "c">>) = {
 << >>,
 <<"a">>,
 <<"b">>,
 <<"c">>,
 <<"a","b">>,
 <<"a","c">>,
 <<"b","c">>,
 <<"a","b","c">>
}

Test == TestSubsequences

\* The only possible extension for H3 is completing the enqueue
ExtH3 == L!Extensions(H3) = {[op|->"Ok", proc|->"A"]}


=============================================================================
\* Modification History
\* Last modified Sat Oct 20 21:57:20 PDT 2018 by lhochstein
\* Created Sat Oct 20 13:43:05 PDT 2018 by lhochstein
