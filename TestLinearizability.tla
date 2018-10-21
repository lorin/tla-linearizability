------------------------ MODULE TestLinearizability ------------------------
EXTENDS Naturals, Sequences, LinQueue

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

TestComplete == L!Complete(<< [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"] >>)

TestAreEquivalentTrue == L!AreEquivalent(
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"], [op |-> "Ok", val |-> "x", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"] >>
)

TestAreEquivalentFalse == L!AreEquivalent(
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", proc |-> "A"], [op |-> "Ok", val |-> "x", proc |-> "B"] >>,
    << [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"], [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "y", proc |-> "B"] >>
)

TestPrecedes == 
    LET H == << 
        [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"],
        [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"],
        [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"]>>
        e1 == <<H[1], H[2]>>
        e2 == <<H[3], H[4]>>
        e3 == <<H[5], H[6]>>
    IN /\ L!Precedes(H, e1, e2)
       /\ L!Precedes(H, e2, e3)

TestOperations ==
    LET H == << 
        [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"],
        [op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"],
        [op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"]>>
    IN L!Operations(H) = { 
        <<[op |-> "E", val |-> "x", proc |-> "A"], [op |-> "Ok", proc |-> "A"]>>,
        <<[op |-> "D", proc |-> "B"], [op |-> "Ok", val |-> "x", proc |-> "B"]>>}

Test == TestOperations

\* The only possible extension for H3 is completing the enqueue
ExtH3 == L!Extensions(H3) = {[op|->"Ok", proc|->"A"]}


=============================================================================
\* Modification History
\* Last modified Sun Oct 21 10:18:05 PDT 2018 by lhochstein
\* Created Sat Oct 20 13:43:05 PDT 2018 by lhochstein
