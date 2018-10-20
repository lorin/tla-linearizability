------------------------ MODULE TestLinearizability ------------------------
EXTENDS Linearizability

H3 == <<
    [op|->"E", val|->"x", proc|->"A"],
    [op|->"D", proc|-> "B"],
    [op|->"Ok", val|->"x", proc|->"B"]
 >>


\* THe only possible extension for H3 is completing the enqueue
Test == Extensions(H3) = {Append(H3, [op|->"Ok", proc|->"A"])}


=============================================================================
\* Modification History
\* Last modified Sat Oct 20 13:46:00 PDT 2018 by lhochstein
\* Created Sat Oct 20 13:43:05 PDT 2018 by lhochstein
