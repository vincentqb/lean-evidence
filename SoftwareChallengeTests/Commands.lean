module

public import SoftwareChallengeTests.Fixtures.Shell
import all SoftwareChallengeTests.Fixtures.Core
meta import SoftwareChallengeTests.Fixtures.Core
meta import SoftwareChallengeTests.Support
public meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Commands

open SoftwareChallengeTests.Fixtures

rejects "doc comment" in WorldClaim Undocumented := True

Check SuccAgrees : nativeSucc 0 = 0 + 1
assert_evidence SuccAgrees = 0 tests 2 checks 0 suites

rejects "false when compiled and run" in Check Unchecked : wrongSucc 1 = 1 + 1
rejects "not an instance" in Check SuccAgrees : 2 + 2 = 4
rejects "not a WorldClaim or Conjecture" in Check (2 = 2) : 2 = 2

Test Identity identity : identity 4 = 4 := by decide
rejects "not an instance" in Test Identity identity : identity 4 = 5 := by decide
rejects "kernel-checked" in Test Identity identity : identity 6 = 6 := by native_decide
rejects "kernel-checked" in Test Identity identity : identity 7 = 7 := by sorry
rejects "declaration failed" in Test Unchecked : wrongSucc 1 = 1 + 1 := by decide

Check Identity identity : identity 1000 = 1000
assert_evidence Identity = 2 tests 1 checks 0 suites

assert_evidence ClockAdvances = 0 tests 0 checks 1 suites
rejects "not a WorldClaim or Conjecture" in
  @[exercises Nat.add] def bogusSuite : IO Unit := pure ()

rejects "marked as `meta`" in
  def runtimeEvidence : Bool := (SoftwareChallenge.allEvidence default).isEmpty

end SoftwareChallengeTests.Commands
