module

public import Tests.Fixtures.Shell
import all Tests.Fixtures.Core
meta import Tests.Fixtures.Core
meta import Tests.Support
public meta import LeanEvidence

public section

namespace Tests.Commands

open Tests.Fixtures

rejects "doc comment" in WorldClaim Undocumented := True
assert_absent Undocumented

assert_claim SuccAgrees is world
assert_claim Identity is conjecture
assert_evidence SuccAgrees = 0 tests 1 checks 0 suites
assert_evidence Identity = 1 tests 0 checks 0 suites

Check SuccAgrees : nativeSucc 0 = 0 + 1
assert_evidence SuccAgrees = 0 tests 2 checks 0 suites

rejects "false when compiled and run" in Check Unchecked : wrongSucc 1 = 1 + 1
assert_evidence Unchecked = 0 tests 0 checks 0 suites
rejects "not an instance" in Check SuccAgrees : 2 + 2 = 4
rejects "not a WorldClaim or Conjecture" in Check (2 = 2) : 2 = 2

Test Identity identity : identity 4 = 4 := by decide
assert_evidence Identity = 2 tests 0 checks 0 suites
rejects "not an instance" in Test Identity identity : identity 4 = 5 := by decide
rejects "kernel-checked" in Test Identity identity : identity 6 = 6 := by native_decide
rejects "kernel-checked" in Test Identity identity : identity 7 = 7 := by sorry
Conjecture Successor (f : Nat → Nat) := ∀ n, f n = n + 1
rejects "declaration failed" in Test Successor identity : identity 8 = 8 + 1 := by decide
assert_evidence Identity = 2 tests 0 checks 0 suites

Check Identity identity : identity 1000 = 1000
assert_evidence Identity = 2 tests 1 checks 0 suites

assert_evidence ClockAdvances = 0 tests 0 checks 1 suites
rejects "not a WorldClaim or Conjecture" in
  @[exercises Nat.add] def bogusSuite : IO Unit := pure ()

Conjecture Bounded (f : Nat → Nat) := ∀ n, f n ≤ n
Test Bounded identity : identity 2 ≤ 2 := by decide
rejects "marked as `meta`" in
  def runtimeEvidence : Bool := (LeanEvidence.evidenceFor default `x).isEmpty

end Tests.Commands
