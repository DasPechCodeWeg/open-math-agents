import FormalConjectures.OEIS.«189409»

/-!
# `(p_n#)^2 + 1` is not always squarefree

The ninth term is a counterexample. The product of the first nine primes is
`2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 = 223092870`, and

`223092870 ^ 2 + 1 = 49770428644836901 = 29 ^ 2 * 53 * 1116604864937`.

So `29 ^ 2` divides `a 9`, and `a 9` is not squarefree.
-/

namespace OMA.A189409

open Nat

lemma kthPrimorial_nine : Nat.kthPrimorial 9 = 223092870 := by
  rw [Nat.kthPrimorial_succ, Nat.kthPrimorial_succ, Nat.kthPrimorial_succ, Nat.kthPrimorial_succ,
    Nat.kthPrimorial_five, Nat.nth_prime_five_eq_thirteen, Nat.nth_prime_six_eq_seventeen,
    Nat.nth_prime_seven_eq_nineteen, Nat.nth_prime_eight_eq_twentyThree]

end OMA.A189409

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro h
  have h9 := h 9
  rw [OeisA189409.a, OMA.A189409.kthPrimorial_nine] at h9
  have hunit : IsUnit (29 : ℕ) := h9 29 ⟨59180057841661, by norm_num⟩
  rw [Nat.isUnit_iff] at hunit
  omega
