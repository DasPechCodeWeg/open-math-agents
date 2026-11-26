import FormalConjectures.ErdosProblems.«436»

/-!
# `Λ(k, 3) = ∞` for even `k`

For even `k`, a `k`th power residue is a quadratic residue, so it is enough to find, for every
`N`, infinitely many primes `p` with no three consecutive quadratic residues below `N`.

Take `p ≡ -3` modulo `8` times the product of all primes `q ≤ N + 2`, `q ≠ 3` (Dirichlet). Then
`p ≡ 5 (mod 8)`, so `(2/p) = -1 = (2/3)`, and for odd `q ≠ 3` quadratic reciprocity gives
`(q/p) = (p/q) = (-3/q) = (q/3)`. By multiplicativity `(m/p) = (m/3)` for all `m ≤ N + 2` prime
to `3`. So every `m ≤ N + 2` with `m ≡ 2 (mod 3)` is a non-residue modulo `p`, and one of any
three consecutive integers is `≡ 2 (mod 3)`.
-/

open Filter Erdos436

namespace OMA.E436b

lemma two_not_sq_mod_three : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by
  unfold IsSquare
  decide

lemma leg3_two : legendreSym 3 ((2 : ℕ) : ℤ) = -1 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (legendreSym.eq_neg_one_iff' 3).2 two_not_sq_mod_three

/-- `(q/p) = (q/3)` for a prime `q ≠ 3`, when `p ≡ 5 (mod 8)` and `p ≡ -3 (mod q)`. -/
lemma leg_prime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact (Nat.Prime 3)] (hp8 : p % 8 = 5)
    (hmod : (p : ℤ) ≡ -3 [ZMOD (q : ℤ)]) :
    legendreSym p q = legendreSym 3 q := by
  by_cases hq2 : q = 2
  · subst hq2
    have h1 : legendreSym p ((2 : ℕ) : ℤ) = -1 := by
      refine (legendreSym.eq_neg_one_iff' p).2 ?_
      rw [Nat.cast_ofNat, ZMod.exists_sq_eq_two_iff (by omega)]
      omega
    rw [h1, leg3_two]
  · have hp4 : p % 4 = 1 := by omega
    have e1 : legendreSym p q = legendreSym q p :=
      (legendreSym.quadratic_reciprocity_one_mod_four hp4 hq2).symm
    have h' : (p : ℤ) % (q : ℤ) = (-3) % (q : ℤ) := hmod
    have e2 : legendreSym q p = legendreSym q (-3) := by
      rw [legendreSym.mod q (p : ℤ), h', ← legendreSym.mod q (-3)]
    have hodd : q % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq2
    have hneg : legendreSym q (-1) = ZMod.χ₄ q := legendreSym.at_neg_one hq2
    have hrec : legendreSym q ((3 : ℕ) : ℤ) = (-1) ^ (3 / 2 * (q / 2)) * legendreSym 3 q :=
      legendreSym.quadratic_reciprocity' (p := 3) (q := q) (by norm_num) hq2
    have e3 : legendreSym q (-3) = legendreSym 3 q := by
      rw [show (-3 : ℤ) = (-1) * ((3 : ℕ) : ℤ) by norm_num, legendreSym.mul, hneg, hrec,
        ZMod.χ₄_eq_neg_one_pow hodd]
      have h32 : 3 / 2 = 1 := by norm_num
      rw [h32, one_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [e1, e2, e3]

/-- Multiplicativity extends `(q/p) = (q/3)` from primes to all `m ≤ M` prime to `3`. -/
lemma leg_all {p M : ℕ} [Fact p.Prime] [Fact (Nat.Prime 3)]
    (hprime : ∀ q : ℕ, q.Prime → q ≤ M → q ≠ 3 → legendreSym p q = legendreSym 3 q) :
    ∀ m : ℕ, 1 ≤ m → m ≤ M → ¬ 3 ∣ m → legendreSym p m = legendreSym 3 m := by
  intro m
  induction m using induction_on_primes with
  | zero => intro h; omega
  | one =>
    intro _ _ _
    simp [legendreSym.at_one]
  | prime_mul q a hq ih =>
    intro h1 hM h3
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at h1
      · exact h
    have hqa : q ≤ q * a := Nat.le_mul_of_pos_right q ha
    have haq : a ≤ q * a := Nat.le_mul_of_pos_left a hq.pos
    have hq3 : q ≠ 3 := fun h => h3 (h ▸ dvd_mul_right q a)
    have ha3 : ¬ 3 ∣ a := fun h => h3 (Dvd.dvd.mul_left h q)
    rw [Nat.cast_mul, legendreSym.mul, legendreSym.mul, hprime q hq (by omega) hq3,
      ih ha (by omega) ha3]

lemma exists_prime (N a : ℕ) :
    ∃ p > a, p.Prime ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ N + 2 → m % 3 = 2 → ¬ IsSquare ((m : ℕ) : ZMod p) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S : Finset ℕ := (Finset.range (N + 3)).filter (fun q => q.Prime ∧ q ≠ 3) with hS
  set L : ℕ := 8 * ∏ q ∈ S, q with hL
  have hprod : 0 < ∏ q ∈ S, q :=
    Finset.prod_pos (fun q hq => (Finset.mem_filter.1 hq).2.1.pos)
  have hL0 : L ≠ 0 := by positivity
  have hc3 : Nat.Coprime 3 L := by
    refine Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.prod_right fun q hq => ?_)
    have hq' := (Finset.mem_filter.1 hq).2
    exact (Nat.coprime_primes Nat.prime_three hq'.1).2 (Ne.symm hq'.2)
  have hcop : IsCoprime (-3 : ℤ) (L : ℤ) := by
    have h := (Nat.isCoprime_iff_coprime.2 hc3).neg_left
    simpa using h
  obtain ⟨p, hpa, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq a hL0 hcop
  have := Fact.mk hp
  have h8dvd : (8 : ℤ) ∣ (L : ℤ) := ⟨((∏ q ∈ S, q : ℕ) : ℤ), by rw [hL]; push_cast; ring⟩
  have hp8 : p % 8 = 5 := by
    have h8 : (p : ℤ) % 8 = (-3) % 8 := hmod.of_dvd h8dvd
    omega
  have hprime : ∀ q : ℕ, q.Prime → q ≤ N + 2 → q ≠ 3 → legendreSym p q = legendreSym 3 q := by
    intro q hq hqM hq3
    have := Fact.mk hq
    have hqS : q ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq, hq3⟩
    have hdvd : (q : ℤ) ∣ (L : ℤ) :=
      Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hqS) 8)
    exact leg_prime hp8 (hmod.of_dvd hdvd)
  refine ⟨p, hpa, hp, ?_⟩
  intro m h1 hM h3
  refine (legendreSym.eq_neg_one_iff' p).1 ?_
  rw [leg_all hprime m h1 hM (by omega), legendreSym.mod 3 (m : ℤ),
    show (m : ℤ) % ((3 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by push_cast; omega]
  exact leg3_two

lemma le_r {k N p : ℕ} (hk : Even k)
    (hres : ∀ m : ℕ, 1 ≤ m → m ≤ N + 2 → m % 3 = 2 → ¬ IsSquare ((m : ℕ) : ZMod p)) :
    (N : ℕ∞) ≤ r k 3 p := by
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ N + 2 → m % 3 = 2 → ¬ IsPowerResidue k p m := by
    rintro m h1 h2 h3 ⟨-, x, hx⟩
    obtain ⟨j, rfl⟩ := hk
    exact hres m h1 h2 h3 ⟨x ^ j, by rw [← hx, pow_add]⟩
  refine le_iInf₂ ?_
  rintro n ⟨hn, h⟩
  by_contra hlt
  have hnN : n < N := by exact_mod_cast lt_of_not_ge hlt
  have h0 : IsPowerResidue k p n := by simpa using h 0 (by norm_num)
  have h1 : IsPowerResidue k p (n + 1) := h 1 (by norm_num)
  have h2 : IsPowerResidue k p (n + 2) := h 2 (by norm_num)
  rcases (by omega : n % 3 = 2 ∨ (n + 1) % 3 = 2 ∨ (n + 2) % 3 = 2) with c | c | c
  · exact key n hn (by omega) c h0
  · exact key (n + 1) (by omega) (by omega) c h1
  · exact key (n + 2) (by omega) (by omega) c h2

end OMA.E436b

theorem OMA.solution : type_of% @Erdos436.erdos_436.variants.even_three := by
  intro k _ hkeven
  show runLimsup k 3 = ⊤
  by_contra htop
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 htop
  have hfreq : ∃ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, ((N + 1 : ℕ) : ℕ∞) ≤ r k 3 p := by
    rw [Filter.frequently_inf_principal, Filter.frequently_atTop]
    intro a
    obtain ⟨p, hpa, hp, hres⟩ := OMA.E436b.exists_prime (N + 1) a
    exact ⟨p, hpa.le, hp, OMA.E436b.le_r hkeven hres⟩
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ runLimsup k 3 := Filter.le_limsup_of_frequently_le' hfreq
  rw [← hN] at hle
  have : N + 1 ≤ N := by exact_mod_cast hle
  omega
