module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansion
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.QPd

theorem exists_sub_one_pow {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] (x : B) :
    ∃ z : B, (x - 1) ^ (p - 1) = (∑ i ∈ Finset.range p, x ^ i) - (p : B) * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : ((X - 1 : (ZMod p)[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
    have h1 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
      simpa using sub_pow_char (X : (ZMod p)[X]) 1
    have h2 : (X - 1 : (ZMod p)[X]) * ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i = X ^ p - 1 :=
      mul_geom_sum _ _
    have h3 : (X - 1 : (ZMod p)[X]) ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    have h4 : (X - 1 : (ZMod p)[X]) * ((X - 1) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
      rw [mul_sub, h2, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left h3
  have hdvd : C (p : ℤ) ∣ ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i) := by
    have hmap : ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map
        (Int.castRingHom (ZMod p)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Polynomial.map_sum] using hmod
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have h5 := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) hmap
    simp only [coeff_map, coeff_zero] at h5
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using h5)
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨-aeval x g, ?_⟩
  have := congrArg (aeval x) hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_pow, aeval_X, map_one, map_sum, map_mul, aeval_C] at this
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at this
  linear_combination this

theorem not_dvd_choose {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ (a * p + c).choose c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a * p + c) (k := c)
  have h1 : (a * p + c) % p = c := by
    rw [Nat.mul_add_mod_of_lt hc] <;> simp
  have h2 : c % p = c := Nat.mod_eq_of_lt hc
  have h3 : c / p = 0 := Nat.div_eq_of_lt hc
  rw [h1, h2, h3] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans h
  have := (Nat.modEq_iff_dvd.1 h0)
  simp at this
  have h5 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h5)

theorem not_dvd_uniformBell {p : ℕ} (hp : p.Prime) (a : ℕ) : ¬ p ∣ Nat.uniformBell a p := by
  induction a with
  | zero => simpa [Nat.uniformBell_zero_left] using hp.one_lt.ne'
  | succ a ih =>
    rw [Nat.uniformBell_succ_left]
    intro h
    rcases (hp.dvd_mul).1 h with h | h
    · refine not_dvd_choose hp a (p - 1) (Nat.sub_lt hp.pos one_pos) ?_
      have h6 : a * p + (p - 1) = a * p + p - 1 := by have := hp.pos; omega
      rwa [h6]
    · exact ih h

theorem exists_inv {B : Type} [CommRing B] {p N : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B))
    (h : ¬ p ∣ N) : ∃ v : B, v * N = 1 := by
  obtain ⟨e, he⟩ := hnil
  have hc : IsCoprime (N : ℤ) ((p : ℤ) ^ e) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨s, t, hst⟩ := hc
  refine ⟨s, ?_⟩
  have := congrArg (Int.cast : ℤ → B) hst
  push_cast at this
  rw [he] at this
  simpa using this

theorem pow_dvd_factorial {p : ℕ} (hp : p.Prime) (e : ℕ) : p ^ e ∣ (p * e).factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_pow_eq_zero {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ}
    (hp : p.Prime) (hnil : IsNilpotent (p : B)) : ∃ n : ℕ, ∀ y ∈ J, y ^ n = 0 := by
  obtain ⟨e, he⟩ := hnil
  refine ⟨p * e, fun y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := pow_dvd_factorial hp e
  rw [← δ.factorial_mul_dpow_eq_pow hy, hk]
  push_cast
  rw [he]
  simp

theorem not_dvd_coeff {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial := by
  rw [Nat.choose_symm_add]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact not_dvd_uniformBell hp a h
    · exact not_dvd_choose hp a c hc h
  · exact absurd ((hp.dvd_factorial).1 h) (not_le.2 hc)

section
variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem coeff_mul_dpow {p : ℕ} (hp : p.Prime) {μ w : B} (hμ : μ ∈ J) (hw : w ∈ J)
    (h : δ.dpow p μ = μ * w) (a c : ℕ) :
    ((Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial : ℕ) : B) *
        δ.dpow (a * p + c) μ = μ ^ (a + c) * δ.dpow a w := by
  have h1 : (Nat.uniformBell a p : B) * δ.dpow (a * p) μ = μ ^ a * δ.dpow a w := by
    rw [← δ.dpow_comp hp.ne_zero hμ, h, δ.dpow_mul hw]
  have h2 := δ.mul_dpow (m := a * p) (n := c) hμ
  have h3 := δ.factorial_mul_dpow_eq_pow (n := c) hμ
  push_cast
  rw [pow_add]
  linear_combination (-(Nat.uniformBell a p : B) * (c.factorial : B)) * h2 +
    (c.factorial : B) * δ.dpow c μ * h1 + μ ^ a * δ.dpow a w * h3

theorem exists_dpow_prime_eq {p : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B)) (x : B)
    (hξ : (∑ i ∈ Finset.range p, x ^ i) ∈ J) :
    ∃ w ∈ GlobalTheory.Cris.ExpBij.dpFil δ (p - 1), δ.dpow p (x ^ p - 1) = (x ^ p - 1) * w := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  simp only [Nat.add_sub_cancel] at *
  set ξ := ∑ i ∈ Finset.range (q + 1), x ^ i with hξdef
  obtain ⟨z, hz⟩ := exists_sub_one_pow hp x
  simp only [Nat.add_sub_cancel, ← hξdef] at hz
  obtain ⟨u, hu⟩ := exists_inv (N := q.factorial) hp hnil
    (fun h ↦ absurd ((hp.dvd_factorial).1 h) (by omega))
  have hμ : x ^ (q + 1) - 1 = (x - 1) * ξ := (mul_geom_sum x (q + 1)).symm
  have h2 := δ.factorial_mul_dpow_eq_pow (n := q + 1) hξ
  rw [Nat.factorial_succ] at h2
  push_cast at h2 hz
  refine ⟨δ.dpow (q + 1) ξ - z * u * ξ ^ q, ?_, ?_⟩
  · refine Ideal.sub_mem _ (GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ q)
      (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hξ _)) (Ideal.mul_mem_left _ _ ?_)
    simpa using GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hξ) q
  · rw [hμ, δ.dpow_mul hξ, pow_succ]
    linear_combination (x - 1) * δ.dpow (q + 1) ξ * hz +
      (x - 1) * z * ((q : B) + 1) * δ.dpow (q + 1) ξ * hu - (x - 1) * z * u * h2

end

theorem dpow_pow_sub_one : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  intro B _ J δ p hp hnil x hξ
  have hμJ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hξ
  obtain ⟨n, hn⟩ := exists_pow_eq_zero δ hp hnil
  obtain ⟨w, hwf, hw⟩ := exists_dpow_prime_eq δ hp hnil x hξ
  have hp2 := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hwJ : w ∈ J := GlobalTheory.Cris.ExpBij.dpFil_le δ hp1 hwf
  generalize x ^ p - 1 = μ at hμJ hw ⊢
  have key : ∀ m, ∃ b : B, (m = 1 → b = 1) ∧
      (1 ≤ m → δ.dpow m μ = μ * b ∧ b ∈ GlobalTheory.Cris.ExpBij.dpFil δ (m - 1)) ∧
      (p * (n + 2) ≤ m → b = 0) := by
    intro m
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact ⟨0, by simp, by simp, fun _ ↦ rfl⟩
      · refine ⟨1, fun _ ↦ rfl, fun _ ↦ ⟨by rw [δ.dpow_one hμJ, mul_one],
          GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ 1⟩, fun h ↦ ?_⟩
        nlinarith
    · obtain ⟨a, c, hc, rfl⟩ : ∃ a c, c < p ∧ a * p + c = m :=
        ⟨m / p, m % p, Nat.mod_lt _ hp.pos, Nat.div_add_mod' m p⟩
      obtain ⟨v, hv⟩ := exists_inv hp hnil (not_dvd_coeff hp a c hc)
      have hco := coeff_mul_dpow δ hp hμJ hwJ hw a c
      obtain ⟨k, hk⟩ : ∃ k, a + c = k + 1 := by
        refine ⟨a + c - 1, ?_⟩
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [zero_mul, zero_add] at h ⊢
          omega
        · omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      refine ⟨v * (μ ^ k * δ.dpow a w), fun h1 ↦ by omega, fun _ ↦ ⟨?_, ?_⟩, fun hM ↦ ?_⟩
      · calc δ.dpow (a * (q + 1) + c) μ
            = (v * ((Nat.uniformBell a (q + 1) * (a * (q + 1) + c).choose (a * (q + 1)) *
                c.factorial : ℕ) : B)) * δ.dpow (a * (q + 1) + c) μ := by rw [hv, one_mul]
          _ = v * (μ ^ (a + c) * δ.dpow a w) := by rw [mul_assoc, hco]
          _ = μ * (v * (μ ^ k * δ.dpow a w)) := by rw [hk, pow_succ]; ring
      · have h5 := GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ
          (GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hμJ) k)
          (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hp1 hwf a)
        have e : a * (q + 1) + c - 1 = k * 1 + a * (q + 1 - 1) := by
          rw [Nat.add_sub_cancel, Nat.mul_succ]
          omega
        rw [e]
        exact Ideal.mul_mem_left _ _ h5
      · have h6 : n + 2 ≤ a := by
          by_contra hlt
          have h7 : a + 1 ≤ n + 2 := by omega
          have h8 := Nat.mul_le_mul_left (q + 1) h7
          nlinarith
        have h9 : μ ^ k = 0 := pow_eq_zero_of_le (by omega : n ≤ k) (hn μ hμJ)
        simp [h9]
  choose ν h1 h2 h3 using key
  refine ⟨⟨n, hn _ hμJ⟩, ν, h1 1 rfl, fun m ↦ (h2 (m + 1) (by omega)).1, fun m ↦ ?_, fun m hm ↦ ?_,
    p * (n + 2), fun m hm ↦ h3 m hm⟩
  · have h := (h2 (m + 1) (by omega)).2
    rw [Nat.add_sub_cancel] at h
    exact h
  · exact ⟨n, hn _ (GlobalTheory.Cris.ExpBij.dpFil_le δ (show 1 ≤ m - 1 by omega) (h2 m (by omega)).2)⟩

end GlobalTheory.CompanionTheory.QPd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDFil

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_mul_le (δ : DividedPowers J) (a c : ℕ) :
    GlobalTheory.PDA.fil δ a * GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ (a + c) := by
  unfold GlobalTheory.PDA.fil
  rw [Ideal.span_mul_span']
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨l, hl, hn, rfl⟩, _, ⟨m, hm, hk, rfl⟩, rfl⟩
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · exact hm p h
  · simp only [List.map_append, List.sum_append]
    omega
  · simp only [List.map_append, List.prod_append]

theorem fil_anti (δ : DividedPowers J) {a c : ℕ} (h : a ≤ c) :
    GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ a := by
  refine Ideal.span_mono ?_
  rintro b ⟨l, h1, h2, h3⟩
  exact ⟨l, h1, h.trans h2, h3⟩

theorem fil_zero (δ : DividedPowers J) : GlobalTheory.PDA.fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

theorem dpow_mem_fil (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ GlobalTheory.PDA.fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

def coefFil (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Submodule B Q.P where
  carrier := {z | ∀ k, Q.e.repr z k ∈ GlobalTheory.PDA.fil δ (r - k)}
  add_mem' := by
    intro x y hx hy k
    simpa using Ideal.add_mem _ (hx k) (hy k)
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c x hx k
    simpa using Ideal.mul_mem_left _ c (hx k)

theorem coefFil_anti (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} (h : a ≤ c) {z : Q.P}
    (hz : z ∈ coefFil δ Q c) : z ∈ coefFil δ Q a :=
  fun k ↦ fil_anti δ (by omega) (hz k)

theorem mem_coefFil_zero (δ : DividedPowers J) (Q : PDPoly B) (z : Q.P) :
    z ∈ coefFil δ Q 0 := by
  intro k
  simp [fil_zero]

theorem smul_e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r k : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (r - k)) : b • Q.e k ∈ coefFil δ Q r := by
  intro j
  by_cases h : j = k
  · subst h
    simpa using hb
  · have : Q.e.repr (b • Q.e k) j = 0 := by
      simp [Finsupp.single_apply, Ne.symm h]
    rw [this]
    exact Ideal.zero_mem _

theorem eq_sum_repr (Q : PDPoly B) (z : Q.P) :
    z = ∑ k ∈ (Q.e.repr z).support, Q.e.repr z k • Q.e k := by
  conv_lhs => rw [← Q.e.linearCombination_repr z]
  rfl

theorem smul_e_mul_smul_e_mem (δ : DividedPowers J) (Q : PDPoly B) {a c k l : ℕ} {b b' : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (a - k)) (hb' : b' ∈ GlobalTheory.PDA.fil δ (c - l)) :
    (b • Q.e k) * (b' • Q.e l) ∈ coefFil δ Q (a + c) := by
  have h1 : b * b' ∈ GlobalTheory.PDA.fil δ (a + c - (k + l)) :=
    fil_anti δ (by omega) (fil_mul_le δ _ _ (Ideal.mul_mem_mul hb hb'))
  rw [smul_mul_smul_comm, Q.e_mul, ← nsmul_eq_mul, smul_comm]
  exact nsmul_mem (smul_e_mem_coefFil δ Q h1) _

theorem mul_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} {z w : Q.P}
    (hz : z ∈ coefFil δ Q a) (hw : w ∈ coefFil δ Q c) : z * w ∈ coefFil δ Q (a + c) := by
  rw [eq_sum_repr Q z, eq_sum_repr Q w, Finset.sum_mul_sum]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦
    smul_e_mul_smul_e_mem δ Q (hz k) (hw l)

def coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Ideal Q.P where
  carrier := coefFil δ Q r
  add_mem' := (coefFil δ Q r).add_mem
  zero_mem' := (coefFil δ Q r).zero_mem
  smul_mem' := by
    intro c x hx
    simpa using mul_mem_coefFil δ Q (mem_coefFil_zero δ Q c) hx

theorem algebraMap_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ r) : algebraMap B Q.P b ∈ coefFil δ Q r := by
  have : algebraMap B Q.P b = b • Q.e 0 := by
    rw [Q.e_zero, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact smul_e_mem_coefFil δ Q (by simpa using hb)

theorem e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {n m : ℕ} (h : n ≤ m) :
    Q.e m ∈ coefFil δ Q n := by
  have : (1 : B) ∈ GlobalTheory.PDA.fil δ (n - m) := by
    rw [Nat.sub_eq_zero_of_le h, fil_zero]
    trivial
  simpa using smul_e_mem_coefFil δ Q this

theorem e_mem_ext (Q : PDPoly B) (J : Ideal B) (k : ℕ) : Q.e (k + 1) ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

theorem dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) {y : Q.P} (hy : y ∈ Q.ext J) (n : ℕ) :
    η.dpow n y ∈ coefFil δ Q n := by
  let S : Ideal Q.P :=
    { carrier := {y | y ∈ Q.ext J ∧ ∀ n, η.dpow n y ∈ coefFil δ Q n}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Ideal.add_mem _ hx hy, fun n ↦ ?_⟩
        rw [η.dpow_add hx hy]
        refine Submodule.sum_mem _ fun p hp ↦ ?_
        have := mul_mem_coefFil δ Q (hx' p.1) (hy' p.2)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hp] at this
      zero_mem' := by
        refine ⟨Ideal.zero_mem _, fun n ↦ ?_⟩
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact mem_coefFil_zero δ Q _
        · rw [η.dpow_eval_zero hn.ne']
          exact Submodule.zero_mem _
      smul_mem' := by
        rintro a y ⟨hy, hy'⟩
        refine ⟨Ideal.mul_mem_left _ a hy, fun n ↦ ?_⟩
        rw [smul_eq_mul, η.dpow_mul hy]
        exact (coefIdeal δ Q n).mul_mem_left _ (hy' n) }
  have hS : Q.ext J ≤ S := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_) (Ideal.span_le.2 ?_)
    · refine ⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj), fun n ↦ ?_⟩
      rw [h.dp.dpow_comp j hj]
      exact algebraMap_mem_coefFil δ Q (dpow_mem_fil δ n hj)
    · rintro _ ⟨k, rfl⟩
      have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
      refine ⟨e_mem_ext Q J k, fun n ↦ ?_⟩
      show η.dpow n (Q.e (k + 1)) ∈ coefFil δ Q n
      rw [← h.var (k + 1), η.dpow_comp (Nat.succ_ne_zero k) h1, h.var, ← nsmul_eq_mul]
      exact nsmul_mem (e_mem_coefFil δ Q (Nat.le_mul_of_pos_right n (Nat.succ_pos k))) _
  exact (hS hy).2 n

theorem prod_dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (l : List (ℕ × Q.P)) (hl : ∀ p ∈ l, p.2 ∈ Q.ext J) :
    (l.map fun p ↦ η.dpow p.1 p.2).prod ∈ coefFil δ Q (l.map Prod.fst).sum := by
  induction l with
  | nil => simpa using mem_coefFil_zero δ Q 1
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem_coefFil δ Q (dpow_mem_coefFil δ Q η h (hl p (by simp)) p.1)
      (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))

theorem fil_le_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) : GlobalTheory.PDA.fil η r ≤ coefIdeal δ Q r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hn, rfl⟩
  exact coefFil_anti δ Q hn (prod_dpow_mem_coefFil δ Q η h l hl)

theorem algebraMap_mem_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {b : B} (hb : b ∈ GlobalTheory.PDA.fil δ r) :
    algebraMap B Q.P b ∈ GlobalTheory.PDA.fil η r := by
  have : (GlobalTheory.PDA.fil δ r).map (algebraMap B Q.P) ≤ GlobalTheory.PDA.fil η r := by
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro _ ⟨l, hl, hn, rfl⟩
    have hmem : ∀ p ∈ l, algebraMap B Q.P p.2 ∈ Q.ext J := fun p hp ↦
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hl p hp))
    have key : algebraMap B Q.P (l.map fun p ↦ δ.dpow p.1 p.2).prod =
        ((l.map fun p ↦ (p.1, algebraMap B Q.P p.2)).map fun p ↦ η.dpow p.1 p.2).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p hp ↦ ?_
      exact (h.dp.dpow_comp p.2 (hl p hp)).symm
    show algebraMap B Q.P _ ∈ GlobalTheory.PDA.fil η r
    rw [key]
    refine Ideal.subset_span ⟨_, ?_, ?_, rfl⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hmem q hq
    · simpa [List.map_map, Function.comp_def] using hn
  exact this (Ideal.mem_map_of_mem _ hb)

theorem coefFil_le_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {z : Q.P} (hz : z ∈ coefFil δ Q r) : z ∈ GlobalTheory.PDA.fil η r := by
  rw [eq_sum_repr Q z]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
  have hk : Q.e k ∈ GlobalTheory.PDA.fil η k := by
    rw [← h.var k]
    exact dpow_mem_fil η k h1
  rw [Algebra.smul_def]
  exact fil_anti η (by omega)
    (fil_mul_le η _ _ (Ideal.mul_mem_mul (algebraMap_mem_fil δ Q η h _ (hz k)) hk))

theorem fil_pdPoly : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  intro B _ J δ Q η h
  exact ⟨fil_mul_le δ, fun _ _ hac ↦ fil_anti δ hac, fil_zero δ, fun r z ↦
    ⟨fun hz ↦ fil_le_coefIdeal δ Q η h r hz, fun hz ↦ coefFil_le_fil δ Q η h r hz⟩⟩

end GlobalTheory.CompanionTheory.PDFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftHomExistsUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem lift_hom_existsUnique {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I) (𝓛 : Lift a T Λ I κ) {B : Type} [CommRing B]
    (J : Ideal B) : EtLift J → ∀ (h : Λ →+* B) (g : R →+* B ⧸ J) (u : Fin d → B), I ≤ J.comap h →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = Ideal.Quotient.mk J (h x)) →
    (∀ k, Ideal.Quotient.mk J (u k) = g (T k)) →
    ∃! f : 𝓛.D →+* B, f.comp 𝓛.i = h ∧ (∀ k, f (𝓛.t k) = u k) ∧
      ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk J (f z) = g r := by
  intro hEt h g u hIJ hg hu
  obtain ⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩ := 𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)
  have hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) =
      (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hg0i c
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hu k]
      exact hg0j (T k) (𝓛.t k) (𝓛.hT k).symm
  obtain ⟨F, ⟨hFψ, hFg⟩, hFu⟩ :=
    hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)
  · exact fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)
  · intro r z hz
    rw [← hg0j r z hz]
    exact RingHom.congr_fun hFg z
  · rintro f' ⟨hf'i, hf't, hf'j⟩
    apply hFu
    refine ⟨?_, ?_⟩
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact RingHom.congr_fun hf'i c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hf't k
    · apply hg0u
      refine ⟨?_, ?_⟩
      · rw [RingHom.comp_assoc, hf'i]
      · intro r z hz
        exact hf'j r z hz

end GlobalTheory.CompanionTheory.EtaleLift
end

