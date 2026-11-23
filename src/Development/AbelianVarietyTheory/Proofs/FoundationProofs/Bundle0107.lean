module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatDegreeMinpolyLe
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ValMax

variable {Ω : Type} [Field Ω]

theorem val_int_le_one (V : ValuationSubring Ω) (z : ℤ) : V.valuation (z : Ω) ≤ 1 :=
  V.valuation_le_one ⟨_, intCast_mem V z⟩

theorem val_nat_eq_one (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : ¬ q ∣ n) : V.valuation (n : Ω) = 1 := by
  have hc : IsCoprime (q : ℤ) n :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : Ω) * (q : Ω) + (b : Ω) * (n : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at this
    exact this
  have hle : V.valuation (n : Ω) ≤ 1 := by simpa using val_int_le_one V (n : ℤ)
  by_contra hne
  have hlt : V.valuation (n : Ω) < 1 := lt_of_le_of_ne hle hne
  have ha : V.valuation ((a : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V a)) hV
  have hb : V.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V b)) hlt
  have := V.valuation.map_add_lt ha hb
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem val_nat_eq_pow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, V.valuation (n : Ω) = V.valuation (q : Ω) ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  refine ⟨e, ?_⟩
  push_cast
  rw [map_mul, map_pow, val_nat_eq_one V hq hV hm, mul_one]

variable [Algebra ℚ Ω]

theorem val_q_ne_zero (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime) :
    V.valuation (q : Ω) ≠ 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rw [Valuation.ne_zero_iff]
  exact Nat.cast_ne_zero.2 hq.ne_zero

theorem val_rat_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℤ, V.valuation (algebraMap ℚ Ω r) = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_nat_eq_pow V hq hV (n := r.num.natAbs)
    (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr))
  obtain ⟨e2, h2⟩ := val_nat_eq_pow V hq hV (n := r.den) r.den_nz
  have h3 : V.valuation ((r.num : ℤ) : Ω) = V.valuation (q : Ω) ^ e1 := by
    rw [← h1]
    rcases Int.natAbs_eq r.num with h | h
    · conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    · conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
  refine ⟨(e1 : ℤ) - e2, ?_⟩
  have h4 : algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) / ((r.den : ℕ) : Ω) := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, map_intCast, map_natCast]
  rw [h4, map_div₀, h3, h2, zpow_sub₀ h0, zpow_natCast, zpow_natCast]

theorem val_pow_sub (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0)
    {i k : ℕ} (h : V.valuation (r • x ^ i) = V.valuation (s • x ^ (i + k))) :
    ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_rat_eq_zpow V hq hV hr
  obtain ⟨e2, h2⟩ := val_rat_eq_zpow V hq hV hs
  have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, h1, h2, map_pow, map_pow, pow_add,
    mul_comm (V.valuation x ^ i), ← mul_assoc] at h
  have h3 := mul_right_cancel₀ (pow_ne_zero i hx0) h
  refine ⟨e1 - e2, ?_⟩
  rw [zpow_sub₀ h0, h3, mul_div_cancel_left₀ _ (zpow_ne_zero _ h0)]

theorem val_pow_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (minpoly ℚ x).natDegree ∧
      ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  classical
  set p := minpoly ℚ x with hp
  set f : ℕ → Ω := fun i => p.coeff i • x ^ i with hf
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    rw [← Polynomial.aeval_eq_sum_range]
    exact minpoly.aeval ℚ x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (p.natDegree + 1))
    (fun i => V.valuation (f i)) ⟨0, by simp⟩
  have hj0 : V.valuation (f j) ≠ 0 := by
    intro h
    have h1 := hmax p.natDegree (by simp)
    have h2 : f p.natDegree = x ^ p.natDegree := by
      have : p.coeff p.natDegree = 1 := (minpoly.monic hi).coeff_natDegree
      simp only [hf, this, one_smul]
    rw [h, h2, le_zero_iff, Valuation.zero_iff] at h1
    exact pow_ne_zero _ hx h1
  have hex : ∃ i ∈ Finset.range (p.natDegree + 1) \ {j}, ¬ V.valuation (f i) < V.valuation (f j) := by
    by_contra hcon
    push Not at hcon
    have := V.valuation.map_sum_eq_of_lt hj hcon
    rw [hsum, map_zero] at this
    exact hj0 this.symm
  obtain ⟨i, hi', hlt⟩ := hex
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi'
  have heq : V.valuation (f i) = V.valuation (f j) :=
    le_antisymm (hmax i hi'.1) (not_lt.1 hlt)
  have hcj : p.coeff j ≠ 0 := by
    intro h
    apply hj0
    simp only [hf, h, zero_smul, map_zero]
  have hci : p.coeff i ≠ 0 := by
    intro h
    apply hj0
    rw [← heq]
    simp only [hf, h, zero_smul, map_zero]
  have hi1 := Finset.mem_range.1 hi'.1
  have hj1 := Finset.mem_range.1 hj
  rcases lt_or_gt_of_ne hi'.2 with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hci hcj heq⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hcj hci heq.symm⟩

theorem val_pow_factorial (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) {n : ℕ}
    (hn : (minpoly ℚ x).natDegree ≤ n) :
    ∃ e : ℤ, V.valuation x ^ n.factorial = V.valuation (q : Ω) ^ e := by
  obtain ⟨k, hk0, hk, e, he⟩ := val_pow_eq_zpow V hq hV hx hi
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hk0 (hk.trans hn)
  exact ⟨e * m, by rw [hm, pow_mul, he, _root_.zpow_mul, zpow_natCast]⟩

theorem natDegree_minpoly_le {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) [FiniteDimensional K F] {x : L} (hx : x ∈ F) :
    (minpoly K x).natDegree ≤ Module.finrank K F := by
  have h1 : (minpoly K (⟨x, hx⟩ : F)).natDegree ≤ Module.finrank K F :=
    minpoly.natDegree_le _
  rwa [IntermediateField.minpoly_eq] at h1

theorem exists_max_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (F : IntermediateField ℚ Ω), FiniteDimensional ℚ F → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (ι : Type) (a : ι → Ω) (c : Ω), c ≠ 0 → (∀ i, a i ∈ F) → (∀ i, c * a i ∈ V) → (∃ i, a i ≠ 0) → ∃ i, a i ≠ 0 ∧ ∀ i', V.valuation (a i') ≤ V.valuation (a i) := by
  intro Ω _ _ _ F hF q hq V hV ι a c hc haF hca hex
  rw [ValuationSubring.mem_nonunits_iff] at hV
  have h0 := val_q_ne_zero V hq
  have hpos : 0 < V.valuation (q : Ω) := zero_lt_iff.2 h0
  have hint : ∀ x : Ω, IsIntegral ℚ x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  set n := Module.finrank ℚ F + (minpoly ℚ c).natDegree with hn
  obtain ⟨e0, he0⟩ := val_pow_factorial V hq hV hc (hint c) (n := n) (by omega)
  have hall : ∀ i, a i ≠ 0 →
      ∃ e : ℤ, V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e := by
    intro i hi
    refine val_pow_factorial V hq hV hi (hint _) ?_
    exact (natDegree_minpoly_le F (haF i)).trans (Nat.le_add_right _ _)
  obtain ⟨e, ⟨i, hi, he⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun e : ℤ => ∃ i, a i ≠ 0 ∧ V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e)
    ⟨-e0, by
      rintro z ⟨i, -, hz⟩
      have h1 : V.valuation (c * a i) ≤ 1 := V.valuation_le_one ⟨_, hca i⟩
      have h2 : V.valuation (c * a i) ^ n.factorial ≤ 1 := pow_le_one' h1 _
      rw [map_mul, mul_pow, he0, hz, ← zpow_add₀ h0, ← zpow_zero (V.valuation (q : Ω)),
        zpow_le_zpow_iff_right_of_lt_one₀ hpos hV] at h2
      omega⟩
    (by
      obtain ⟨i, hi⟩ := hex
      obtain ⟨e, he⟩ := hall i hi
      exact ⟨e, i, hi, he⟩)
  refine ⟨i, hi, fun i' => ?_⟩
  by_cases hi' : a i' = 0
  · rw [hi', map_zero]
    exact zero_le'
  obtain ⟨e', he'⟩ := hall i' hi'
  have h1 : V.valuation (a i') ^ n.factorial ≤ V.valuation (a i) ^ n.factorial := by
    rw [he, he', zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]
    exact hmin e' ⟨i', hi', he'⟩
  by_contra hcon
  exact absurd h1 (not_le.2 (pow_lt_pow_left₀ (not_le.1 hcon) zero_le' n.factorial_ne_zero))

end GlobalTheory.ValMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrob
section
open GlobalTheory.Col PowerSeries

theorem GlobalTheory.Col.normOp_frob : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  intro R _ p _ σ hfl h
  obtain ⟨b, -⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hfl.complete
  exact GlobalTheory.Col.NormFrob.normOp_eq_smap_add p σ hfl b h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem normOp_comp : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A B C hA hB hC hAB hAC v hv
  induction hn : idx A B using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  by_cases hle : B ≤ A
  · have hAB' : A = B := by
      refine le_antisymm (fun x hx => (hB x).2 fun b hb => h.iso hA hx (hle hb)) hle
    subst hAB'
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A hA).2.2 le_rfl
    have : normOp lam W A A v = v := by
      rw [normOp, h1, map_one, inv_one, one_smul, h2 v hv]
    rw [this]
  · obtain ⟨A', hA', hadj, hbet⟩ := _root_.GlobalTheory.FinWeil.exists_adj_selfDual_step h A B hA hB hAB hle
    obtain ⟨x, hx, P, hP, hfin, hann, hgen⟩ := id hadj
    obtain ⟨e1, e2, -⟩ := _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple h A A' hA hA' x hx P hP hfin hann hgen
    have hcard : 1 < Nat.card (R ⧸ P) := by
      haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
      exact Finite.one_lt_card
    have hAA' : idx A A' ≠ 0 := by omega
    have hA'A : idx A' A ≠ 0 := by omega
    have hA'B : idx A' B ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAB
    have hA'C : idx A' C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAC
    have hmul := (_root_.GlobalTheory.FinWeil.sumOp_comp_of_between h A A' B hA hA' hB hAA' hA'B hbet).1
    have hlt : idx A' B < n := by
      rw [← hn, hmul, e1]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hA'B) hcard
    have hfix : Fixes W A' (normOp lam W A A' v) := by
      intro a ha
      rw [normOp, map_smul, ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A' hA').2.1 hAA').2.1 v hv a ha]
    rw [← _root_.GlobalTheory.FinWeil.normOp_comp_of_adj h lam hlam A A' B hA hA' hB hadj hAB v hv,
      ih _ hlt A' hA' hA'B hA'C _ hfix rfl,
      _root_.GlobalTheory.FinWeil.normOp_comp_of_adj h lam hlam A A' C hA hA' hC hadj hAC v hv]

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NqSubGalSmall
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnitStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_prime_div_zeta_sub_one_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt (p := p) y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt (p := p) (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hdiv : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2) :=
    GlobalTheory.K5.PDiv.pdiv p Ω T j 2 hj htot
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) := hdiv.mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    have : M.IsPrime := hM.isPrime
    have : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    have : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      let q := Ideal.Quotient.mk M
      change (q (ζ' - 1)) ^ (p ^ j) = 0
      rw [q.map_sub, q.map_one, sub_pow_char_pow (p := p) (q ζ') 1 j,
        ← q.map_pow, hζp, q.map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem one_sub_two_div_le_mass_true :
    ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 - 2 / (g : ℝ) ≤ mass g N fun _ => True := by
  intro g hg N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg.out.pos
  have hpow : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hterm : ∀ f ∈ sqSet g N, ((g : ℝ) ^ N)⁻¹ ≤ ((torusCard g f : ℝ))⁻¹ := by
    intro f hf
    obtain ⟨h1, h2, -⟩ := (_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 N f hf
    have h1' : (0 : ℝ) < (torusCard g f : ℝ) := by exact_mod_cast h1
    have h2' : (torusCard g f : ℝ) ≤ (g : ℝ) ^ N := by exact_mod_cast h2
    exact inv_anti₀ h1' h2'
  have hsum : ((sqSet g N).card : ℝ) * ((g : ℝ) ^ N)⁻¹ ≤ mass g N fun _ => True := by
    have h := Finset.card_nsmul_le_sum (sqSet g N) (fun f => ((torusCard g f : ℝ))⁻¹) _ hterm
    rw [nsmul_eq_mul] at h
    unfold mass
    simpa only [Finset.filter_true] using h
  refine le_trans ?_ hsum
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : (ZMod g)[X]) ∈ sqSet g 0 :=
      (GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree g 0 1).2 ⟨monic_one, natDegree_one, squarefree_one, by simp⟩
    have hc : (1 : ℝ) ≤ ((sqSet g 0).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨_, h1⟩
    have : (0 : ℝ) ≤ 2 / (g : ℝ) := by positivity
    simp only [pow_zero, inv_one, mul_one]
    linarith
  · have hc := _root_.GlobalTheory.BadShare.card_sqSet_ge g N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hc
    have he : 1 - 2 / (g : ℝ) = ((g : ℝ) ^ (M + 1) - 2 * (g : ℝ) ^ M) * ((g : ℝ) ^ (M + 1))⁻¹ := by
      field_simp
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hpow.le)

end GlobalTheory.BadShare
end

