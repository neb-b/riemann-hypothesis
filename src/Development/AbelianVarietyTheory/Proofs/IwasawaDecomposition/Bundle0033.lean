module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsDiscreteValuationRingLocalizationOfIsDedekindD
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OrdFracEqValuationInvOfIsLocalization

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.WeilDeligne

theorem frobAlg_pow_apply (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (m : ℕ) (a : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) a = a ^ (Fintype.card K ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
      ← pow_mul, pow_succ]

end GlobalTheory.WeilDeligne


open GlobalTheory.WeilDeligne Pointwise in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.WeilDeligne.exists_pow_normV_resPow (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) :
    IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω,
      g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x →
        A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  intro hA L hL g hg
  classical
  set Q := primeBelow (F := E) A with hQ
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) Q
    (by rw [show Ideal.under (𝓞 E) Q = w.asIdeal from under_primeBelow hA]
        exact w.isMaximal)
  letI : Field (IntCl E Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI : Algebra.IsIntegral (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q w.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  have hqc : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  have hq1 : 1 < normV w := one_lt_normV w

  have hgQ : g • Q = Q := by rw [hQ, ← primeBelow_smul, (mem_Dec.mp hg)]
  let ψ := Ideal.Quotient.stabilizerHom Q w.asIdeal (Ω ≃ₐ[E] Ω) ⟨g, hgQ⟩
  have hψ : ∀ b : IntCl E Ω, ψ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g • b) :=
    fun b => Ideal.Quotient.stabilizerHom_apply _ _ _ _ b

  set n := Module.finrank E L with hn
  set M := n.factorial with hM

  have hres : ∀ b : IntCl E Ω, (b : Ω) ∈ L →
      (Ideal.Quotient.mk Q b) ^ (normV w ^ M) = Ideal.Quotient.mk Q b := by
    intro b hbL
    set y := Ideal.Quotient.mk Q b with hy
    have hbi : IsIntegral (𝓞 E) (b : Ω) := b.2
    set f := minpoly (𝓞 E) (b : Ω) with hf
    have hdeg : f.natDegree ≤ n := by
      have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' E hbi
      have h2 : (minpoly E (b : Ω)).natDegree ≤ n := by
        have h3 := minpoly.algebraMap_eq (A := E) (algebraMap L Ω).injective (⟨b, hbL⟩ : L)
        rw [show (b : Ω) = algebraMap L Ω ⟨b, hbL⟩ from rfl, h3]
        exact minpoly.natDegree_le _
      rwa [h1, (minpoly.monic hbi).natDegree_map] at h2
    have hbf : Polynomial.aeval b f = 0 := by
      apply Subtype.ext
      rw [Polynomial.aeval_subalgebra_coe]
      exact minpoly.aeval _ _
    have hy0 : Polynomial.aeval y (f.map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, hy, ← Ideal.Quotient.mkₐ_eq_mk (𝓞 E),
        Polynomial.aeval_algHom_apply, hbf, map_zero]
    have hmon := (minpoly.monic hbi).map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))
    have hyInt : IsIntegral (𝓞 E ⧸ w.asIdeal) y := ⟨_, hmon, hy0⟩
    have hdvd := minpoly.dvd (𝓞 E ⧸ w.asIdeal) y hy0
    have hle : (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree ≤ n := by
      have := Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
      rw [(minpoly.monic hbi).natDegree_map] at this
      exact this.trans hdeg
    have hpos := minpoly.natDegree_pos hyInt
    set K' := IntermediateField.adjoin (𝓞 E ⧸ w.asIdeal) ({y} : Set (IntCl E Ω ⧸ Q))
    haveI : FiniteDimensional (𝓞 E ⧸ w.asIdeal) K' := IntermediateField.adjoin.finiteDimensional hyInt
    haveI : Finite K' := Module.finite_of_finite (𝓞 E ⧸ w.asIdeal)
    letI : Fintype K' := Fintype.ofFinite _
    have hcard : Fintype.card K' = normV w ^ (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree := by
      rw [Module.card_eq_pow_finrank (K := 𝓞 E ⧸ w.asIdeal), hqc,
        IntermediateField.adjoin.finrank hyInt]
    obtain ⟨m, hm⟩ := Nat.dvd_factorial hpos hle
    have key := FiniteField.pow_card_pow m
      (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : K')
    rw [hcard, ← pow_mul, ← hm] at key
    exact congrArg Subtype.val key

  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q)
  let τ := frob ^ M
  have hτ : ∀ y, τ y = y ^ (normV w ^ M) := fun y => by
    rw [frobAlg_pow_apply, hqc]
  let R := IntermediateField.fixedField (Subgroup.zpowers τ)
  have hmemR : ∀ y, y ∈ R ↔ y ^ (normV w ^ M) = y := by
    intro y
    rw [← hτ]
    constructor
    · intro h; exact (IntermediateField.mem_fixedField_iff _ _).mp h τ (Subgroup.mem_zpowers τ)
    · intro h
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have hs : τ ∈ MulAction.stabilizer
        ((IntCl E Ω ⧸ Q) ≃ₐ[𝓞 E ⧸ w.asIdeal] (IntCl E Ω ⧸ Q)) y := h
      exact (Subgroup.zpowers_le.mpr hs) hf
  have hqM : 1 < normV w ^ M := Nat.one_lt_pow (Nat.factorial_ne_zero n) hq1
  haveI : Finite R := by
    have hfin := (Polynomial.X ^ (normV w ^ M) - Polynomial.X :
      Polynomial (𝓞 E ⧸ w.asIdeal)).rootSet_finite (IntCl E Ω ⧸ Q)
    refine Set.Finite.to_subtype (hfin.subset fun y hy => ?_)
    rw [Polynomial.mem_rootSet]
    refine ⟨Polynomial.X_pow_sub_X_ne_zero hqM, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X]
    rw [(hmemR y).mp hy, sub_self]

  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 E ⧸ w.asIdeal) R).2 (ψ.restrictNormal R)
  have hj' : FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) R ^ (j : ℕ) =
      ψ.restrictNormal R := hj
  have hψR : ∀ y ∈ R, ψ y = y ^ (normV w ^ (j : ℕ)) := by
    intro y hy
    have h1 := AlgEquiv.restrictNormal_commutes ψ R ⟨y, hy⟩
    rw [← hj', frobAlg_pow_apply, hqc] at h1
    simpa [IntermediateField.algebraMap_apply] using h1.symm

  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero n)
  refine ⟨m * (j : ℕ), fun x hxL hx => ?_⟩
  let b : IntCl E Ω := ⟨x, hx.tower_top⟩
  have hbR : Ideal.Quotient.mk Q b ∈ R := (hmemR _).mpr (hres b hxL)
  have hfix : ∀ t : ℕ, (Ideal.Quotient.mk Q b) ^ (normV w ^ (M * t)) = Ideal.Quotient.mk Q b := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hres b hxL]
  have h2 : (g • b) ^ (normV w ^ (m * (j : ℕ))) - b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hψ, hψR _ hbR, ← pow_mul, ← pow_add,
      show (j : ℕ) + m * j = M * j by rw [hM, hm, Nat.succ_mul, add_comm], hfix, sub_self]
  exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
section
open Filter Topology Complex GlobalTheory.Mem.An

namespace GlobalTheory.Mem.An

section
variable {q : ℕ}

theorem zsym_gammaFactor_ne_zero (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h <;> rw [h.gammaFactor_def]
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

theorem zsym_differentiable_gammaFactor_inv (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => (χ.gammaFactor s)⁻¹) := by
  rcases χ.even_or_odd with h | h <;> simp only [h.gammaFactor_def]
  · exact differentiable_Gammaℝ_inv
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

variable [NeZero q]

theorem zsym_rootNumber_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  intro h
  have h1 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h1
  have h2 := χ.LFunction_eq_completed_div_gammaFactor (1 - -1) (Or.inl (by norm_num))
  rw [h1, zero_div] at h2
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num) h2

noncomputable def zsymFactor (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber * (χ.gammaFactor s)⁻¹ / (χ⁻¹.gammaFactor (1 - s))⁻¹

theorem zsym_eq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) : χ.LFunction s = zsymFactor χ s * χ⁻¹.LFunction (1 - s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : 1 - s ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; simp at h1
  have h2 := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h2
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0),
    χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hs1), h2, zsymFactor]
  field_simp

theorem zsymFactor_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : zsymFactor χ s ≠ 0 := by
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have g3 := zsym_rootNumber_ne_zero hχ
  have g4 : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    simp [cpow_eq_zero_iff, NeZero.ne q]
  unfold zsymFactor
  exact div_ne_zero (mul_ne_zero (mul_ne_zero g4 g3) (inv_ne_zero g1)) (inv_ne_zero g2)

theorem zsymFactor_analyticAt (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : s.re < 1) : AnalyticAt ℂ (zsymFactor χ) s := by
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have d1 : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ ((1 - s) - 1 / 2)) := by
    have : NeZero (q : ℂ) := ⟨by exact_mod_cast NeZero.ne q⟩
    fun_prop
  have d2 : Differentiable ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) :=
    (zsym_differentiable_gammaFactor_inv χ⁻¹).comp (differentiable_id.const_sub 1)
  have d3 := (d1.mul_const χ.rootNumber).mul (zsym_differentiable_gammaFactor_inv χ)
  exact (d3.analyticAt s).div (d2.analyticAt s) (inv_ne_zero g2)

theorem zsym_analyticAt_LFunction (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ χ.LFunction s := by
  refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun z hz => ?_)
    (isOpen_compl_singleton.mem_nhds hs)
  exact (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt

end

theorem zeros_symm_one_sub : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧
        zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by
  intro q _ χ hχ ρ h0 h1
  have hne := zsymFactor_ne_zero hχ h0 h1
  refine ⟨by rw [zsym_eq hχ h0 h1]; simp [hne], ?_⟩
  have hev : χ.LFunction =ᶠ[𝓝 ρ] zsymFactor χ * (χ⁻¹.LFunction ∘ fun s => 1 - s) := by
    have a : ∀ᶠ s : ℂ in 𝓝 ρ, 0 < s.re := (isOpen_lt continuous_const continuous_re).mem_nhds h0
    have b : ∀ᶠ s : ℂ in 𝓝 ρ, s.re < 1 := (isOpen_lt continuous_re continuous_const).mem_nhds h1
    filter_upwards [a, b] with s a b
    exact zsym_eq hχ a b
  have hρ : 1 - ρ ≠ 1 := by
    intro h; rw [sub_eq_self] at h; subst h; simp at h0
  have hL := zsym_analyticAt_LFunction χ⁻¹ hρ
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hf := zsymFactor_analyticAt χ h1
  unfold zmult analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hf (AnalyticAt.comp hL hg),
    hf.analyticOrderAt_eq_zero.2 hne, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)]

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers
section
open NumberField Module

namespace GlobalTheory.Mem.ImagQuad

open QuadraticZeta

theorem exists_field_sq_eq_neg (d : ℕ) (hd : 0 < d) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (r : K),
      finrank ℚ K = 2 ∧ r ^ 2 = -(d : K) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set p : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C (d : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hpmon : p.Monic := by
    rw [hp]; monicity!
  have hroot : ∀ x : ℚ, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hpdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := pb.finite
  have : NumberField (AdjoinRoot p) := ⟨⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, AdjoinRoot.root p, ?_, ?_⟩
  · rw [pb.finrank, AdjoinRoot.powerBasis_dim, hpdeg]
  · have h := AdjoinRoot.eval₂_root p
    simp only [hp, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero, ← h]
    simp

theorem exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by
  intro d hdp hd4
  obtain ⟨K, _, _, r, h2, hr⟩ := exists_field_sq_eq_neg d hdp.pos
  have hsq : Squarefree d := hdp.squarefree
  obtain ⟨w, bar, hw, -, hspan, hemb, -⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d hsq hd4 K h2 r hr
  have hwr : 2 * (w : K) - 1 = r := by rw [hw]; ring
  have hcoe : algebraMap (𝓞 K) K (2 * w - 1) = r := by
    rw [← hwr]
    simp only [map_sub, map_mul, map_one, map_ofNat]
  have hw2 : (2 * w - 1) ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hcoe, hr, map_neg, map_natCast]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hwsq : w * w = w - (k : 𝓞 K) := by
    have h4 : (4 : 𝓞 K) * (w * w - w + k) = 0 := by
      have : ((d : ℕ) : 𝓞 K) + 1 = 4 * (k : 𝓞 K) := by exact_mod_cast hk
      linear_combination hw2 - this
    have h4ne : (4 : 𝓞 K) ≠ 0 := by
      intro h
      have : ((4 : 𝓞 K) : K) = 0 := by rw [h]; simp
      norm_num at this
    have := (mul_eq_zero.mp h4).resolve_left h4ne
    linear_combination this
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) + t * (w : K) = 0 := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := by
      by_contra ht
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      set q : ℚ := -(2 * s + t) / t with hqdef
      have hrq : r = algebraMap ℚ K q := by
        simp only [hqdef, map_div₀, map_neg, map_add (f := _), map_mul, map_ofNat, map_intCast]
        field_simp
        linear_combination (2 : K) * hK + (-(t : K)) * hwr
      have hq : q ^ 2 = -(d : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hrq, hr]
        simp
      have hdpos : (0 : ℚ) < d := by exact_mod_cast hdp.pos
      nlinarith [sq_nonneg q]
    subst ht
    refine ⟨?_, rfl⟩
    have : (s : K) = 0 := by simpa using hK
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspan z
    have hr' : Set.range ![(1 : 𝓞 K), w] = {1, w} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hr', Submodule.mem_span_pair]
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let B := Basis.mk hli hsp
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = w := by simp [B]
  have hrepr : ∀ s t : ℤ, B.repr ((s : 𝓞 K) + t * w) = Finsupp.single 0 s + Finsupp.single 1 t := by
    intro s t
    have : (s : 𝓞 K) + t * w = s • B 0 + t • B 1 := by
      rw [hB0, hB1]; simp [zsmul_eq_mul]
    rw [this, map_add (f := _), map_zsmul, map_zsmul, B.repr_self, B.repr_self]
    simp
  refine ⟨K, inferInstance, inferInstance, w, ?_, h2, ?_, hw2, hspan, ?_⟩
  · refine ⟨fun v => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    exact (hemb v.embedding).1
  · exact GlobalTheory.discr_eq_neg_of_sq_eq h2 hsq hd4 hr
  · intro a b
    rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
    have e00 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 0 = a := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have e10 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 0 = b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one, hrepr]; simp
    have hx1 : ((a : 𝓞 K) + b * w) * w = ((-(b * k) : ℤ) : 𝓞 K) + ((a + b : ℤ) : 𝓞 K) * w := by
      push_cast
      linear_combination (b : 𝓞 K) * hwsq
    have e01 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 0 1 = -(b * k) := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    have e11 : Algebra.leftMulMatrix B ((a : 𝓞 K) + b * w) 1 1 = a + b := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hx1, hrepr]; simp
    rw [e00, e10, e01, e11]
    have hk' : (d : ℤ) + 1 = 4 * k := by exact_mod_cast hk
    linear_combination (-(b ^ 2) : ℤ) * hk'

end GlobalTheory.Mem.ImagQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReversedCharpolyCoeffNotMemPrimeStatement
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  first | exact @GlobalTheory.NormalDescent.exists_normCoeff_not_mem | exact GlobalTheory.NormalDescent.exists_normCoeff_not_mem | (intros; apply GlobalTheory.NormalDescent.exists_normCoeff_not_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
section
open NumberField IsDedekindDomain IsLocalRing IsDiscreteValuationRing

namespace GlobalTheory

namespace OrderNorm

theorem length_quot_ringEquiv {T U : Type*} [CommRing T] [CommRing U] (e : T ≃+* U) (x : T) :
    Module.length T (T ⧸ Ideal.span {x}) = Module.length U (U ⧸ Ideal.span {e x}) := by
  let _ : Algebra T U := e.toRingHom.toAlgebra
  let f : T ≃ₐ[T] U := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (f : T →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [(Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hI).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

end OrderNorm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
section
namespace GlobalTheory.Mem.An

theorem _root_.GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    linarith
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffMapOfIsPushoutStatement
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | exact GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.normCoeff_map_of_isPushout <;> assumption)
end

