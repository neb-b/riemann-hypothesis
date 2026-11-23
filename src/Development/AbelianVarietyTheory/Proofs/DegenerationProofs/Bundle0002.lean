module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompositumFiniteNormalIsPGroup
section
namespace GlobalTheory

open IntermediateField Polynomial

theorem compositum_finite_normal_isPGroup (K K' Ω : Type) [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ)
    (L : IntermediateField K Ω) (hfin : FiniteDimensional K L) (hn : Normal K L)
    (hp : IsPGroup l (L ≃ₐ[K] L)) :
    FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K']
        IntermediateField.adjoin K' (L : Set Ω)) := by
  obtain ⟨p, hsp⟩ := Normal.exists_isSplittingField K L
  obtain ⟨hs, hL⟩ := IntermediateField.isSplittingField_iff.mp hsp
  have hsΩ : (p.map (algebraMap K Ω)).Splits := by
    have := hs.map (algebraMap L Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hmm : (p.map (algebraMap K K')).map (algebraMap K' Ω) = p.map (algebraMap K Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : (p.map (algebraMap K K')).rootSet Ω = p.rootSet Ω := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmm]
  have hE : IntermediateField.adjoin K' (L : Set Ω) =
      IntermediateField.adjoin K' ((p.map (algebraMap K K')).rootSet Ω) := by
    rw [hroot]
    conv_lhs => rw [hL]
    exact IntermediateField.adjoin_adjoin_right _ _
  have hsp' : (p.map (algebraMap K K')).IsSplittingField K'
      (IntermediateField.adjoin K' (L : Set Ω)) := by
    rw [hE]
    exact IntermediateField.adjoin_rootSet_isSplittingField (by rw [hmm]; exact hsΩ)
  refine ⟨Polynomial.IsSplittingField.finiteDimensional _ (p.map (algebraMap K K')),
    Normal.of_isSplittingField (p.map (algebraMap K K')), ?_⟩
  set E := IntermediateField.adjoin K' (L : Set Ω) with hEdef
  let i : L →ₐ[K] E :=
    { toFun := fun x => ⟨x, IntermediateField.subset_adjoin K' _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  letI : Algebra L E := i.toRingHom.toAlgebra
  haveI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  let r : (E ≃ₐ[K'] E) →* (E ≃ₐ[K] E) :=
    { toFun := fun g => g.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : (E ≃ₐ[K'] E) →* (L ≃ₐ[K] L) := (AlgEquiv.restrictNormalHom L).comp r
  refine hp.of_injective φ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : L, g (i x) = i x := by
    intro x
    have h1 := AlgEquiv.restrictNormal_commutes (r g) L x
    have h2 : (r g).restrictNormal L = 1 := hg
    rw [h2] at h1
    exact h1.symm
  have : (g : E →ₐ[K'] E) = AlgHom.id K' E :=
    IntermediateField.adjoin_algHom_ext K' fun x hx => hfix ⟨x, hx⟩
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun this x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ConeClosureArcOfIntegralImageReduction
section
open scoped BigOperators

namespace GlobalTheory

theorem exists_common_nat_denominator {R F α : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (g : α → F) (S : Finset α) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ S, ∃ r : R, φ r = n * g s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨n, hn, hS⟩ := ih
    obtain ⟨r, m, hm, hr⟩ := h (g a)
    refine ⟨n * m, Nat.mul_pos hn hm, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨n * r, by rw [map_mul, map_natCast, hr]; push_cast; ring⟩
    · obtain ⟨r', hr'⟩ := hS s hs
      exact ⟨m * r', by rw [map_mul, map_natCast, hr']; push_cast; ring⟩

theorem exists_homogeneous_lift_nat_mul {R F J : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (G : MvPolynomial J F) (d : ℕ)
    (hG : G.IsHomogeneous d) :
    ∃ (n : ℕ) (G' : MvPolynomial J R), 0 < n ∧ G'.IsHomogeneous d ∧
      MvPolynomial.map φ G' = (n : MvPolynomial J F) * G := by
  classical
  obtain ⟨n, hn, hS⟩ := exists_common_nat_denominator φ h (fun s => G.coeff s) G.support
  choose! r hr using hS
  refine ⟨n, ∑ s ∈ G.support, MvPolynomial.monomial s (r s), hn, ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      conv_rhs => rw [G.as_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [MvPolynomial.map_monomial, hr s hs, ← map_natCast (MvPolynomial.C : F →+* MvPolynomial J F),
        MvPolynomial.C_mul_monomial]

theorem cone_closure_arc_of_integral_image_reduction :
    (∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W) → (∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ) → ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∀ (K J ι : Type) [Field K] [CharZero K] [Fintype J] [Finite ι] (ψ : R →+* K), (∀ r, φ r = 0 → ψ r = 0) → ∀ (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℚ (A i)], (∀ i, Algebra.FiniteType ℚ (A i)) → ∀ (χ : ∀ i, R →+* A i), (∀ i r, φ r = 0 → χ i r = 0) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J R) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.eval₂ (χ i) (w i) G = 0) → MvPolynomial.eval₂ ψ v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ r : R, f (χ i r) = algebraMap W (FractionRing W) (algebraMap K W (ψ r))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro H1 H2 R _ φ hφ K J ι _ _ _ _ ψ hψ A _ _ hA χ hχ w v hv hG
  obtain ⟨F, _, _, φ', hF, hlift⟩ := H2 R φ hφ
  obtain ⟨ψ', hψ'⟩ := hlift K ψ hψ
  choose χ' hχ' using fun i => hlift (A i) (χ i) (hχ i)
  letI : Algebra F K := ψ'.toAlgebra
  letI : ∀ i, Algebra F (A i) := fun i => (χ' i).toAlgebra
  have hA' : ∀ i, Algebra.FiniteType F (A i) := fun i => by
    haveI : IsScalarTower ℚ F (A i) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI := hA i
    exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ F (A i)
  obtain ⟨i, W, _, _, _, _, f, s, w', h1, h2, h3, h4⟩ := H1 F K J ι A hA' w v hv (by
    intro G d hd h0
    obtain ⟨n, G', hn, hG', hmap⟩ := exists_homogeneous_lift_nat_mul φ' hF G d hd
    have key := hG G' d hG' (fun i => by
      have : MvPolynomial.eval₂ (χ i) (w i) G'
          = MvPolynomial.aeval (w i) (MvPolynomial.map φ' G') := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hχ' i]; rfl
      rw [this, hmap, map_mul, h0 i, mul_zero])
    have : MvPolynomial.eval₂ ψ v G' = MvPolynomial.aeval v (MvPolynomial.map φ' G') := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hψ']; rfl
    rw [this, hmap, map_mul, map_natCast] at key
    exact (mul_eq_zero.1 key).resolve_left (Nat.cast_ne_zero.2 hn.ne'))
  refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance, f, s, w', h1, h2, fun r => ?_, h4⟩
  have := h3 (φ' r)
  rw [← hχ' i, ← hψ']
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOnPoints
section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.EqualityOnPoints

theorem eq_on_points {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by

  set l := pullback.lift a b h with hl
  have hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s)) :=
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous

  have he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hi]
  have hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(i ≫ a) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]

  have hall : l x ∈ Set.range (pullback.diagonal s) := by
    have hcl' := hcl.closure_subset_iff.2 hsub
    rw [i.denseRange.closure_range] at hcl'
    exact hcl' (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hall
  have ha : a x = y := by
    have e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_fst, hl, pullback.lift_fst] at e
    simpa using e.symm
  have hb : b x = y := by
    have e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_snd, hl, pullback.lift_snd] at e
    simpa using e.symm
  rw [ha, hb]

end GlobalTheory.EqualityOnPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation
section
namespace GlobalTheory.PadicVal

variable {p : ℕ} [Fact p.Prime]

theorem exists_rat_log (x : PadicAlgCl p) (hx : x ≠ 0) : ∃ q : ℚ, Real.log ‖x‖ = q * Real.log p := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hn : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨((-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ) : ℚ) / ((minpoly ℚ_[p] x).natDegree : ℚ), ?_⟩
  rw [hn, Real.log_rpow (norm_pos_iff.2 hc), Padic.norm_eq_zpow_neg_valuation hc, Real.log_zpow]
  push_cast
  ring


open Classical in
theorem exists_addValuation (π : PadicAlgCl p) (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ x, x ≠ 0 →
      ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖ := by
  classical
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have hex : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ q : ℚ, Real.log ‖x‖ = q * Real.log ‖π‖ := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rat_log x hx
    obtain ⟨b, hb⟩ := exists_rat_log π (norm_pos_iff.1 h0)
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hb
      exact hL.ne hb
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hb
      exact hL.ne hb
    refine ⟨a / b, ?_⟩
    rw [ha, hb]
    push_cast
    field_simp
  let r : PadicAlgCl p → ℚ := fun x => if hx : x = 0 then 0 else Classical.choose (hex x hx)
  have hr : ∀ x, x ≠ 0 → Real.log ‖x‖ = r x * Real.log ‖π‖ := by
    intro x hx
    simp only [r, dif_neg hx]
    exact Classical.choose_spec (hex x hx)
  have hr' : ∀ x, x ≠ 0 → (r x : ℝ) = Real.log ‖x‖ / Real.log ‖π‖ := by
    intro x hx
    rw [hr x hx, mul_div_cancel_right₀ _ hL.ne]
  let f : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ)
  have f_ne : ∀ x, x ≠ 0 → f x = (r x : WithTop ℚ) := fun x hx => if_neg hx
  have f_zero : f 0 = ⊤ := if_pos rfl
  refine ⟨AddValuation.of f f_zero ?_ ?_ ?_, ?_⟩
  · have h : (r 1 : ℝ) = 0 := by
      rw [hr' 1 one_ne_zero, norm_one, Real.log_one, zero_div]
    rw [f_ne 1 one_ne_zero, Rat.cast_eq_zero.1 h]
    rfl
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [f_zero, zero_add]
      exact min_le_right _ _
    by_cases hy : y = 0
    · subst hy
      rw [f_zero, add_zero]
      exact min_le_left _ _
    by_cases hxy : x + y = 0
    · rw [hxy, f_zero]
      exact le_top
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
      ← Rat.cast_le (K := ℝ), Rat.cast_min, hr' x hx, hr' y hy, hr' _ hxy]
    have hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    have hpos : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
    rcases le_total ‖y‖ ‖x‖ with h | h
    · rw [max_eq_left h] at hle
      exact (min_le_left _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
    · rw [max_eq_right h] at hle
      exact (min_le_right _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [zero_mul, f_zero, top_add]
    by_cases hy : y = 0
    · subst hy
      rw [mul_zero, f_zero, add_top]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have h : (r (x * y) : ℝ) = r x + r y := by
      rw [hr' _ hxy, hr' x hx, hr' y hy, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div]
    exact_mod_cast h
  · intro x hx
    exact ⟨r x, f_ne x hx, hr x hx⟩

theorem tendsto_of_null {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    {v : AddValuation (PadicAlgCl p) (WithTop ℚ)}
    (hv : ∀ x, x ≠ 0 → ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖)
    {I : Type} {x : I → PadicAlgCl p} (hx : ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite) :
    Filter.Tendsto x Filter.cofinite (nhds 0) := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_gt (Real.log ε / Real.log ‖π‖)
  rw [Filter.eventually_cofinite]
  refine (hx q).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hlt
  apply hi
  rw [dist_zero_right, norm_norm]
  by_cases hxi : x i = 0
  · rw [hxi, norm_zero]
    exact hε
  obtain ⟨q', hv', hlog⟩ := hv (x i) hxi
  have hqq : q ≤ q' := by
    rw [hv', not_lt, WithTop.coe_le_coe] at hlt
    exact hlt
  have h2 : (q' : ℝ) * Real.log ‖π‖ ≤ q * Real.log ‖π‖ :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hqq) hL.le
  have h3 : (q : ℝ) * Real.log ‖π‖ < Real.log ε := (div_lt_iff_of_neg hL).1 hq
  have h4 : Real.log ‖x i‖ < Real.log ε := by linarith
  exact (Real.log_lt_log_iff (norm_pos_iff.2 hxi) hε).1 h4

theorem summable_of_mem (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {I : Type} {x : I → PadicAlgCl p} (hK : ∀ i, x i ∈ K) (hx : Filter.Tendsto x Filter.cofinite (nhds 0)) :
    Summable x := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  let y : I → K := fun i => ⟨x i, hK i⟩
  have hy : Filter.Tendsto y Filter.cofinite (nhds 0) := by
    rw [tendsto_subtype_rng]
    exact hx
  have hs : Summable y := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hy
  exact hs.map K.val continuous_subtype_val

end GlobalTheory.PadicVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomLocalizationAwayOfRationalPoints
section
namespace GlobalTheory

open Polynomial

theorem localizationAway_eq_zero_of_forall_eval {k : Type} [Field k] [Infinite k]
    (D : Polynomial k) (hD : D ≠ 0) (b : Localization.Away D)
    (h : ∀ t, D.eval t ≠ 0 → ∀ e : Localization.Away D →+* k,
      (∀ q, e (algebraMap (Polynomial k) _ q) = q.eval t) → e b = 0) : b = 0 := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj D b
  have hq0 : q * D = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : D.eval t = 0
    · rw [ht, mul_zero]
    · have hu : IsUnit (Polynomial.evalRingHom t D) := isUnit_iff_ne_zero.mpr ht
      have he : ∀ q, (IsLocalization.Away.lift (S := Localization.Away D) D hu)
          (algebraMap (Polynomial k) _ q) = q.eval t := fun q =>
        IsLocalization.Away.lift_eq D hu q
      have h0 := h t ht _ he
      have h1 := congrArg (IsLocalization.Away.lift (S := Localization.Away D) D hu) hq
      rw [map_mul, h0, zero_mul, he] at h1
      rw [← h1, zero_mul]
  have hq1 : q = 0 := (mul_eq_zero.mp hq0).resolve_right hD
  rw [hq1, map_zero] at hq
  exact ((IsLocalization.Away.algebraMap_isUnit D).pow n).mul_left_eq_zero.mp hq

theorem exists_algHom_localizationAway_of_rational_points :
    ∀ (k : Type) [Field k] [Infinite k] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → Pd ≠ 0 → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → ∃ χ : A →ₐ[k] Localization.Away (Polynomial.X * Pd), ∀ i, χ (f i) * algebraMap (Polynomial k) _ Pd = algebraMap (Polynomial k) _ (P i) := by
  intro k _ _ A _ _ r f Pd P ψ hf hPd hψ
  have hD : (Polynomial.X * Pd : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  obtain ⟨u, hu⟩ : ∃ u : Localization.Away (Polynomial.X * Pd),
      u * algebraMap (Polynomial k) _ Pd = 1 := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)
    rw [map_mul] at h
    exact (isUnit_of_mul_isUnit_right h).exists_left_inv
  let Θ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away (Polynomial.X * Pd) :=
    MvPolynomial.aeval fun i => algebraMap (Polynomial k) _ (P i) * u
  have hsurj : Function.Surjective (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hf]
  have hker : ∀ p, MvPolynomial.aeval f p = 0 → Θ p = 0 := by
    intro p hp
    apply localizationAway_eq_zero_of_forall_eval _ hD
    intro t ht e he
    rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
    have ht0 : t ≠ 0 := left_ne_zero_of_mul ht
    have ht1 : Pd.eval t ≠ 0 := right_ne_zero_of_mul ht
    have key : ∀ p, e (Θ p) = ψ t (MvPolynomial.aeval f p) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C, AlgHom.commutes,
          IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.X * Pd)),
          he]
        simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | mul_X p i hp =>
        rw [map_mul, map_mul, map_mul, map_mul, hp]
        congr 1
        have h1 := congrArg e hu
        rw [map_mul, he, map_one] at h1
        simp only [Θ, MvPolynomial.aeval_X, map_mul, he]
        rw [← hψ t ht0 ht1 i, mul_assoc, mul_comm (Pd.eval t), h1, mul_one]
    rw [key, hp, map_zero]
  have hle : RingHom.ker (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A).toRingHom ≤
      RingHom.ker Θ.toRingHom := fun p hp => hker p hp
  refine ⟨AlgHom.liftOfSurjective _ hsurj Θ hle, fun i => ?_⟩
  have h2 : f i = MvPolynomial.aeval f (MvPolynomial.X i : MvPolynomial (Fin r) k) := by simp
  rw [h2]
  erw [AlgHom.liftOfSurjective_apply]
  simp only [Θ, MvPolynomial.aeval_X]
  rw [mul_assoc, hu, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
section
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_algHom_of_finiteType_of_isAlgClosed (K C F : Type) [Field K] [CommRing C]
    [Nontrivial C] [Algebra K C] [Algebra.FiniteType K C] [Field F] [IsAlgClosed F]
    [Algebra K F] : Nonempty (C →ₐ[K] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsEqDivOfIsPullback
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.SS

theorem exists_eq_div_of_isPullback : ∀ (P X Y S : Scheme.{0}) [IsAffine S] (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S), IsPullback p q f g → ∀ (z : P) (U : X.Opens) (U' : Y.Opens) (W : P.Opens), p z ∈ U → q z ∈ U' → z ∈ W → ∃ (V : X.Opens) (V' : Y.Opens) (W' : P.Opens) (h₁ : W' ≤ p ⁻¹ᵁ V) (h₂ : W' ≤ q ⁻¹ᵁ V'), V ≤ U ∧ V' ≤ U' ∧ W' ≤ W ∧ z ∈ W' ∧ ∀ τ : Γ(P, W'), ∃ a ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), ∃ b ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), IsUnit a ∧ τ * a = b := by
  intro P X Y S _ p q f g H z U U' W hU hU' hW
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) hU
  obtain ⟨V', hV', hpV', hVU'⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := U') hU'
  have hP : IsAffineOpen (p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V') := by
    have : IsAffine _ := hV
    have : IsAffine _ := hV'
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V') (UX := V) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V') (UX := V) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV' hV)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  obtain ⟨r, hrW, hzr⟩ := hP.exists_basicOpen_le (V := W) ⟨z, hW⟩ ⟨hpV, hpV'⟩
  have hle : P.basicOpen r ≤ p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V' := P.basicOpen_le r
  refine ⟨V, V', P.basicOpen r, hle.trans inf_le_left, hle.trans inf_le_right, hVU, hVU', hrW,
    hzr, fun τ => ?_⟩
  have key : ∀ x : Γ(P, p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V'), (P.presheaf.map (homOfLE hle).op).hom x ∈
      Subring.closure (Set.range (p.appLE V _ (hle.trans inf_le_left)).hom ∪
        Set.range (q.appLE V' _ (hle.trans inf_le_right)).hom) := by
    intro x
    have hx := hgen.ge (Subring.mem_top x)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ hx)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · refine Subring.subset_closure (Or.inr ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hloc := hP.isLocalization_basicOpen r
  obtain ⟨⟨b, a⟩, hab⟩ := IsLocalization.surj (Submonoid.powers r) τ
  exact ⟨_, key a, _, key b, IsLocalization.map_units Γ(P, P.basicOpen r) a, hab⟩

end GlobalTheory.SS
end

