module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Homog

variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem weight_blockSingle (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

theorem isMultiHomog_iff_weighted (f : MRingOver R ι) (a : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  constructor
  · intro h d hd
    rw [weight_blockSingle]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_blockSingle] at this
    exact congrFun this k

end Homog

section Subst

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem aeval_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by
  have h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
      MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) =
      (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      split_ifs with h h'
      · rw [aeval_C, ← G.compat, h'.choose_spec]
      · exact absurd (hv.2.2.2 q h) h'
      · rw [aeval_X]
  exact DFunLike.congr_fun h f

theorem baseSubst_isMultiHomog (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by
  classical
  rw [isMultiHomog_iff_weighted] at hs ⊢
  have hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous
      (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ))
      (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
        else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ))
      (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) := by
    intro q
    by_cases h : q.1 ∈ Set.range κ
    · have h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0 := by
        funext k
        have : k.1 ≠ q.1 := fun e => k.2 (e ▸ h)
        simp [this]
      rw [dite_eq_left h, h0]
      split_ifs
      · exact isWeightedHomogeneous_C _ _
      · exact isWeightedHomogeneous_zero _ _ _
    · rw [dite_eq_right h]
      have e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) =
          (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ) := by
        funext k
        simp [Pi.single_apply, Subtype.ext_iff]
      rw [e]
      exact isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)
  induction hs using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add (f := _)]; exact ihp.add ihq
  | monomial d r hr =>
    unfold baseSubst
    rw [coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]
    convert ((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1
    funext k
    rw [← hr]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

end Subst

theorem PFFibreSum.proof (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRSlotAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_metric {D : ℕ} {A : HermLine ι} (hA : IsSmoothHerm A)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ A.h (γ y) := hA.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (A.pos _ hy).ne')) 2

theorem cxHessian_pot_snoc {n : ℕ} (L : Fin n → HermLine ι) (A X : HermLine ι)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian (fun y' => pot (Fin.snoc L X) k (γ y')) y) =
      Function.update (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
        (cxHessian (fun y' => Real.log (X.h (γ y'))) y) := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp only [pot, Fin.snoc_castSucc]
  · rw [Function.update_self]
    simp only [pot, Fin.snoc_last]

theorem maDensity_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) {A C : HermLine ι}
    (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => pot (Fin.snoc L (A.tensor C)) j (γ y')) y =
      maDensity (fun j y' => pot (Fin.snoc L A) j (γ y')) y +
        maDensity (fun j y' => pot (Fin.snoc L C) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hA (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (C.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hC (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((A.tensor C).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (A.h (γ y')) + 1 * Real.log (C.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (A.pos _ hy'.2).ne' (C.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simp only [Complex.ofReal_one, one_smul] at hH
  unfold maDensity
  rw [cxHessian_pot_snoc L A (A.tensor C), cxHessian_pot_snoc L A C, hH]
  have hm := ReciprocityTheory.AnForm.A.mdisc_update_add
    (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
    (cxHessian (fun y' => Real.log (A.h (γ y'))) y) (cxHessian (fun y' => Real.log (C.h (γ y'))) y)
  change mixedDisc _ = mixedDisc _ + mixedDisc _ at hm
  rw [← cxHessian_pot_snoc L A A γ y] at hm
  rw [hm, Complex.add_re, mul_add]

theorem sheetDensity_snoc_tensor (P : Ideal (MRing ι)) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot (Fin.snoc L (A.tensor C))) g y w =
      sheetDensity P Ψ (pot (Fin.snoc L A)) g y w + sheetDensity P Ψ (pot (Fin.snoc L C)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_snoc_tensor L hA hC hγ, mul_add]
  · simp only [dif_neg h, add_zero]

theorem arInt_snoc_tensor (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement)
    {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) {A C B : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hC : IsSmoothHerm C) (hB : IsSmoothHerm B) (hs : IsSectionOn P B s) :
    arInt P s B (Fin.snoc L (A.tensor C)) =
      arInt P s B (Fin.snoc L A) + arInt P s B (Fin.snoc L C) := by
  change ptsIntegral P (pot (Fin.snoc L (A.tensor C))) (logNorm B s) =
    ptsIntegral P (pot (Fin.snoc L A)) (logNorm B s) + ptsIntegral P (pot (Fin.snoc L C)) (logNorm B s)
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · rw [dif_pos hΨ, dif_pos hΨ, dif_pos hΨ]
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X →
        ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j) := by
      intro X hX j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using hL j
      · simpa only [Fin.snoc_last] using hX
    have iA := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L A) B s hP hΨ.choose_spec (hsm A hA) hB hs
    have iC := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L C) B s hP hΨ.choose_spec (hsm C hC) hB hs
    unfold ptsIntegralAt
    rw [← integral_add iA iC]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (hFF K ι P (n + 1) hΨ.choose hP hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => sheetDensity_snoc_tensor P hΨ.choose L hA hC _ y w
  · rw [dif_neg hΨ, dif_neg hΨ, dif_neg hΨ, add_zero]


omit [∀ k, Fintype (ι k)] in
theorem geoNum_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) (A C : HermLine ι) (W : Ideal (MRing ι)) :
    geoNum (n + 1) W (fun j => ((Fin.snoc L (A.tensor C) : Fin (n + 1) → HermLine ι) j).a) =
      geoNum (n + 1) W (fun j => ((Fin.snoc L A : Fin (n + 1) → HermLine ι) j).a) + geoNum (n + 1) W (fun j => ((Fin.snoc L C : Fin (n + 1) → HermLine ι) j).a) := by
  have hi : ∀ X : HermLine ι, Fin.init (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) = fun j => (L j).a := by
    intro X; funext j; simp only [Fin.init, Fin.snoc_castSucc]
  simp only [geoNum]
  split_ifs with h
  · simp only [hi, Fin.snoc_last, HermLine.tensor, Pi.add_apply, ← Finset.sum_add_distrib, add_mul]
  · simp


open Classical in
theorem RPositionAdd.proof (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement) :
    RPositionAdd.Statement := by
  intro K _ ι _ I P n L A C B s hI hP hL hA hC hB hs
  let term : HermLine ι → Ideal (MRing ι) → ℝ := fun X W =>
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W (n + 1) (Fin.snoc L X)
        else (geoNum (n + 1) W (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) : ℝ) * Real.log (charOf W))
  have e : ∀ X, recR I P (Fin.snoc L X) B s =
      (∑ᶠ W ∈ divSupp P s, term X W) - arInt P s B (Fin.snoc L X) := fun X => rfl
  have key : ∀ W ∈ divSupp P s, term (A.tensor C) W = term A W + term C W := by
    intro W hW
    simp only [term]
    split_ifs with hh
    · rw [hI W L A C ((divSuppArith K ι P (n + 1) B s W hP hs hW).1 hh) hL hA hC]; ring
    · rw [geoNum_snoc_tensor L A C W]; push_cast; ring
  rw [e, e, e, finsum_mem_congr rfl key, finsum_mem_add_distrib (divSupp_finite P s),
    arInt_snoc_tensor hFF hInt L hP hL hA hC hB hs]
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRegCurvBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian RegularizedCurvature MvPolynomial

theorem RegCurvBound.proof (hB : TorusInvLevi.Statement) : RegCurvBound.Statement := by
  intro K _ ι _ E t ht hE
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  have hlogH : ∀ M : HermLine ι, IsSmoothHerm M → ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun M hM z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (E.h y) + ∑ k, (-(E.a k : ℝ)) * F k y with hu
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(E.a k : ℝ)) (hlogH E hE z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι := ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι := ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (E.h (fun p => c p.1 * z p)) =
        ∑ k, (E.a k : ℝ) * Real.log ‖c k‖ + Real.log (E.h z) := by
      rw [E.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (E.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (E.h (fun p => c p.1 * z p)) + ∑ k, (-(E.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (E.h z) + ∑ k, (-(E.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_const] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(E.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (E.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(E.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(E.a k : ℝ)| ≤ ∑ k, |(E.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(E.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (E.a k : ℝ)
    linarith
  refine ⟨N, fun ε hε => ?_⟩
  set R : HermLine ι := regLine E t ht ε with hR
  have hRs : IsSmoothHerm R := isSmoothHerm_regLine hE hε
  intro z hz v
  have hW0 : 0 ≤ ∑ k, ReciprocityTheory.AnForm.levi (F k) z v :=
    Finset.sum_nonneg fun k _ => levi_F_nonneg hz k v

  have hLW : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    have hs := levi_add_sum u F (fun k => (E.a k : ℝ)) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    have hfun : (fun y => u y + ∑ k, (E.a k : ℝ) * F k y) = fun y => Real.log (E.h y) := by
      funext y
      simp only [hu, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hfun] at hs
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, (E.a k : ℝ) * ReciprocityTheory.AnForm.levi (F k) z v + N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    rw [hs.2]
    linarith

  have hΦ1 : ContDiffAt ℝ 2 (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) z :=
    (hlogH E hE z hz).add (contDiffAt_const.mul (hlogH R hRs z hz))
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := levi_logSum (h := E.h)
    (T := fun y => eval y (map (Int.castRingHom ℂ) t))
    (Φ := fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) (hlogH E hE z hz)
    (by filter_upwards [hUo.mem_nhds hz] with y hy; exact E.pos y hy) (analyticAt_eval_map t z) hε hΦ1
    (fun y => by rw [hR, log_regLine_h, secNorm, one_mul]) v

  have hs := levi_add_sum (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) F (fun _ => (N : ℝ)) hΦ1
    (contDiffAt_F hz) v Finset.univ
  have hev : (fun y => Real.log (((E.tensor R).tensor
      (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (N : ℤ)))).h y)) =ᶠ[𝓝 z]
      fun y => (Real.log (E.h y) + 1 * Real.log (R.h y)) + ∑ k, (N : ℝ) * F k y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    show Real.log ((E.h y * R.h y) * ∏ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ^ ((N : ℤ))) = _
    rw [Real.log_mul (mul_pos (E.pos y hy) (R.pos y hy)).ne'
        (Finset.prod_pos fun k _ => zpow_pos (rho_pos hy k) _).ne',
      Real.log_mul (E.pos y hy).ne' (R.pos y hy).ne',
      Real.log_prod (fun k _ => (zpow_pos (rho_pos hy k) _).ne')]
    simp only [Real.log_zpow, F, Int.cast_natCast, one_mul]
  rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2,
    ← Finset.mul_sum]
  have hmu : 0 ≤ μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    rcases le_or_gt 0 (ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v) with hL0 | hL0
    · exact add_nonneg (mul_nonneg hμ0 hL0) (mul_nonneg (Nat.cast_nonneg _) hW0)
    · nlinarith
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def LocRingDimOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsMultiProjPrime P → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsNoetherianRing (locRing P W) ∧ IsLocalRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end GroundTheory.Heights₂.Heights.Inter
end
end

