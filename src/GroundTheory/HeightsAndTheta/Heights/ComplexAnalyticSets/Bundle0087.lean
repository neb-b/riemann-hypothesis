module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermWeierstrassPreparation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCircleArgumentPrinciple
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffFinite.proof (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace CutOffDominated

variable {n d : ℕ}

theorem chartDens_congr_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0 :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

end CutOffDominated

theorem CutOffDominated.proof : CutOffDominated.Statement := by
  classical
  intro n d J A P χ f ψ hJ hdim hA hP hχm hχ01 hlim hf hψ hint
  have hfin : ∀ y, (fibre J A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
  set g : (Fin n → ℂ) → ℝ := (zeroSet J).piecewise f 0 with hgdef
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : ∀ k, Measurable (chartDens J A (fun x => χ k x * f x) ψ) := fun k => by
    rw [CutOffDominated.chartDens_congr_zeroSet (g := fun x => χ k x * g x)
      (fun x hx => by rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hx])]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA ((hχm k).mul hg) hψ).1
  refine tendsto_integral_of_dominated_convergence (chartAbsDens J A f ψ)
    (fun k => (hmeas k).aestronglyMeasurable) hint (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with h
    · rw [mul_assoc, abs_mul, abs_of_nonneg (hχ01 k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 k x).2
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    have hxl := hlim x hx.1 (by rw [show A *ᵥ x = y from hx.2]; exact hy)
    split_ifs with h
    · simpa using (hxl.mul_const (f x)).mul_const
        (ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ h.choose) y)
    · exact tendsto_const_nhds

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsUFD
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem coe_mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ((mkGerm f hf : holGerms (0 : τ → ℂ)) : Germ (𝓝 (0 : τ → ℂ)) ℂ) = ↑f := rfl

theorem isUnit_mkGerm {τ : Type} [Fintype τ] (e : (τ → ℂ) → ℂ) (he : AnalyticAt ℂ e 0) (he0 : e 0 ≠ 0) :
    IsUnit (mkGerm e he) := by
  refine IsUnit.of_mul_eq_one (mkGerm (fun x => (e x)⁻¹) (he.inv he0)) (Subtype.ext ?_)
  show ((fun x => e x * (e x)⁻¹ : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ) =
    ((fun _ => (1 : ℂ) : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ)
  exact Germ.coe_eq.2 (by
    filter_upwards [he.continuousAt.eventually_ne he0] with x hx
    exact mul_inv_cancel₀ hx)

theorem uniqueFactorizationMonoid_holGerms_option (hN : AnalyticGermsNoetherian.Statement)
    (hG : GeneralLinearCoordinates.Statement) (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassDivision.Statement) (σ : Type) [Fintype σ]
    (hR : UniqueFactorizationMonoid (holGerms (0 : σ → ℂ))) :
    UniqueFactorizationMonoid (holGerms (0 : Option σ → ℂ)) := by
  have := hN (Option σ) 0
  have := hR
  refine { irreducible_iff_prime := fun {φ} => ⟨fun hφ => ?_, Prime.irreducible⟩ }
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := fun h =>
    hφ.ne_zero (Subtype.ext (by rw [← hfφ]; exact Germ.coe_eq.2 h))
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz
  have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)

  have hT : germAffineEquiv A (0 : Option σ → ℂ) φ = mkGerm (f ∘ A) hfA := by
    apply Subtype.ext
    show ((germPull (fun z : Option σ → ℂ => A z + 0) ((A.analyticAt 0).add analyticAt_const) (by simp) φ : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(f ∘ A)
    rw [germPull_coe _ _ _ φ f hfφ]
    simp only [add_zero]
  refine (MulEquiv.prime_iff (germAffineEquiv A (0 : Option σ → ℂ))).1 ?_
  rw [hT]
  have hirrA : Irreducible (mkGerm (f ∘ A) hfA) := by
    rw [← hT]; exact (MulEquiv.irreducible_iff (germAffineEquiv A (0 : Option σ → ℂ))).2 hφ

  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d (f ∘ A) hfA hAd
  have hE := isUnit_mkGerm e he he0
  have hF : mkGerm (f ∘ A) hfA = polyToGerm σ (weierstrassPoly c hc) * mkGerm e he := by
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGerm_weierstrassPoly, coe_mkGerm, coe_mkGerm, ← Germ.coe_mul]
    exact Germ.coe_eq.2 (by
      filter_upwards [hfe] with x hx
      rw [hx, Pi.mul_apply, mul_comm])
  have hassoc : Associated (polyToGerm σ (weierstrassPoly c hc)) (mkGerm (f ∘ A) hfA) :=
    ⟨hE.unit, by rw [hF, IsUnit.unit_spec]⟩
  have hirrW : Irreducible (polyToGerm σ (weierstrassPoly c hc)) := hassoc.irreducible_iff.2 hirrA
  refine hassoc.prime_iff.1 ?_

  have hprimeω : Prime (weierstrassPoly c hc) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.1 (weierstrassPoly_irreducible c hc hc0 hirrW)
  refine prime_map_of_prime (polyToGerm σ) hprimeω hirrW.ne_zero ?_
    (weierstrassPoly_dvd_of_polyToGerm_dvd c hc hc0)
  intro g
  obtain ⟨g₀, hg₀, hg₀g⟩ := g.2
  obtain ⟨q, a, hq, ha, hdiv⟩ := hD σ d (f ∘ A) g₀ hfA hg₀ hAd
  refine ⟨mkGerm (q * e) (hq.mul he), finPoly fun j => mkGerm (a j) (ha j), Subtype.ext ?_⟩
  rw [Subring.coe_add, Subring.coe_mul, polyToGerm_weierstrassPoly, polyToGerm_finPoly, coe_mkGerm, ← hg₀g,
    ← Germ.coe_mul, ← Germ.coe_add]
  exact Germ.coe_eq.2 (by
    filter_upwards [hdiv, hfe] with x hx hx'
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [hx, hx']
    ring)

theorem HolGermsUFD.proof (hP : WeierstrassPreparation.Statement) (hD : WeierstrassDivision.Statement) :
    HolGermsUFD.Statement := by
  have hG := GeneralLinearCoordinates.proof
  have hN := AnalyticGermsNoetherian.proof hD hG
  have hfin : ∀ n : ℕ, UniqueFactorizationMonoid (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := isField_holGerms_fin_zero.toField
      infer_instance
    | succ n ih =>
      exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv
        (0 : Fin (n + 1) → ℂ)).symm.toMulEquiv.uniqueFactorizationMonoid
        (uniqueFactorizationMonoid_holGerms_option hN hG hP hD (Fin n) ih)
  intro σ _ w
  exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
    w).symm.toMulEquiv.uniqueFactorizationMonoid (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace IntegralIndep

variable {n d : ℕ}

theorem chartDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartAbsDens J A f φ y = chartPosDens J A f φ y + chartPosDens J A (-f) φ y ∧
      chartDens J A f φ y = chartPosDens J A f φ y - chartPosDens J A (-f) φ y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartAbsDens chartDens chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem chartPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) : 0 ≤ chartPosDens J A f φ y := by
  unfold chartPosDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)]
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp

theorem measurable_chartPosDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (chartPosDens J A f φ) :=
  SheetSumMeasurable.measurable_sheetSum hA (fun a b => max (a * b) 0)
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf φ

theorem chartInt_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by
  have h0 := chartPosDens_nonneg J A hA f φ
  have h1 := chartPosDens_nonneg J A hA (-f) φ
  have m0 := measurable_chartPosDens hA hf φ
  have m1 := measurable_chartPosDens hA hf.neg φ
  have habs : chartAbsDens J A f φ = fun y => chartPosDens J A f φ y + chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).1
  have hlin : ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (chartAbsDens J A f φ) ↔
      ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (chartPosDens J A f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (chartPosDens J A (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : chartDens J A f φ = fun y => chartPosDens J A f φ y - chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).2
  rw [chartInt, hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

end IntegralIndep

theorem IntegralIndep.proof (h : PosPartIndep.Statement) : IntegralIndep.Statement := by
  intro n d J A A' f φ hP hd hA hA' hf hφ hi
  have e0 := h n d J A A' f φ hP hd hA hA' hf hφ
  have e1 := h n d J A A' (-f) φ hP hd hA hA' hf.neg hφ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨iA', cA'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf φ
  have hi' : Integrable (chartAbsDens J A' f φ) := iA'.2 (by rw [← e0, ← e1]; exact iA.1 hi)
  exact ⟨hi', by rw [cA hi, cA' hi', e0, e1]⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitAtBranches.proof (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by
  intro n d J W u q m γ ord π φ hJ hdim hu hW hq hφ hzW hcov hsl hdisj hord _
  obtain ⟨NA, hNA, hA⟩ := hDec n d J u q m γ ord hJ hdim hu hcov hdisj hord
  obtain ⟨NB, hNB, hB⟩ := hSl n d J W u q m γ ord hJ hdim hu hW hq hzW hcov hsl hdisj hord
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu hcov hdisj b 0 (Metric.mem_ball_self (γ b).radius_pos)
      (γ b).map_zero _ (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨NA ∩ NB ∩ ⋂ b, Metric.ball q (e b), inter_mem (inter_mem hNA hNB)
    (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)), fun f hf hfc hfN => ?_⟩
  have hcons : ∀ (g : (Fin n → ℂ) → ℝ) (b : Fin m), (fun k => vecCons g φ k ∘ (γ b).toFun) =
      vecCons (g ∘ (γ b).toFun) fun k => φ k ∘ (γ b).toFun := fun g b => by
    funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hsum : (fun ε => ∑ b, ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) =ᶠ[𝓝[>] 0]
      fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hA f _ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_left))
      (fun i => Fin.cases ⟨Set.univ, isOpen_univ, Set.subset_univ _, (contDiff_logReg u hε).contDiffOn⟩
        (fun j => hφ j) i)]
    exact Finset.sum_congr rfl fun b _ => by rw [hcons]; rfl
  refine Tendsto.congr' hsum ?_
  have hlim : ∀ b, Tendsto (fun ε => ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) (𝓝[>] 0) (𝓝 ((ord b : ℝ) * varInt W d f φ)) := by
    intro b
    have han : AnalyticOnNhd ℂ (γ b).toFun (Metric.ball 0 (γ b).radius) := fun w hw =>
      AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) _ (fun z => (γ b).toFun z i)
        Metric.isOpen_ball (differentiableOn_pi.1 (γ b).differentiableOn i) w hw
    have hγ : ContDiffOn ℝ ∞ (γ b).toFun (Metric.ball 0 (γ b).radius) :=
      (han.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    rw [hB b f φ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_right)) hφ]
    refine hLim d (ord b) (γ b).radius ((γ b).radius / 2) _ (f ∘ (γ b).toFun) _
      (half_lt_self (γ b).radius_pos) (hord b) (hf.comp_contDiffOn hγ) (fun τ hτ hne => hpe b τ hτ ?_)
      (fun k => ?_)
    · exact Set.mem_iInter.1 (Set.inter_subset_right (hfN (subset_tsupport f hne))) b
    · obtain ⟨U, hU, hsub, hφU⟩ := hφ k
      exact hφU.comp hγ fun τ hτ => hsub ((γ b).mapsTo hτ)
  have := tendsto_finsetSum Finset.univ fun b _ => hlim b
  convert this using 2
  push_cast
  rw [Finset.sum_mul]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitGoodPoints.proof (hBr : DivisorGeneralPointBranches.Statement)
    (hLim : LelongLimitAtBranches.Statement) (hOrd : LocalOrder.Statement) :
    LelongLimitGoodPoints.Statement := by
  classical
  intro n d J u φ hJ hdim hu hφ
  obtain ⟨I, hI, hIdim, hgood⟩ := hBr n d J u hJ hdim hu
  refine ⟨I, hI, hIdim, fun q hqJ hqu hqI => ?_⟩
  obtain ⟨W, hWm, hqW, hone, hWloc, m, γ, ord, π, hcov, hsl, hmeet, hvan, hbij⟩ :=
    hgood q hqJ hqu hqI
  obtain ⟨N, hN, hlim⟩ :=
    hLim n d J W u q m γ ord π φ hJ hdim hu hWm hqW hφ hWloc hcov hsl hmeet hvan hbij
  have hmult := hOrd n d J W u q m γ ord hJ hdim hu hWm hqW hcov hsl hmeet hvan
  have hclosed : ∀ W' : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet W') := fun W' => by
    have : zeroSet W' = ⋂ p ∈ W', {x : Fin n → ℂ | MvPolynomial.eval x p = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

  set O := ⋂ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hO : O ∈ 𝓝 q :=
    (Filter.biInter_mem
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).sdiff)).2 fun W' hW' =>
      (hclosed W').isOpen_compl.mem_nhds fun h => hW'.2 (hone W' hW'.1 h)
  refine ⟨N ∩ O, Filter.inter_mem hN hO, fun f hf hfc hfN => ?_⟩
  have hL : (∑ᶠ (W' : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W' : ℝ) * varInt W' d f φ) =
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    rw [finsum_eq_single _ W fun W' hne => ?_, finsum_eq_dif, dite_eq_left hWm]
    rw [finsum_eq_dif]
    split_ifs with hW'
    · rw [varInt_eq_zero_of_vanish W' f φ fun x hx => image_eq_zero_of_notMem_tsupport fun hxs =>
        Set.mem_iInter₂.1 (hfN hxs).2 W' ⟨hW', hne⟩ hx, mul_zero]
    · rfl
  rw [hL, hmult]
  exact hlim f hf hfc fun x hx => (hfN hx).1

end GroundTheory.Heights₂.Heights
end

