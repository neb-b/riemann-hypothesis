module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0003
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ExistsCut
section
noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

open NumberField MeasureTheory Filter GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem borelSp : BorelSpace (H E n 0) := ⟨rfl⟩

attribute [local instance] borelSp

private theorem exists_cut (A : ℝ) : ∃ χ : ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ ∀ s, |s| ≤ A → χ s = 1 := by
  obtain ⟨c, h1, -, h3, -⟩ := exists_continuous_one_zero_of_isCompact (isCompact_closedBall (0 : ℝ) A)
    (Metric.isOpen_ball (x := (0 : ℝ)) (ε := A + 1)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨fun s => (c s : ℂ), Complex.continuous_ofReal.comp c.continuous,
    h3.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, fun s hs => ?_⟩
  have : c s = 1 := h1 (by simpa [Real.norm_eq_abs] using hs)
  simp [this]

private def mulL (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) :
    Lp ℂ 2 D.ν →L[ℂ] Lp ℂ 2 D.ν :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL D.ν ∞ 2 2
    (memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x)) : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν).toLp

private theorem mulL_ae (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (v : Lp ℂ 2 D.ν) : (mulL D hw hC v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => w (ldet x) * (v : H E n 0 → ℂ) x := by
  have hm : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν :=
    memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x))
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) hm.toLp v, hm.coeFn_toLp] with x h1 h2
  refine Eq.trans h1 ?_
  simp only [ContinuousLinearMap.mul_apply']
  rw [h2]

private def mulV (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] :
    Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D where
  toFun f := WithLp.toLp 2 fun i => mulL D hw hC (f i)
  map_add' a b := PiLp.ext fun i => map_add (mulL D hw hC) (a i) (b i)
  map_smul' c a := PiLp.ext fun i => map_smul (mulL D hw hC) c (a i)

private theorem mulV_cont (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (ι : Type) [Fintype ι] : Continuous (mulV D hw hC ι) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (mulL D hw hC).continuous.comp (PiLp.continuous_apply 2 _ i))

private theorem mul_keep (D : Dom E n 0) (π : CuspSub E n) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] {f : Hs (ι := ι) D} (hf : f ∈ piSp D π ι) :
    mulV D hw hC ι f ∈ piSp D π ι := by
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (mulV D hw hC ι) := by
    refine Submodule.span_le.2 fun g hg => ?_
    choose ψ hψ u hu hu' hgu using hg
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span fun j => ?_)
    refine ⟨ψ j, hψ j, fun s => u j s * w s, (hu j).mul hw, (hu' j).mul_right, ?_⟩
    filter_upwards [mulL_ae D hw hC (g j), hgu j] with x h1 h2
    refine Eq.trans h1 ?_
    rw [h2]
    ring
  have hcl : IsClosed (((piSp D π ι).comap (mulV D hw hC ι)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage
      (mulV_cont D hw hC ι)
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

set_option synthInstance.maxHeartbeats 200000 in
private theorem cv_cont (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {u : ℝ → ℂ} (hu : Continuous u) {f : GA E n → ℂ} (hf : Continuous f) : Continuous (cvF μ φ u f) := by
  have hl : Continuous (ldet : H E n 0 → ℝ) := DiscreteGroups.T1.G.continuous_ldet
  haveI : SecondCountableTopology (H E n 0) := inferInstance
  haveI : FirstCountableTopology (H E n 0) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have h1 : Continuous fun x : H E n 0 => ∫ y in tsupport φ, φ y * u (ldet y) * f (x.1 * y.1) ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun (x y : H E n 0) => φ y * u (ldet y) * f (x.1 * y.1))
      (((hφ.1.comp continuous_snd).mul (hu.comp (hl.comp continuous_snd))).mul
        (hf.comp ((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd))))
      hφ.2.isCompact
  have h2 : cvF μ φ u f = fun g : GA E n => ∫ y in tsupport φ, φ y * u (ldet y) * f ((g, (1 : GA E 0)).1 * y.1) ∂μ := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [h2]
  exact h1.comp (continuous_id.prodMk continuous_const)

private theorem form_rat (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) (γ : ratH E n 0) (y : H E n 0) :
    ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
  obtain ⟨⟨a, b⟩, hγ⟩ := γ.2
  have e : (γ : H E n 0).1 = ratGL E n a := by rw [← hγ]; rfl
  rw [Prod.fst_mul, e]
  exact (π.cusp ψ hψ).1.left a y.1

private theorem cut_value (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) (R : ℝ) :
    ∃ v ∈ piSp D π Unit, ∀ᵐ x ∂D.ν, |ldet x| ≤ R → (v () : H E n 0 → ℂ) x = cvF D.μ φ u ψ.1 x.1 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, hl, -⟩ := hB E n hn
  set φ' : H E n 0 → ℂ := fun y => φ y * u (ldet y) with hφ'
  have ht : IsTestH φ' := ⟨hφ.1.mul (hu.comp hl), hφ.2.mul_right⟩
  obtain ⟨A, hA⟩ := (hφ.2.isCompact.image hl).isBounded.subset_closedBall (0 : ℝ)
  have hA' : ∀ y, φ y ≠ 0 → |ldet y| ≤ A := fun y hy => by
    have := hA (Set.mem_image_of_mem _ (subset_tsupport φ hy))
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨χ, hχ, hχs, hχ1⟩ := exists_cut (R + A)
  set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * χ (ldet x) with hf
  have hfL : MemLp f 2 D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ χ hχ hχs).1
  let g : Hs (ι := Unit) D := WithLp.toLp 2 fun _ => hfL.toLp f
  have hg : g ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, χ, hχ, hχs, hfL.coeFn_toLp⟩)
  obtain ⟨T, hT, -, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D Unit (fun _ _ => φ') (fun _ _ => ht)
  refine ⟨T g, DiscreteGroups.T1.G.piInv E n hn D π hθ Unit _ T (fun _ _ => ht) hT g hg, ?_⟩
  filter_upwards [hT g ()] with x hx hxR
  let X : E1.Ctx :=
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (E1.ratProper_holds E n).2.1
    haveI := (E1.ratProper_holds E 0).2.1
    { G := H E n 0
      ms := PositivityTheory.Rg.BcB.E.borelH E n 0
      bs := ⟨rfl⟩
      μ := D.μ
      haar := { toIsFiniteMeasureOnCompacts :=
                  @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
                toIsMulLeftInvariant := D.haar.1
                toIsOpenPosMeasure := D.haar.2.2.1 }
      Γ := ratH E n 0
      cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
      proper := by
        intro C hC
        have h1 := (E1.ratProper_holds E n).2.2 _ (hC.image continuous_fst)
        have h2 := (E1.ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
        refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
        rintro ⟨_, γ, rfl⟩ hγ
        exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
      F := D.F
      fd := D.fd }
  have hinv : ∀ (δ : ratH E n 0) (y : H E n 0), f ((δ : H E n 0) * y) = f y := fun δ y => by
    show ψ.1 ((δ : H E n 0) * y).1 * χ (ldet ((δ : H E n 0) * y)) = ψ.1 y.1 * χ (ldet y)
    rw [form_rat π hψ δ y, hmul, (hrat δ).1, zero_add]
  have e1 : ∫ y, kerH φ' x y * (g () : H E n 0 → ℂ) y ∂D.ν = ∫ y, kerH φ' x y * f y ∂D.ν :=
    integral_congr_ae (hfL.coeFn_toLp.mono fun y hy => by
      show kerH φ' x y * (hfL.toLp f : H E n 0 → ℂ) y = _
      rw [hy])
  have e2 : ∫ y, kerH φ' x y * f y ∂D.ν = ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ :=
    (DiscreteGroups.T1.G.unfold X PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable ht hinv hfL x).2
  have e3 : ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ = ∫ y, φ' y * f (x * y) ∂D.μ := by
    haveI : D.μ.IsMulLeftInvariant := D.haar.1
    have h := integral_mul_left_eq_self (μ := D.μ) (fun y => φ' y * f (x * y)) x⁻¹
    simpa only [mul_inv_cancel_left] using h
  have e4 : ∫ y, φ' y * f (x * y) ∂D.μ = cvF D.μ φ u ψ.1 x.1 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases h0 : φ y = 0
    · simp [hφ', h0]
    · have hy := hA' y h0
      have hc : χ (ldet (x * y)) = 1 := hχ1 _ (by
        rw [hmul]
        exact (abs_add_le _ _).trans (add_le_add hxR hy))
      simp only [hφ', hf, hc, mul_one, Prod.fst_mul]
  rw [hx]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact e1.trans (e2.trans (e3.trans e4))

private theorem cv_inS (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) :
    InS D π (cvF D.μ φ u ψ.1) := by
  intro w hw hws
  obtain ⟨R, hR⟩ := hws.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hws
  obtain ⟨v, hv, hva⟩ := cut_value hB hn D π hθ hψ hφ hu R
  refine ⟨mulV D hw hC Unit v, mul_keep D π hw hC Unit hv, ?_⟩
  filter_upwards [mulL_ae D hw hC (v ()), hva] with x h1 h2
  refine Eq.trans h1 ?_
  by_cases h0 : w (ldet x) = 0
  · simp [h0]
  · have hx := hR (subset_tsupport w h0)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    rw [h2 hx, mul_comm]

private theorem form_inS (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) : InS D π ψ.1 := by
  intro w hw hws
  have hL := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1
  exact ⟨WithLp.toLp 2 fun _ => hL.toLp _,
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, w, hw, hws, hL.coeFn_toLp⟩),
    hL.coeFn_toLp⟩

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.cvIn_pf :
    Basic → AeEq → CvIn := by
  intro hB _ E _ _ _ n hn D π hθ ψ hψ
  have hc := DiscreteGroups.T1.G.continuous_of_mem π hψ
  have hμ : MeasureTheory.IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨⟨hc, (π.cusp ψ hψ).1.left, hθ.1 ψ hψ, fun w hw hws =>
    (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1⟩, fun φ u hφ hu => ?_⟩
  have hin := cv_inS hB hn D π hθ hψ hφ hu
  refine ⟨⟨cv_cont D.μ hφ hu hc, fun γ g => ?_, fun t g => ?_, fun w hw hws => ?_⟩, hin, form_inS hn D π hθ hψ⟩
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.CuspRep.ratGL E n γ) g y.1, (π.cusp ψ hψ).1.left]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.UnitaryBC.splitCentre E n t) g y.1, hθ.1 ψ hψ]
  · obtain ⟨v, -, hv⟩ := hin w hw hws
    exact (MeasureTheory.Lp.memLp (v ())).ae_eq hv
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsType
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

private lemma exists_projL {F : Type} [AddCommGroup F] [Module ℂ F] (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a) (hpos : ∀ a, a ≠ 0 → 0 < (B a a).re)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S] :
    ∃ P : F →ₗ[ℂ] F, (∀ x, P x ∈ S) ∧ ∀ x, ∀ a ∈ S, B a (x - P x) = 0 := by
  let core : InnerProductSpace.Core ℂ F :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => hsym b a
      re_inner_nonneg := fun a => by
        by_cases h : a = 0
        · simp [h]
        · exact (hpos a h).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a h => by
        by_contra h0
        have h1 := hpos a h0
        have h2 : B a a = 0 := h
        simp [h2] at h1 }
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩
  have h0 := S.starProjection_inner_eq_zero x a ha
  have h1 : B (x - S.starProjection x) a = 0 := h0
  have h2 := hsym (x - S.starProjection x) a
  rw [h1, map_zero] at h2
  exact h2.symm

private lemma orbit_stable {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) (g : Γ) :
    ∀ a ∈ Submodule.span ℂ (Set.range fun k => R k x),
      R g a ∈ Submodule.span ℂ (Set.range fun k => R k x) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨k, rfl⟩ := h
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma self_mem_orbit {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) : x ∈ Submodule.span ℂ (Set.range fun k => R k x) :=
  Submodule.subset_span ⟨1, by simp⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absType_pf :
    AbsType := by
  intro Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt
  have hRR : ∀ k a, R k (R k⁻¹ a) = a := fun k a => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b := fun k a b => by
    have h := hinv k (R k⁻¹ a) b
    rwa [hRR] at h
  let T : Submodule ℂ F :=
    { carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W}
      add_mem' := fun {a b} ha hb l => by
        have h := W.add_mem (ha l) (hb l)
        convert h using 1
        ext k; simp
      zero_mem' := fun l => by
        have h := W.zero_mem
        convert h using 1
        ext k; simp
      smul_mem' := fun c x hx l => by
        have h := W.smul_mem c (hx l)
        convert h using 1
        ext k; simp }
  have hTR : ∀ g, ∀ x ∈ T, R g x ∈ T := fun g x hx l => by
    have h := hW _ (hx l) g
    convert h using 1
    ext k; simp [map_mul, Module.End.mul_apply]
  haveI : FiniteDimensional ℂ Y := hY
  haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) :=
    Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2
  obtain ⟨P, hPm, hPo⟩ := exists_projL B hsym hpos (V ⊓ T)
  refine ⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩
  have hz1T : z - P z ∈ T := T.sub_mem hzt (hPm z).2
  have hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hTR k _ hz1T
  have hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨k, rfl⟩ := h
      show B a (R k (z - P z)) = 0
      rw [hadj]
      exact hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩
    | zero => simp
    | add a' b _ _ ha' hb => rw [map_add (f := _), ha', hb, add_zero]
    | smul c a' _ ha' => rw [map_smul, ha', smul_zero]
  intro v hv
  haveI := hVf v hv
  obtain ⟨Q, hQm, hQo⟩ := exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))
  have hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hV k v hv
  have hzero : ∀ d, B d d = 0 → d = 0 := fun d h => by
    by_contra h0
    have h1 := hpos d h0
    simp [h] at h1
  have hQR : ∀ g x, Q (R g x) = R g (Q x) := fun g x => by
    have hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v) :=
      Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))
    have h1 := hQo (R g x) _ hd
    have h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0 := by
      rw [← map_sub, hadj]
      exact hQo x _ (orbit_stable R v g⁻¹ _ hd)
    have h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0 := by
      have h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) =
          B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) -
            B (Q (R g x) - R g (Q x)) (R g x - Q (R g x)) := by
        rw [← map_sub]
        congr 1
        abel
      rw [h4, h1, h2, sub_zero]
    exact sub_eq_zero.1 (hzero _ h3)
  have hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T := fun w hw l => by
    have h := hZT hw (l ∘ₗ Q)
    convert h using 1
    ext k; simp [hQR]
  have hQ0 : Q (z - P z) = 0 := by
    have hw := self_mem_orbit R (z - P z)
    have h1 := hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw
    have h2 := hQo (z - P z) _ (hQm (z - P z))
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact hzero _ h2
  have h := hQo (z - P z) v (self_mem_orbit R v)
  rwa [hQ0, sub_zero] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PCvType
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private lemma shiftInt (D : Dom E n 0) (a : H E n 0) (F : H E n 0 → ℂ) :
    ∫ y, F (a * y) ∂D.μ = ∫ y, F y ∂D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.1
  exact integral_mul_left_eq_self F a

private lemma ldet_shift (a : GA E n) (h : logAbs a.val.det = 0) (y : H E n 0) :
    ldet (((a, 1) : H E n 0) * y) = ldet y := by
  simp only [ldet, Prod.fst_mul, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h, zero_add]

private lemma cv_shift (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (h : logAbs a.val.det = 0) :
    cvF D.μ φ u f (g * a) = ∫ y, φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ := by
  rw [← shiftInt D ((a, 1) : H E n 0) (fun y => φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1))]
  unfold cvF
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((a⁻¹, 1) : H E n 0) * (((a, 1) : H E n 0) * y) = y := by
    rw [← mul_assoc]; simp
  simp only [e, ldet_shift a h, Prod.fst_mul, mul_assoc]

private lemma term_integrable (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (hφ : IsTestH φ) (hu : Continuous u) (hf : Continuous f) :
    Integrable (fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1)) D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ :=
    ⟨fun _ h => h.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x _⟩
  have c1 : Continuous fun y : H E n 0 => φ ((a, 1) * y) := hφ.1.comp (continuous_const.mul continuous_id)
  have s1 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) :=
    hφ.2.comp_homeomorph (Homeomorph.mulLeft ((a, 1) : H E n 0))
  have s3 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (s1.mul_right (f' := fun y : H E n 0 => u (ldet y))).mul_right (f' := fun y : H E n 0 => f (g * y.1))
  have c3 : Continuous fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (c1.mul (hu.comp DiscreteGroups.T1.G.continuous_ldet)).mul (hf.comp (continuous_const.mul continuous_fst))
  exact c3.integrable_of_hasCompactSupport s3

theorem cvType_pf : DetZero → EvalBasis → CvType := by
  intro hdz hev E _ _ _ n D K W φ u f hK hW hφ hL hu hf
  refine ⟨fun k hk g => ?_, fun g => ?_⟩
  · rw [cv_shift D φ u f g _ ((hdz E n).2 K hK k hk)]
    unfold cvF
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := hL.1 k⁻¹ (K.inv_mem hk) y
    simp only [map_inv] at this
    simp only [this]
  · obtain ⟨d, x, w, hw, hs⟩ := hev (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x)
      (fun v hv => funext hv) W hW
    set c : Fin d → ℂ := fun b =>
      ∫ y, φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ with hc
    have key : (fun k : Kinf E n => cvF D.μ φ u f (g * kI E n k)) = ∑ b, c b • w b := by
      funext k
      rw [cv_shift D φ u f g _ ((hdz E n).1 k)]
      have e : ∀ y : H E n 0, φ (((kI E n k)⁻¹, 1) * y) * u (ldet y) * f (g * y.1) =
          ∑ b, w b k * (φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1)) := by
        intro y
        have := congrFun (hs _ (hL.2 y)) k
        simp only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      simp only [e]
      rw [integral_finsetSum _ fun b _ => (term_integrable D φ u f g _ hφ hu hf).const_mul _]
      simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [key]
    exact Submodule.sum_mem _ fun b _ => W.smul_mem _ (hw b)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiFinOf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty
end

