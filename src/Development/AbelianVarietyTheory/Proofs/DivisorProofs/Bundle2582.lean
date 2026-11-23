module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.FSMass

theorem chern_mass_hermitian_O_one_projective : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  intro N
  have hproj : IsProjOver (PSpace.str ℂ N) := ProjSpace.isProjOver_str ℂ N
  haveI : IsIntegral (PSpace ℂ N) := ProjSpace.isIntegral_of_isDomain ℂ N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).IsCInf := (ProjSpace.hermitianTwistingSheaf ℂ N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf ℂ N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := _root_.GlobalTheory.StdProjChart.exists_stdChart N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace ℂ N) ∈ ProjSpace.chart ℂ N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace ℂ N)).mem_open_set_iff (ProjSpace.chart ℂ N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := _root_.GlobalTheory.ChernNullField.chernPart_compl_null ℂ (PSpace ℂ N) (PSpace.str ℂ N) (RingHom.id ℂ) N hproj _ hgen _
    ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)) 1
  rw [← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (_root_.GlobalTheory.lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, _root_.GlobalTheory.FSDet.det_fubiniStudy_hess N v]
  simp
end GlobalTheory.FSMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology MeasureTheory
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ChernFrame

theorem chernAt_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {H K : V n → Matrix r r ℂ} {v : V n}
    (h : H =ᶠ[𝓝 v] K) (j : ℕ) : chernAt H v j = chernAt K v j := by
  unfold chernAt chernPoly curvPoly
  simp only [curv_congr h]

theorem delAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem dbarAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.dbar_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem chern_frame_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  intro M _ n A ι _ _ κ U hUo hUc g hg G hGs hGp hGt j
  have hop : ∀ i a, IsOpen ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a =>
    (A.e i).isOpen_inter_preimage_symm (hUo a)
  have hsm : ∀ i a p q, ContDiffOn ℝ ∞ (fun v => G a ((A.e i).symm v) p q)
      ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a p q => hGs a p q i
  have hun : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a, IsUnit (G a ((A.e i).symm v)).det :=
    fun i a v hv => (isUnit_iff_isUnit_det _).1 (hGp a _ hv.2).isUnit
  have hpt : ∀ (x : A.Pt) a, x.pt ∈ U a → x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' U a :=
    fun x a ha => ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact ha⟩
  have hfr : ∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x := by
    intro a b x ha hb
    have hN : IsOpen ((A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b)) :=
      (A.e x.1.1).isOpen_inter_preimage_symm ((hUo a).inter (hUo b))
    have hsym : (A.e x.1.1).symm x.crd = x.pt := x.ch.left_inv x.2
    have hx : x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b) :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [hsym]; exact ⟨ha, hb⟩⟩
    have hK : MContDiffAt 2 (fun v => G a ((A.e x.1.1).symm v)) x.crd := fun p q =>
      ((hsm x.1.1 a p q).contDiffAt ((hop x.1.1 a).mem_nhds (hpt x a ha))).of_le (by norm_cast)
    have hKu : IsUnit (G a ((A.e x.1.1).symm x.crd)).det := hun x.1.1 a _ (hpt x a ha)
    have hA : ∀ p q, AnalyticAt ℂ (fun w => g a b ((A.e x.1.1).symm w) p q) x.crd := fun p q =>
      GlobalTheory.SCV.analyticAt_of_differentiableOn (hg a b p q x.1.1) (hN.mem_nhds hx)
    have hAu : IsUnit (g a b ((A.e x.1.1).symm x.crd)).det := by
      rw [hsym]
      have h2 := (isUnit_iff_isUnit_det _).1 (hGp b _ hb).isUnit
      rw [hGt a b x.pt ⟨ha, hb⟩, chg, det_mul, det_mul] at h2
      simpa using isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2)
    have hev : (fun v => G b ((A.e x.1.1).symm v)) =ᶠ[𝓝 x.crd]
        fun v => chg (g a b ((A.e x.1.1).symm v)) (G a ((A.e x.1.1).symm v)) :=
      Filter.eventually_of_mem (hN.mem_nhds hx) fun v hv => hGt a b _ hv.2
    exact (_root_.GlobalTheory.CxForm.chernAt_changeFrame _ _ _ _ hK hKu hA hAu hev j).symm
  refine ⟨hfr, fun P hP => ?_⟩
  have hloc : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a,
      A.loc P i v = (chernAt (fun w => G a ((A.e i).symm w)) v j : Alt n) := by
    intro i a v hv
    rw [HolAtlas.loc, dite_eq_left hv.1, hP a ⟨(i, (A.e i).symm v), (A.e i).map_target hv.1⟩ hv.2]
    show ((chernAt (fun w => G a ((A.e i).symm w)) ((A.e i) ((A.e i).symm v)) j : Ev n) : Alt n) = _
    rw [(A.e i).right_inv hv.1]
  have hgerm : ∀ i a v, v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a →
      A.loc P i =ᶠ[𝓝 v] fun w => (chernAt (fun w' => G a ((A.e i).symm w')) w j : Alt n) :=
    fun i a v hv => Filter.eventually_of_mem ((hop i a).mem_nhds hv) (hloc i a)
  refine ⟨⟨fun i S => ?_, fun x x' hxx => ?_⟩, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
    obtain ⟨a, ha⟩ := hUc ((A.e i).symm v)
    refine ⟨_, hop i a, ⟨hv, ha⟩, ?_⟩
    refine ((_root_.GlobalTheory.ChernSmooth.contDiffOn_chernAt _ _ (hop i a) (hsm i a) (hun i a) j S).mono inter_subset_right).congr fun w hw => ?_
    rw [hloc i a w hw.2]
  · obtain ⟨a, ha⟩ := hUc x.pt
    have ha' : x'.pt ∈ U a := hxx ▸ ha
    rw [hP a x ha, hP a x' ha']
    have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hxW : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; show x.pt ∈ _; rw [hxx]; exact x'.2⟩
    have hφ : AnalyticAt ℂ (x'.ch ∘ x.ch.symm) x.crd := GlobalTheory.SCV.analyticAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hW.mem_nhds hxW)
    have hφv : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      simp only [Function.comp_apply]; rw [x.ch.left_inv x.2]; show x'.ch x.pt = x'.ch x'.pt; rw [hxx]
    have hH2 : MContDiffAt 2 (fun v => G a (x'.ch.symm v)) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hφv]
      exact fun p q => ((hsm x'.1.1 a p q).contDiffAt ((hop x'.1.1 a).mem_nhds (hpt x' a ha'))).of_le
        (by norm_cast)
    have hHu : IsUnit (G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
      rw [hφv]; exact hun x'.1.1 a _ (hpt x' a ha')
    have key := _root_.GlobalTheory.CxForm.chernAt_comp (fun v => G a (x'.ch.symm v)) (x'.ch ∘ x.ch.symm) x.crd hφ hH2 hHu j
    rw [hφv] at key
    have hge : (fun v => G a (x.ch.symm v)) =ᶠ[𝓝 x.crd] fun w => G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) w)) :=
      Filter.eventually_of_mem (hW.mem_nhds hxW) fun w hw => by
        simp only [Function.comp_apply]; rw [x'.ch.left_inv hw.2]
    show ((chernAt (fun v => G a (x.ch.symm v)) x.crd j : Ev n) : Alt n) = _
    rw [chernAt_congr hge j, key]
    rfl
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show delAt (A.loc P x.1.1) x.crd = 0
    rw [delAt_congr (hgerm _ a _ (hpt x a ha))]
    exact _root_.GlobalTheory.CxForm.ChernDel.delAt_chernAt _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show dbarAt (A.loc P x.1.1) x.crd = 0
    rw [dbarAt_congr (hgerm _ a _ (hpt x a ha))]
    exact _root_.GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)

end GlobalTheory.ChernFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory

theorem chernInt_pull_fubiniStudy_eq_zero_of_not_dominant : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  intro Y π hπ ⟨x, hx⟩
  have := ProjSpace.isIntegral_of_isDomain ℂ Y.dim
  obtain ⟨-, -, -, A', hA'⟩ := _root_.GlobalTheory.cxPts_var_compact_manifold Y
  have hA : IsAlgAtlas (ProjAn.finAtlas ℂ (RingHom.id ℂ) Y.dim) := AnRead.isAlgAtlas_finAtlas _
  have hne : π (genericPoint Y.X) ≠ genericPoint (PSpace ℂ Y.dim) := fun h =>
    hx (h ▸ genericPoint_specializes x)
  have hc := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)
  have hs := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).isSmooth hA.anRead
  rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y _ _ (hc.pull π hπ)).2 A' hA',
    SameForm.mInt_eq (fun _ => hs.sameForm_pull hA hA' π hπ)]
  exact rankDrop _ A' _ (hA.holoMap hA' (f := π) fun _ => rfl)
    (_root_.GlobalTheory.finrank_range_fderiv_lt_of_not_dominant ℂ _ _ _ _ _ _ _ A' hA hA' π hπ hne) _ (fun _ => hs.isPotential hA) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.ChernMassPull

theorem mass : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  intro k _ X Y _ _ p q σ D hX hY hsm π hπ hη hδ B φ hφ ε
  obtain ⟨U, hUη, hcard, hchart, hlift⟩ := _root_.GlobalTheory.CoverDegField.exists_open_covering_charts k X Y p q σ D hX hY hsm π hπ hη hδ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have h0Y := _root_.GlobalTheory.ChernNullField.chernPart_compl_null k Y q σ D hY (π ⁻¹ᵁ U) (by simp [hη, hUη]) _ (φ.pull π hπ) ε
  have h0X := _root_.GlobalTheory.ChernNullField.chernPart_compl_null k X p σ D hX U hUη B φ ε
  have h3 := _root_.GlobalTheory.CoverChernField.chernPart_preimage_of_cover k X Y p q σ D hX hY π hπ B φ hφ ε (ptsIn p σ U) (isOpen_ptsIn U) _
    hcard hchart hlift
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.ChernMassPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.FrameInv

section Algebra

variable {r R : Type} [Fintype r] [DecidableEq r] [CommRing R] {P Q : Matrix r r R}

theorem conj_pow (h : Q * P = 1) (A : Matrix r r R) (k : ℕ) : (P * A * Q) ^ k = P * A ^ k * Q := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h, one_mul]

theorem trace_conj' (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, h, one_mul]

theorem charpolyRev_conj (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).charpolyRev = A.charpolyRev := by
  have h' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 - (Polynomial.X : Polynomial R) • (P * A * Q).map Polynomial.C : Matrix r r (Polynomial R)) =
      P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • A.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 h', Matrix.mul_smul,
      Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    mul_eq_one_comm.1 h', Matrix.det_one, one_mul]

theorem conj_mul_three (h : Q * P = 1) (A B C : Matrix r r R) :
    (P * A * Q) * (P * B * Q) * (P * C * Q) = P * (A * B * C) * Q := by
  simp only [mul_assoc]
  rw [← mul_assoc Q P, h, one_mul, ← mul_assoc Q P, h, one_mul]

end Algebra

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem curvPoly_eq_sum (G : V n → Matrix r r ℂ) (v : V n) : curvPoly G v =
    ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext1 i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem curvPoly_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) : curvPoly G₂ v = P.map C * curvPoly G v * Q.map C := by
  simp only [curvPoly_eq_sum, h, Matrix.map_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem curvEv_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) :
    curvEv G₂ v = P.map (algebraMap ℂ (Ev n)) * curvEv G v * Q.map (algebraMap ℂ (Ev n)) := by
  have e (M : Matrix r r ℂ) : (M.map C).map (aeval (R := ℂ) (sym (n := n))) = M.map (algebraMap ℂ (Ev n)) := by
    ext1 i j
    simp only [Matrix.map_apply, aeval_C]
  rw [curvEv, curvPoly_conj h, Matrix.map_mul, Matrix.map_mul, e, e, curvEv]

theorem pow_chern_trans_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  intro n r _ _ G G' G₂ G₂' T K K' v hG uG hG' uG' hT uT hK uK hK' uK' h k
  obtain ⟨c₁, f₁⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G G₂ T K v hG uG hT uT hK uK (h.mono fun _ hx => hx.1)
  obtain ⟨c₂, f₂⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G' G₂' T K' v hG' uG' hT uT hK' uK' (h.mono fun _ hx => hx.2)
  have u : (T v)ᵀ * (T v)ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have uE : (T v)ᵀ.map (algebraMap ℂ (Ev n)) * (T v)ᵀ⁻¹.map (algebraMap ℂ (Ev n)) = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  have uC : (T v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * (T v)ᵀ⁻¹.map C = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [powAt, curvEv_conj f₁, conj_pow uE, trace_conj' uE, powAt]
  · rw [chernAt, chernPoly, curvPoly_conj f₁, ← neg_mul, ← mul_neg, charpolyRev_conj uC, chernAt, chernPoly]
  · have c (ξ : V n) : conn G₂ v ξ - conn G₂' v ξ = (T v)ᵀ⁻¹ * (conn G v ξ - conn G' v ξ) * (T v)ᵀ := by
      rw [c₁, c₂, ← mul_sub, add_sub_add_right_eq_sub, ← sub_mul, mul_assoc]
    unfold transAt
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [c, curvEv_conj f₁, curvEv_conj f₂, conj_pow uE, conj_pow uE, Matrix.map_mul, Matrix.map_mul,
      conj_mul_three uE, trace_conj' uE]

end GlobalTheory.ChernCalc.FrameInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  first | exact @GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | exact GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | (intros; apply GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeightStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) ≤ G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | exact GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | (intros; apply GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | exact GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | (intros; apply GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneFamilyTermEqPsiThetaValueCharacterStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ₀ : FractionRing V, ∀ (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b), w.IsGen → ∀ (mu : D.X) (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z (coef s g' w mu) * (rigV D (TF (R := V) (FractionRing V)).hom z J).val * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi 0) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z κ₀ * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val := by
  first | exact @GlobalTheory.Poinc.IntTerm.coef_eq_theta_value | exact GlobalTheory.Poinc.IntTerm.coef_eq_theta_value | (intros; apply GlobalTheory.Poinc.IntTerm.coef_eq_theta_value <;> assumption)
end

