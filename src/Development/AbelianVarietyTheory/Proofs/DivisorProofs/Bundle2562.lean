module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorOverOpen

theorem isNormalScheme_opens {S : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (V : S.Opens) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme := fun x => by
  obtain ⟨h₁, h₂⟩ := h x.1
  have e := (V.stalkIso x).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem isNoetherian_opens {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (V : S.Opens) :
    AlgebraicGeometry.IsNoetherian V.toScheme := by
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.1 (TopologicalSpace.NoetherianSpace.isCompact (V : Set S))
  exact {}

theorem exists_isGrpPullback_cancel {S S' S'' : Scheme.{0}} {H : Over S} {G : Over S'} {A' : Over S''}
    [GrpObj H] [GrpObj G] [GrpObj A'] {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ H.left} {ψ : G.left ⟶ H.left}
    (hφ : IsGrpPullback A' H (g ≫ f) φ) (hψ : IsGrpPullback G H f ψ) :
    ∃ φ' : A'.left ⟶ G.left, IsGrpPullback A' G g φ' := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso hφ ((isGrpPullback_pullback G g).comp hψ)
  exact ⟨_, ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G g)).congr (Category.id_comp _) rfl⟩

end GlobalTheory.FactorOverOpen


open GlobalTheory.FactorOverOpen in
theorem GlobalTheory.FactorOverOpen.factor_over_open : ∀ {S X : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (hX : IsSeparated (toZ X)) (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (H : Over S) [GrpObj H] (hH : IsSemiAbelian H) (U₀ U : S.Opens) (hU₀ : (U₀ : Set S).Nonempty) (hU : (U : Set S).Nonempty) (u' : U₀.toScheme ⟶ X) (c : U.toScheme ⟶ X) (A₀ : Over U₀.toScheme) [GrpObj A₀] (e₀ : A₀.left ⟶ H.left) (e₁ : A₀.left ⟶ A.left) (h₀ : IsGrpPullback A₀ H U₀.ι e₀) (h₁ : IsGrpPullback A₀ A u' e₁) (K : Type) [Field K] (pt : Sp K ⟶ S) (hpt : Set.range pt = {genericPoint S}) (hgen : ∀ (x : Sp K ⟶ U.toScheme) (y : Sp K ⟶ U₀.toScheme), x ≫ U.ι = pt → y ≫ U₀.ι = pt → x ≫ c = y ≫ u'), ∃ e : pullback A.hom c ⟶ H.left, IsGrpPullback ((Over.pullback c).obj A) H U.ι e := by
  intro S X _ _ hS hX A _ hA H _ hH U₀ U hU₀ hU u' c A₀ _ e₀ e₁ h₀ h₁ K _ pt hpt hgen

  let V : S.Opens := U ⊓ U₀
  have hη : ∀ W : S.Opens, (W : Set S).Nonempty → genericPoint S ∈ W := fun W hW =>
    ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 (by simpa using hW)
  have hηV : genericPoint S ∈ V := ⟨hη U hU, hη U₀ hU₀⟩
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty U := ⟨⟨_, hη U hU⟩⟩
  let jU : V.toScheme ⟶ U.toScheme := S.homOfLE inf_le_left
  let j₀ : V.toScheme ⟶ U₀.toScheme := S.homOfLE inf_le_right
  have hjU : jU ≫ U.ι = V.ι := S.homOfLE_ι _
  have hj₀ : j₀ ≫ U₀.ι = V.ι := S.homOfLE_ι _

  have hrange : Set.range pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hpt]
    simpa using hηV
  let z : Sp K ⟶ V.toScheme := IsOpenImmersion.lift V.ι pt hrange
  have hz : z ≫ V.ι = pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant z := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq,
      V.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, ← Set.range_comp]
    have : (⇑V.ι ∘ ⇑z) = ⇑pt := by rw [← hz]; rfl
    rw [this, hpt, (genericPoint_spec S).def]
    rfl
  have ha : jU ≫ c = j₀ ≫ u' := by
    refine ext_of_isDominant_of_isSeparated (ReciprocityTheory.ChartRestriction.G.Semi.toZ X)
      (specULiftZIsTerminal.hom_ext _ _) z ?_
    have := hgen (z ≫ jU) (z ≫ j₀) (by rw [Category.assoc, hjU, hz]) (by rw [Category.assoc, hj₀, hz])
    simpa only [Category.assoc] using this

  let G := (Over.pullback U.ι).obj H
  let G' := (Over.pullback c).obj A
  have pH : IsGrpPullback ((Over.pullback j₀).obj A₀) H (jU ≫ U.ι) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₀).congr (hj₀.trans hjU.symm) rfl
  have pA : IsGrpPullback ((Over.pullback j₀).obj A₀) A (jU ≫ c) _ :=
    ((isGrpPullback_pullback A₀ j₀).comp h₁).congr ha.symm rfl
  obtain ⟨φ, hφ⟩ := exists_isGrpPullback_cancel pH (isGrpPullback_pullback H U.ι)
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_cancel pA (isGrpPullback_pullback A c)

  haveI := isNoetherian_opens U
  haveI : IsDominant jU := ⟨jU.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG : IsSemiAbelian G := IsSemiAbelian.pullback U.ι H hH
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback c A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (isNormalScheme_opens hS U) hG' hG hψ hφ
  exact ⟨_, ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback H U.ι)).congr (Category.id_comp _) rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.RegLog

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_comp {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) {G : ℝ → ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G T) (hf : ∀ z, f z ∈ T) :
    CInfAt (fun z => G (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have e : f y = F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds
  refine ⟨W, ι, inferInstance, g, G ∘ F, O ∩ F ⁻¹' T, h₁, h₄.continuousOn.isOpen_inter_preimage h₂ hT,
    ⟨h₃, show F _ ∈ T from e ▸ hf y⟩, hG.comp (h₄.mono inter_subset_left) fun v hv => hv.2, ?_⟩
  filter_upwards [h₅] with z hz
  simp only [Function.comp_apply, hz]

theorem cInfAt_normSq_ev {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    CInfAt (fun z => ‖ev p σ W g z‖ ^ 2) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => ‖v ()‖ ^ 2, univ, hy, isOpen_univ, trivial,
    ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffOn, EventuallyEq.rfl⟩

theorem cInfAt_nsq {B : LB X} (φ : Weight p σ B) (hφ : φ.IsCInf) (s : B.Sec) (y : CxPts p σ) :
    CInfAt (φ.nsq (secVal p σ s)) y := by
  have hi := mem_pick φ.isLB y
  have h := (cInfAt_normSq_ev (s.f (pick φ.isLB y)) hi).comp₂ (hφ _ y hi)
    (G := fun x => x.1 * Real.exp (-x.2)) (contDiff_fst.mul (Real.contDiff_exp.comp contDiff_snd.neg))
  refine h.congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi] with z hz
  exact φ.nsq_eq (secVal_mem s) hz

end GlobalTheory.Mix.RegLog


open GlobalTheory.Mix.RegLog in
theorem GlobalTheory.Mix.semiPosReg_addFn_log_nsq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  intro k _ X p σ D N hN t δ hδ
  have hC : ∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y := fun y =>
    cInfAt_comp ((cInfAt_nsq N.φ N.cInf t y).add (cInfAt_const δ y)) isOpen_compl_singleton
      Real.contDiffOn_log fun z => (add_pos_of_nonneg_of_pos (N.φ.nsq_nonneg _ z) hδ).ne'
  refine ⟨hC, ?_⟩
  intro i c y hy ξ
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (N.B.U i))
  have hm := mem_over c.e hy.1 hy.2
  have hf : ContDiffAt ℂ 2 (ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) (c.e y) :=
    ReciprocityTheory.L2DbarEstimates.Y.contDiffAt_two_of_holo ho (c.holo _ (t.f i)) hm
  have hψ : ContDiffAt ℝ 2 (fun v => N.φ.φ i (c.e.symm v)) (c.e y) := N.cInf.contDiffAt c hy.1 hy.2
  have hψ' : ContDiffAt ℝ 2 (fun v => 1 * N.φ.φ i (c.e.symm v) + Real.log δ) (c.e y) :=
    (contDiffAt_const.mul hψ).add contDiffAt_const
  let w : Fin 2 → ReciprocityTheory.L2DbarEstimates.V D → ℝ := ![fun v => Complex.normSq ((ev p σ (N.B.U i) (t.f i) ∘ c.e.symm) v),
    fun v => Real.exp (1 * N.φ.φ i (c.e.symm v) + Real.log δ)]
  have hu : ∀ j, ContDiffAt ℝ 2 (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp hf
    · exact Real.contDiff_exp.contDiffAt.comp _ hψ'
  have hl : ∀ j, ReciprocityTheory.L2DbarEstimates.LogPshAt D (w j) (c.e y) := by
    intro j; fin_cases j
    · exact ReciprocityTheory.L2DbarEstimates.logPshAt_normSq hf
    · refine ReciprocityTheory.L2DbarEstimates.logPshAt_exp hψ' fun ζ => ?_
      rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hψ 1 (Real.log δ) ζ, Complex.ofReal_one, one_mul]
      exact hN i c y hy ζ
  have hpos : 0 < ∑ j, w j (c.e y) := by
    simp only [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Real.exp_pos _)
  have key := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg hu hl hpos ξ
  have e : (fun v => (((N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).φ i (c.e.symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (c.e y)] fun v => ((Real.log (∑ j, w j v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hz : c.e.symm v ∈ ptsIn p σ (N.B.U i) := hv.2
    congr 1
    simp only [Weight.addFn, N.φ.nsq_eq (secVal_mem t) hz, Fin.sum_univ_two, w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply, secVal_apply]
    set a := N.φ.φ i (c.e.symm v)
    set b := ev p σ (N.B.U i) (t.f i) (c.e.symm v)
    have h1 : ‖b‖ ^ 2 * Real.exp (-a) + δ = Real.exp (-a) * (Complex.normSq b + Real.exp (1 * a + Real.log δ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.exp_add, Real.exp_log hδ, one_mul, Real.exp_neg]
      field_simp
    rw [h1, Real.log_mul (Real.exp_pos _).ne' (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Real.exp_pos _)).ne', Real.log_exp]
    ring
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Weight

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPosReg_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (D D' : ℕ), SmoothOfRelativeDimension D p → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → φ.SemiPosReg D → (φ.pull π hπ).SemiPosReg D' := by
  intro k _ X Y p q σ π hπ D D' hs B φ hC hSP
  haveI := hs
  intro i c y hy ξ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := p) (σ := σ) (D := D) (m y)
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpByPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullAlong

theorem sharpBy_pull {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (t : T' ⟶ T) (v : T' ⟶ F.X) (hv : t ≫ u = v)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) (φA : P'.A.left ⟶ P.A.left)
    (hS : SharpBy F W P u c pr) (hA : IsGrpPullback P'.A P.A t φA) (hL : LBIso P'.L (P.L.pull φA)) :
    ∃ (c' : SiegPre g n ζ (v ≫ F.s)) (pr' : Fin 8 → (P'.A ⟶ c'.A)) (χ : c'.A.left ⟶ c.A.left),
      SharpBy F W P' v c' pr' ∧ IsGrpPullback c'.A c.A t χ ∧ ∀ a, (pr' a).left ≫ χ = φA ≫ (pr a).left := by
  subst hv
  obtain ⟨hpb, hmon, huniv, hLc⟩ := hS
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) T T' (u ≫ F.s)
    ((t ≫ u) ≫ F.s) t rfl (by rw [hid, Category.comp_id, Category.assoc])).1 c
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpb hc'
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := _root_.GlobalTheory.GrpPullPow.pr_pull pr hA hχ hmon huniv
  exact ⟨c', pr', χ, ⟨hcomp, hmon', huniv', GlobalTheory.T.lineBundleIso_eighthPower_groupPullback c.P c'.P P.L P'.L pr pr' W c.isLB c'.isLB P.isLB P'.isLB hsq hP hpr' hL hLc⟩,
    hχ, hpr'⟩

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ FinalForm.u₀ ≫ u) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ S ρ u c pr hS M U₀ EE FinalForm R _ _ _ _ G' _ _ _ D' A' U' ξ gm hgm hLB ξ₀ hξ₀
  obtain ⟨ψ, hψφ, hψs, hψpb⟩ := _root_.GlobalTheory.GenPb.genfib_grpPullback FinalForm U' ξ gm hgm ξ₀ hξ₀
  have hL := _root_.GlobalTheory.Poinc.GenPull.lbIso_gen_pull FinalForm U' gm ψ hψφ hLB
  obtain ⟨c', pr', χ, hS', hχ, hpr'⟩ := sharpBy_pull F W ρ.P A' u (ξ₀ ≫ FinalForm.u₀) (ξ₀ ≫ FinalForm.u₀ ≫ u)
    (Category.assoc _ _ _) c pr (ψ ≫ pullback.fst _ _) hS hψpb hL
  refine ⟨c', pr', hS', fun a b f f' hf hff' => ?_⟩
  obtain ⟨-, f₁, hf₁, hf₁φ⟩ := hf
  refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, ?_, by simp⟩
  refine _root_.GlobalTheory.MatEndPull.matEnd_pull pr pr' a b f₁ _ hψpb hχ hpr' ?_ hf₁
  have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
    pullback.lift_fst _ _ _
  have hmapf₁ : ((Over.pullback FinalForm.u₀).map f₁).left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f₁.left :=
    pullback.lift_fst _ _ _
  have key : (U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom).left ≫ ψ = ψ ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply FinalForm.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hψφ, reassoc_of% hgi, reassoc_of% hmapf, hff', hf₁φ, reassoc_of% hψφ]
    · have w1 : ((Over.pullback FinalForm.u₀).map f₁).left ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom =
          ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom := Over.w _
      have w2 : ψ ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom = A'.A.hom ≫ ξ₀ := hψs
      simp only [Category.assoc, w1, w2]
      rw [← Category.assoc, Over.w]
  rw [← Category.assoc, key, Category.assoc, hmapf₁, Category.assoc]

end GlobalTheory.Poinc.Eq8.PullAlong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem sharpOver_unique : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u →
    GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' →
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  intro g n F W T T' P P' u u' h hu hS hS'
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀

  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  refine ⟨α, ⟨hpb, hmul⟩, ?_⟩
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ ε
  have l2 : (LB.LinComb (c'.P.pull κ₂) q ε).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q ε
  have l3 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' ε).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' ε).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    LBIso.chartPull (chartPullOut c'.P q' ε α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb (c'.P.pull κ₂) q ε) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q ε) (LB.LinComb c.P q ε) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q ε
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q ε) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  exact LBIso.trans P.isLB l3 h1 hbun chain.symm

end GlobalTheory.Poinc
end
end

