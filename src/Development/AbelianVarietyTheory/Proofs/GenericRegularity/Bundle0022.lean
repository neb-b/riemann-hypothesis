module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartGeneratorPullbackGeneratesFibre
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsContinuousOnEmbeddings
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frPt_tie : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R, (∀ τ i, M.Eig f τ (fun j => u τ j i)) → (∀ τ cv, M.Eig f τ cv → ∃! a : Fin (Dw.mult τ) → R, (u τ).mulVec a = cv) → ∃ y : FrPt Xo c R, y.x = x ∧ M.Comparison₂ f u y := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ u hu huniq
  have hover : x ≫ Xo.s = sOf c R := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    unfold sOf spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hV := _root_.GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M R f x Λ
  choose w hw _ using fun τ (i : Fin (Dw.mult τ)) => hV.1 (fun j => u τ j i)
  obtain ⟨s, hs, hgen⟩ := _root_.GlobalTheory.Reg.ChartGenerator.exists_thTie_generator hT E H Dw l Xo c O β Y M R f x Λ
  refine ⟨⟨x, hover, w, fun τ i => hV.2.1 _ _ (hw τ i),
    fun τ i => (_root_.GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M R f x Λ τ _ _ (hw τ i)).2 (hu τ i), ?_, s, hgen⟩,
    rfl, Λ, fun τ i => hw τ i, hs⟩
  intro τ v hvt hve
  obtain ⟨cv, hcv, hcvu⟩ := hV.2.2 v hvt
  have hcomb : ∀ a, IsCombAt x (w τ) a v ↔ Λ.Vec ((u τ).mulVec a) v := by
    intro a
    have hsum : (∑ i, a i • fun j => u τ j i) = (u τ).mulVec a := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [_root_.GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M R f x Λ _ (fun i j => u τ j i) (w τ) a v (hw τ), hsum]
  have hcve : M.Eig f τ cv := (_root_.GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M R f x Λ τ cv v hcv).1 hve
  obtain ⟨a, ha, hau⟩ := huniq τ cv hcve
  refine ⟨a, (hcomb a).2 (ha ▸ hcv), fun a' ha' => hau a' ?_⟩
  exact hcvu _ ((hcomb a').1 ha')

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankEqOfExistsUniqueComb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.Reg

theorem finrank_eq_of_existsUnique_comb {L V : Type} [Field L] [AddCommGroup V] [Module L V] (N : Submodule L V)
    {m : ℕ} (cv : Fin m → V) (hcv : ∀ i, cv i ∈ N) (h : ∀ v ∈ N, ∃! a : Fin m → L, ∑ i, a i • cv i = v) :
    Module.finrank L N = m := by
  have hli : LinearIndependent L cv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := (h 0 N.zero_mem).unique hg (y₂ := 0) (by simp)
    rw [this]; rfl
  have hN : N = Submodule.span L (Set.range cv) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, rfl, -⟩ := h v hv
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hcv i
  rw [hN, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_chart_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (x : Sp L ⟶ Xo.X) (Λ : M.Lift f x) (τ : E →+* ℂ) (N : Submodule L (Fin M.n → L)), (∀ cv, cv ∈ N ↔ M.Eig f τ cv) → Module.finrank L N = Dw.mult τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f x Λ τ N hN
  classical
  have hx0 : x ≫ Xo.s = sOf c L := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.snd Xo.univ.t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨d, hd, hdW⟩ : ∃ d : Fin (Dw.mult τ) → Fin n → L,
      LinearIndependent L d ∧ ∀ i, d i ∈ gfpEig (c := c) hx τ := by
    obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ)) :=
      ⟨Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)⟩
    exact ⟨(gfpEig (c := c) hx τ).subtype ∘ B,
      B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _), fun i => by simp⟩
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M L f x Λ
  have hcomb := GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f x Λ
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M L f x Λ τ
  choose cv hcv using fun i => (hco _ (gfp_tan hx (d i))).exists
  refine finrank_eq_of_existsUnique_comb N cv
    (fun i => (hN _).2 ((heig _ _ (hcv i)).1 ((gfp_eig_iff hx τ _).2 (hdW i)))) fun v hv => ?_
  obtain ⟨w, hw⟩ := (hex v).exists
  have hwt := htan v w hw
  have hb := gfp_basis hx0 hx τ d hd hdW w hwt ((heig v w hw).2 ((hN v).1 hv))
  refine (existsUnique_congr fun a => ?_).1 hb
  rw [hcomb _ cv _ a w hcv]
  exact ⟨fun h => (hco w hwt).unique h hw, fun h => h ▸ hw⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointIntegralIntegralCellAnyModel
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral_of_any_model : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ :=
    sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    tie_vectors_integral E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_chartPoint_noInvert hS E H Dw l Xo c O β Y M T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_divFin_stLoc_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), 1 ≤ Dd → Dd = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) → KapFG Xo c ∧ KapTrdeg Xo c Dw.dim ∧ DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) ∧ STLoc h Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hD hDd hjc hA
  obtain ⟨hfg, htr⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : Formalism.L2.Pj.FnFG Xo c := fnFG_of Xo c hfg
  have hTr : Formalism.L2.Pj.FnTrdeg Xo c Dd := hDd ▸ fnTrdeg_of Xo c Dw.dim htr
  have hw : ∀ Z, (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z ≠ 0 := fun Z => valC_ne_zero (hjc Z)
  have hT : ∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) Z := fun Z =>
    ((GlobalTheory.differentials_iff_trdegD_and_genericSection _ _ _ _ _ (fun _ _ => ⊥) _ Z (hFG Z) (hTr Z) (hw Z)).1).1 (hA Z)
  refine ⟨hfg, htr, ?_, ?_⟩
  · exact divFin_of_trdeg E H Dw l Xo c _ hD hDd (fun Z j => valC_mem h uL.1 uL.2 (wR j) Z) hw hT
  · apply stLoc_of_trdeg E H Dw l Xo c h Dd N uL wR jc hFG hTr hjc
    intro Z
    have hZ := hT Z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD at hZ
    have key : (fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w j Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z)) =
        fun j => evC h Z (wR j) / evC h Z (wR (jc Z)) := by
      funext j
      refine ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq (valC_ne_zero (hjc Z)) ?_
      unfold dataOf valG valC
      simp [div_mul_cancel₀ _ (hjc Z)]
    rw [key] at hZ
    exact hZ


end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularInvOfDiagNe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem triangular_inv_of_diag_ne {L : Type} [Field L] {n : ℕ} (b : Matrix (Fin n) (Fin n) L)
    (hb : b.BlockTriangular id) (hd : ∀ i, b i i ≠ 0) :
    b * b⁻¹ = 1 ∧ (b⁻¹).BlockTriangular id ∧ ∀ i, b⁻¹ i i ≠ 0 := by

  have hdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  let _ : Invertible b := Matrix.invertibleOfIsUnitDet b hdet
  have htri : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.mul_nonsing_inv b hdet, htri, fun i => ?_⟩

  have hii : (b⁻¹ * b) i i = b⁻¹ i i * b i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hki with h | h
    · rw [htri h, zero_mul]
    · rw [hb h, mul_zero]
  rw [Matrix.nonsing_inv_mul b hdet, Matrix.one_apply_eq] at hii
  exact left_ne_zero_of_mul_eq_one hii.symm

theorem scal_mul_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a a' : S) (i : (PPx x).ι) :
    scal x (a * a') i = scal x a i * scal x a' i := by
  simp only [scal, map_mul, Out.liftFun]

theorem scal_one_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  simp only [scal, map_one, Out.liftFun]

theorem frBor_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y z : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), z.x = y.x → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → M.Comparison₂ f u z → ∃ t : Ix Dw → Lˣ, FrBor t y z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f y z Λ u b hxz hb hΛ hM
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  subst hxz
  obtain ⟨Λ', hΛ'u, -⟩ := hM

  have hB : ∀ τ, b τ * (b τ)⁻¹ = 1 ∧ ((b τ)⁻¹).BlockTriangular id ∧ ∀ i, (b τ)⁻¹ i i ≠ 0 :=
    fun τ => triangular_inv_of_diag_ne (b τ) (hb τ).1 (hb τ).2

  obtain ⟨a, ha, -⟩ := y.gen zs
  obtain ⟨a', ha', -⟩ := zg y.s
  obtain ⟨w, -, huniq⟩ := zg zs
  have h1 : ∀ i, zs.f i = scal y.x (a * a') i * zs.f i := fun i => by
    rw [scal_mul_tie, _root_.mul_assoc, ← ha' i, ← ha i]
  have h2 : ∀ i, zs.f i = scal y.x 1 i * zs.f i := fun i => by
    rw [scal_one_tie, _root_.one_mul]
  have haa : a * a' = 1 := (huniq _ h1).trans (huniq _ h2).symm
  refine ⟨fun k => Option.elim k (Units.mkOfMulEqOne a a' haa)
    (fun p => Units.mk0 ((b p.1)⁻¹ p.2 p.2) ((hB p.1).2.2 p.2)), ?_⟩
  unfold FrBor
  refine ⟨rfl, fun τ i => ⟨fun j => (b τ)⁻¹ j i, rfl, fun j hij => (hB τ).2.1 hij, ?_⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  ·
    refine (_root_.GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f y.x Λ (Dw.mult τ) (fun j k => (u τ * b τ) k j)
      (y.u τ) (fun j => (b τ)⁻¹ j i) (zu τ i) (fun j => hΛ τ j)).mpr ?_
    have hv := (_root_.GlobalTheory.Reg.LiftUnique.lift_indep E H Dw l Xo c O β Y M L f y.x Λ' Λ).1 _ _ (hΛ'u τ i)
    convert hv using 1
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (b τ)⁻¹ j i * (u τ * b τ) k j = (u τ * b τ * (b τ)⁻¹) k i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
      _ = u τ k i := by rw [Matrix.mul_assoc, (hB τ).1, Matrix.mul_one]
  ·
    have e : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, e, Option.elim_none, Units.val_mkOfMulEqOne]
    erw [op_id, CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.hom_id, RingHom.id_apply]
    exact (ha i).symm

end GlobalTheory.Reg
end

