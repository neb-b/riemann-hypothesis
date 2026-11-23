module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSumma
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGood
open ReciprocityTheory.L2DbarEstimates (V)

theorem goodBound_submatrix {n : ℕ} {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (e : K ≃ L) {S : Finset (Fin n)} {c : ℝ} {N : ℕ} {G : V n → Matrix L L ℂ} {v : V n}
    (h : GoodBound S c N G v) : GoodBound S c N (fun u => (G u).submatrix e e) v := by
  refine ⟨fun i j => h.entry (e i) (e j), ?_, ?_, ?_, ?_⟩
  · simpa only [det_submatrix_equiv_self] using h.det
  · intro a i j
    simpa only [GlobalTheory.HermFrame.conn_submatrix_equiv, Matrix.submatrix_apply]
      using h.form a (e i) (e j)
  · intro a b i j
    simpa only [GlobalTheory.HermFrame.curv_submatrix_equiv, Matrix.submatrix_apply]
      using h.dbar a b (e i) (e j)
  · intro a b i j
    have h1 : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn (fun x => (G x).submatrix e e) u ξ) =
        fun u => (GlobalTheory.HermFrame.conn G u ξ).submatrix e e :=
      fun ξ => funext fun u => GlobalTheory.HermFrame.conn_submatrix_equiv G e u ξ
    simp only [h1]
    exact h.del a b (e i) (e j)

theorem frame_summands_goodBound : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  intro n g S W G₀ c N ι _ _ m Q r hW hr hQ hcard hind hG₀ horth
  let K := Σ τ, Fin (m τ)
  let e : K ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let P : V n → Matrix K K ℂ := fun u => Matrix.of fun p k => Q p.1 u p.2 (e k)
  let G₁ : V n → Matrix K K ℂ := fun u => (G₀ u).submatrix e e
  have hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r) := fun i k => hQ i.1 i.2 (e k)
  have hP0 : IsUnit (P 0).det := by
    rw [← isUnit_iff_isUnit_det, ← linearIndependent_row_iff_isUnit]
    have h2 := hind.map' _ (LinearEquiv.ker (LinearEquiv.funCongrLeft ℂ ℂ e))
    have h3 : (P 0).row = ⇑(LinearEquiv.funCongrLeft ℂ ℂ e) ∘ fun p => Q p.1 0 p.2 := by
      funext p k; rfl
    rw [h3]; exact h2
  have hG₁ : ∀ v ∈ W, (G₁ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₁ u i k) v) ∧
      GoodBound S c N G₁ v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hG₀ v hv
    exact ⟨by simpa [G₁, det_submatrix_equiv_self] using h1, fun i k => h2 (e i) (e k),
      goodBound_submatrix e h3⟩
  obtain ⟨r₁, hr₁, -, B, hB⟩ := _root_.GlobalTheory.HermFrame.holoFrame_local_bounds n K P r hr hP hP0
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame n K S c N B
  let Gb : V n → Matrix K K ℂ := fun u => blockDiagonal' fun τ => Q τ u * G₀ u * (Q τ u)ᴴ
  obtain ⟨c', N', h3⟩ := GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal n S ι m (fun τ u => Q τ u * G₀ u * (Q τ u)ᴴ) c₁ N
  refine ⟨min r₁ (1 / 2), by positivity, c', N', fun v hv hvr τ => ?_⟩
  have hv1 : ‖v‖ < r₁ := hvr.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < 1 / 2 := hvr.trans_le (min_le_right _ _)
  obtain ⟨hPu, hPc, hPd, hPb, hPib, hPdb, hPddb⟩ := hB v hv1
  obtain ⟨hdet, hC, hgb⟩ := hG₁ v hv
  obtain ⟨d1, c1, g1⟩ := hc₁ G₁ P v (by linarith) hdet hC hPc hPd hPu hPb hPib hPdb hPddb hgb
  have heq : ∀ u ∈ W, P u * G₁ u * (P u)ᴴ = Gb u := by
    intro u hu
    ext ⟨τ, i⟩ ⟨τ', j⟩
    have key : (P u * G₁ u * (P u)ᴴ) ⟨τ, i⟩ ⟨τ', j⟩ = (Q τ u * G₀ u * (Q τ' u)ᴴ) i j := by
      simp only [P, G₁, Matrix.mul_apply, conjTranspose_apply, of_apply, submatrix_apply]
      exact Fintype.sum_equiv e _ _ fun l => by
        congr 1
        exact Fintype.sum_equiv e _ _ fun k => rfl
    by_cases hτ : τ = τ'
    · subst hτ
      rw [key]
      simp only [Gb, blockDiagonal'_apply_eq]
    · rw [key, horth u hu τ τ' hτ]
      simp only [Gb, blockDiagonal'_apply_ne _ _ _ hτ, Matrix.zero_apply]
  have hev : (fun u => P u * G₁ u * (P u)ᴴ) =ᶠ[𝓝 v] Gb :=
    Filter.eventually_of_mem (hW.mem_nhds hv) heq
  refine h3 v (fun a _ => (PiLp.norm_apply_le v a).trans_lt hv2) ?_ ?_ ?_ τ
  · change (Gb v).det ≠ 0
    rw [← heq v hv]; exact d1
  · intro p q
    exact (c1 p q).congr_of_eventuallyEq (hev.mono fun u hu => by
      exact (congrFun (congrFun hu p) q).symm)
  · exact _root_.GlobalTheory.GoodMetric.goodBound_congr_nhds n K S c₁ N _ Gb v hev g1

end GlobalTheory.FrameGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesSameComponentNearChart
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HodgeSmooth.chart_comp_locconst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ r U hσ hU h1 n ch hsy k₀ x₀ hy₀
  obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU h1
  have := Z.jQ_open
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.target | ⊤ ≤ (ch.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  set y₀ := U.un k₀ x₀ with hy₀def
  have hb₀ : ch (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.map_source hy₀, ?_⟩
    rw [ch.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.symm b).2
  obtain ⟨B, i, P, hB, hbB, hsub, hP, hu⟩ := W.F.lift n B₀ (fun x => w x ≫ pullback.fst _ _) hB₀
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl) hyh _ hb₀
  have hik : ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → W.ik k = i := by
    intro z hz k x hkx
    have h1' : w z = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) (U.un k x) :=
      (cancel_mono Z.jQ).1 ((hw z (hsub hz)).trans (congrArg Subtype.val hkx.symm))
    have h2 : W.F.u i (P z) = (U.un k x).x := by
      rw [hu z hz, h1']
      exact GlobalTheory.ShFam.ptF_fst _
    exact W.F.disj _ _ _ _ (W.period k x) (hP.1 z hz) ((W.lie k x).1.symm.trans h2.symm)
  have hk₀ : W.ik k₀ = i := hik _ hbB k₀ x₀ (by rw [ch.left_inv hy₀])
  exact ⟨B, hB, hbB, fun z hz k x hkx => hinj ((hik z hz k x hkx).trans hk₀.symm)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChange
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointLift

open ReciprocityTheory.ChartRestriction.G.FD

theorem pm_lift_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  intro E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq
  obtain ⟨k₁, x₁, t, hB⟩ := hU.2.2.1 q
  have hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := (W.lie k₁ x₁).1
  have hk : k₁ = k := hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))
  subst hk
  obtain ⟨gam, h, hEF, -, -, hgh⟩ := (W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1
    (by rw [hq, ← hx₁, hB.1])
  let φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap
  have hφi : Function.Injective φL := (U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective
  have hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k₁ a).2
    · intro hv
      exact ⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩
  have hspan : Submodule.span E (Set.range φL) = ⊤ := by rw [hrange]; exact (U.X k₁).Λ_span
  have hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0) := by
    have h0 := (U.X k₁).ξ0_im
    unfold cc at h0 ⊢
    rw [map_neg, h0]
  have hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧
      (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧
      ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y)) :=
    ⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩
  obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam
    hcc hl hl hEF
  have hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹ := by
    refine ⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [← hγh, hinv', hinv']
    · obtain ⟨b, hb⟩ : v ∈ Set.range φL := by rw [hrange]; exact hv
      have e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b) := by
        rw [← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]
      rw [e]
      exact (W.φ k₁ (gam.symm b)).2
    · obtain ⟨a, ha⟩ : _ ∈ Set.range φL := by rw [hrange]; exact hv
      have e : v = φL (gam a) := by rw [hγφ, ha, hinv']
      rw [e]
      exact (W.φ k₁ (gam a)).2
  let x' : (U.X k₁).dom := ⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩
  have hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a) := by
    intro a
    funext j
    rw [W.Pm_eq, W.Pm_eq]
    have e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        (W.φ k₁ (gam a) : Fin r → E) := by
      change φL a = _ *ᵥ φL (gam a)
      rw [hγφ, hinv]
    rw [e]
    exact GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _
  have hQx : ∀ a, W.Pm k₁ x' a = h (Q a) := fun a => by rw [hPm, hgh]
  have hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x') :=
    (W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2
      ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩,
        fun a => hQx a⟩
  refine ⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩
  rw [hQx, LinearEquiv.symm_apply_apply]

end GlobalTheory.PointLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwap
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PosDefSwap


open scoped Matrix.Norms.L2Operator in
theorem one_sub_mul_conjTranspose_posDef {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (h : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).PosDef := by
  have h1 : ‖z‖ < 1 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one z).mp h
  have h2 : ‖zᴴ‖ < 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have h3 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one zᴴ).mpr h2
  rwa [Matrix.conjTranspose_conjTranspose] at h3

theorem main : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef :=
  fun z h => one_sub_mul_conjTranspose_posDef z h

end GlobalTheory.PosDefSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransport
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCorr

theorem psi_sq_terms_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  obtain ⟨σ', f', hE', hrel⟩ := GlobalTheory.T.exists_bundleSquare_section_transport_expansion R hR G hsa D D' A A' U U' wL hwL σ
  refine ⟨σ', f', hE', fun β Z ρ z J J' hJ hJ' => ?_⟩
  have hφ : ∀ κ, D'.toPre.famφB (2 • β) κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB (xe (2 • β)) κ :=
    PsiCompare.famφB_comp Φ.hom (hc β)
  refine GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points R hR G hsa D D' A A' U U' Φ w hw (fun e => (hlev e).1) _ _ hφ (f _) (f' _)
    (fun e Z r z J J' hJ hJ' => ?_) Z ρ z J J' hJ hJ'
  have hB := GlobalTheory.T.termExpansion_weight_correspondence_at_level R hR G hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht σ σ' f f' hE hE' hrel e Z r z J J' hJ hJ' (2 • β)
  have hC := GlobalTheory.T.torus_coord_squares_correspond' R hR G hsa D D' A A' U U' Φ w hw hΦ (fun e => (hlev e).1) xe ht β (hc β) e Z r z J J' hJ hJ'
  have hP := ExpTrans.prod_fam U'.toUnifPre e 2 (fun ψ => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ ψ)) (2 • β)

  set a := sval (f (xe (2 • β))) (r ≫ (U.gt e).pG.left) z J
  set b := sval (f' (2 • β)) (r ≫ (U'.gt e).pG.left) z J'
  set T := val ((U.gt e).t (xe (2 • β))) r z J
  set T' := val ((U'.gt e).t (2 • β)) r z J'
  set O := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)
  set P := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ
  set F := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ
  have hP' : F * P = O ^ 2 := hP
  have key : a ^ 2 * (P * T' ^ 2).val = F.val * b ^ 2 * (P * T' ^ 2).val := by
    calc a ^ 2 * (P * T' ^ 2).val = a ^ 2 * (T ^ 2).val := by rw [hC]
      _ = (a * T.val) ^ 2 := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (O.val * b * T'.val) ^ 2 := by rw [hB]
      _ = (O ^ 2).val * b ^ 2 * (T' ^ 2).val := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (F * P).val * b ^ 2 * (T' ^ 2).val := by rw [hP']
      _ = F.val * b ^ 2 * (P * T' ^ 2).val := by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  exact (Units.mul_left_inj (P * T' ^ 2)).1 key

end GlobalTheory.SqCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
section
noncomputable section

namespace GlobalTheory.PolFan.OrbMark

variable {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def pullAdd (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : LinearMap.BilinForm ℤ X :=
  u.compl₁₂ f.toIntLinearMap f.toIntLinearMap

@[simp] theorem pullAdd_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) (x y : X) : pullAdd f u x y = u (f x) (f y) := rfl

theorem pullAdd_injective {f : X →+ Y} (hf : Function.Surjective f) : Function.Injective (pullAdd f) :=
  fun u u' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact LinearMap.congr_fun₂ h a b

def pullAddLin (f : X →+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pullAdd f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RadicalPrincipalIdealsStayRadicalFlagComponent
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagCptRad

theorem isHom_apply_eq {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    {M : GlobalTheory.ZH.RatModel F Ω} {M' : GlobalTheory.ZH.RatModel F Ω'} {φ ψ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}
    (hφ : M.IsHom M' φ f) (hψ : M.IsHom M' ψ f) (x : Ω) : φ x = ψ x := by
  have hx : ∀ w, x ∈ M.O (f (M'.pt w)) := fun w => by
    have e1 : (M'.pt ≫ f) w = f (M'.pt w) := Scheme.Hom.comp_apply _ _ _
    have e2 : (M'.pt ≫ f) w = genericPoint M.Z := by
      rw [hφ, Scheme.Hom.comp_apply, M.pt_apply]
    rw [← e1, e2, M.O_genericPoint]; exact Algebra.mem_top
  have h1 := hφ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  have h2 := hψ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  rw [GlobalTheory.ZH.RatModel.val_pt] at h1 h2
  exact h1.symm.trans h2

theorem keepsRad_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hj hjs f hf f₀ Eb A₀ hT hlift φ hφ
  haveI : CharZero F := RingHom.charZero e.toRingHom
  obtain ⟨Y', φ', f', S', -, hR⟩ := tower _ (ratOf X) X.dim Eb (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  change Y'.X ⟶ X.X at f'
  obtain ⟨h, hh, hbij⟩ := _root_.GlobalTheory.ShFam.ClsMap.main E H Dw l Xo c O β Z F e C X j hj hjs f hf f₀ Eb A₀ hT hlift Y' φ' f' S' hR
  have hs' : f' ≫ X.str = Y'.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hstr : h ≫ Y'.str = C.Y.str := by
    rw [← hs', ← Category.assoc, hh, ← hjs, ← C.π_str, ← hf, Category.assoc]
  have hiso : IsIso h := _root_.GlobalTheory.BijPointsIso.isIso_of_bijective_points F C.Y Y' h hstr hbij
  obtain ⟨ψ, S'', hR2⟩ := exists_refines_of_iso (ratOf Y') (ratOf C.Y) (@asIso _ _ _ _ h hiso) hstr S'
  have hR2' : Refines S' S'' ψ h := hR2
  subst hh
  have hR3 := hR.comp hR2'
  have hrad : KeepsRad (ratOf X) (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.rad
  have hhom : (ratOf X).IsHom (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.hom
  intro z' g hg
  rw [isHom_apply_eq hφ hhom g]
  exact hrad z' g hg

end GlobalTheory.FlagCptRad
end

