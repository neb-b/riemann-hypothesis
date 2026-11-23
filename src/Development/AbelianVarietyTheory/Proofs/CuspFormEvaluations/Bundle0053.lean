module

public import Mathlib
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSecondPartialLawTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeepSubMulRecAll
section
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem deepSubMul_rec_all : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), EtaleWeightGaps.DeepSubMul (recPJ h j hj) ∧ EtaleWeightGaps.DeepSubMul (recPlus h j hj) ∧ ∀ (j' : ℕ) (ka : WeightFamilies.Wt D j') (Nt : NetData (recB h.toLawsCore) j' ka) (hM : NetMax Nt) (hL : NetLeSup Nt), EtaleWeightGaps.DeepSubMul (B := Nt.Bp hM hL) (PJ.tol2NormAlt _ _ _ _ _ _ (recPlus h j hj)) := by
  intro D T h j hj
  have h0 : EtaleWeightGaps.DeepSubMul (recPJ h j hj) := recSubMul D T h j hj
  have h1 : EtaleWeightGaps.DeepSubMul (recPlus h j hj) := h0
  exact ⟨h0, h1, fun j' ka Nt hM hL => h1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem isFrame_of_isAnE (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) :
    IsFrame y g Φ.jx (anFB ty).G.F (anFB ty).A.act (anFB ty).ph1 (anFB ty).ph2 (anFB ty).sy (anFB ty).ad e := by
  have hI := _root_.GlobalTheory.FrameImm.anPt_imm E H Dw l Xo c y g ty el Φ
  exact ⟨fun m => (he m).1, _root_.GlobalTheory.AnValPh1.first_partial_law E H Dw l Xo c y g ty el Φ hI e he,
    _root_.GlobalTheory.AnValSecondLaw.second_law E H Dw l Xo c y g ty el Φ hI e he, _root_.GlobalTheory.AnVal.Sym.sy_trivial E H Dw l Xo c y g ty el Φ hI e he,
    _root_.GlobalTheory.AnValAd.adjoint_series_trivial E H Dw l Xo c y g ty el Φ hI hst e he⟩

theorem isGerm_tay_of_rd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (wP : PrimTy H Xo) (hw : IsPrim wP) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ)
    (hF : Φ.toAnFr.Rd k F θ) : IsGerm y g Φ.jx (anFB ty).A.act e wP k F (tay θ 0) := by
  simp only [IsGerm]
  intro m
  have hJ : Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) :=
    (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  obtain ⟨τ, -, hτ⟩ := _root_.GlobalTheory.AnValJetEx.exists_gen_jetRd _ _ _ _ _ Φ.toAnFr 1 m (Fin 1) (fun _ => (Φ.jx m).left) (fun _ => (k : ℤ))
    (fun _ => LinearMap.proj 0) (fun _ => hJ)
  obtain ⟨F', hpull, hval⟩ := GlobalTheory.T.isValueAt_jetPoint_cmFrame_section E H Dw l Xo c y g ty el Φ m k F θ τ hF hτ
  have hc := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (_root_.GlobalTheory.FrameImm.anPt_imm E H Dw l Xo c y g ty el Φ) e wP he hw).1 m k τ hτ
  exact ⟨F', τ, hpull, hc, hval⟩

noncomputable def AnPt.chartOf (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e)
    (wP : PrimTy H Xo) (hw : IsPrim wP) : ChartAt Xo c y where
  d := g
  B := anFB ty
  uvec := anUvec el
  x := Φ.jx
  e := e
  wP := wP
  h := 0
  chart := _root_.GlobalTheory.AnVal.anPt_isChart E H Dw l Xo c y g ty el Φ
  frame := isFrame_of_isAnE Φ hst e he
  prim := hw
  gauge := anFB_canon ty
  rig0 := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (_root_.GlobalTheory.FrameImm.anPt_imm E H Dw l Xo c y g ty el Φ) e wP he hw).2

end

theorem rename_cast_refl {g : ℕ} (f : MvPowerSeries (Fin 1 × Fin g) ℂ) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) f = f := by
  have h : (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) = id := funext fun p => rfl
  rw [h]
  exact MvPowerSeries.rename_id_apply f

theorem exists_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hst
  obtain ⟨e, he⟩ := _root_.GlobalTheory.AnVal.exists_isAnE E H Dw l Xo c y g ty el Φ
  obtain ⟨wP, hw⟩ := (_root_.GlobalTheory.AnVal.PrimRd.prim_reading E H Dw l Xo c y g ty el Φ).1
  refine ⟨AnPt.chartOf Φ hst e he wP hw, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    first
      | rfl
      | simp [AnPt.chartOf, anFB, Germ.FB.triv, addFGLaw]
  · intro ℓ i'
    first
      | rfl
      | simp [AnPt.chartOf, anUvec, Pi.single_apply, eq_comm]
      | (simp only [AnPt.chartOf, anUvec]; done)
  · intro k F θ hF
    show IsGerm y g Φ.jx (anFB ty).A.act e wP k F
      (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) (tay θ 0))
    rw [rename_cast_refl]
    exact isGerm_tay_of_rd Φ e he wP hw k F θ hF

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameOfUnitUniformisationFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_anPt_of_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), letI : Algebra c.F ℂ := σ.toAlgebra; ∃ Φ : AnPt (Xo := Xo) (c := c) (U.un k x) W.g (fun j => relab c σ (W.e j).1) W.e, Φ.OfFam W.F (W.ik k) W.Pm ∧ Φ.Hm = Wu.Hm ∧ Φ.χ = Wu.χl ∧ Φ.fr = Wu.fr ∧ Φ.toAnFr.Rd 1 (U.un k x).s Wu.θ ∧ (∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ) ∧ (∀ (α : 𝓞 E) a, W.Pm (W.F.t (W.ik k) (α • a)) = tyAct (fun j => relab c σ (W.e j).1) α (W.Pm (W.F.t (W.ik k) a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo (U.un k x).x a = Φ.e ((l.M : ℂ)⁻¹ • W.Pm (W.F.t (W.ik k) a)) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hAH : AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr := by
    refine ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, ?_, Wu.c6⟩
    intro j hj
    rw [← W.pt]
    exact Wu.c5 j hj
  obtain ⟨Φ, hO, hH, hχ, hfr, hlin, hlev⟩ := _root_.GlobalTheory.AnVal.anPt_of_family E H Dw l Xo c (U.un k x) W.g
    (fun j => relab c σ (W.e j).1) W.e _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per W.pt hAH
    (fun ℓ => W.der ℓ.1 ℓ.2)
  have hRd : ∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ := by
    intro kk F θ
    unfold AnFr.Rd IsFrRd
    constructor
    · intro h j z pt h1 h2 h3
      rw [← hO.1 z] at h1 h3
      rw [← hfr]
      exact h j z pt h1 h2 h3
    · intro h j z pt h1 h2 h3
      rw [hO.1 z] at h1 h3
      rw [hfr]
      exact h j z pt h1 h2 h3
  refine ⟨Φ, hO, hH, hχ, hfr, ?_, hRd, hlin, hlev⟩
  refine (hRd _ _ _).2 ?_
  intro j z pt h1 h2 h3
  rw [zpow_one]
  exact Wu.c7 j z pt h1 h2 h3

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.HostClear

theorem absNorm_pos (D : D7) : 0 < Ideal.absNorm D.host.ccK :=
  Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem d_pos (D : D7) : 0 < D.host.d := D.host.hyp.2.1.pos

theorem sqrt_ne_zero (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 := D.host.sqrtMinusD_sq
  rw [h] at h1
  have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
  exact (d_pos D).ne' (by exact_mod_cast h2)

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) :
    ‖τ D.host.xi0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have hn : ‖τ D.host.sqrtMinusD‖ ^ 2 = D.host.d := by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg, Complex.norm_natCast]
  have h1 : ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  unfold Formalism.BasicNotions.Host.xi0
  rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, h1]

theorem different_le (D : D7) : differentIdeal ℤ (𝓞 D.host.E) ≤ D.host.𝔟 := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)]
  refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
  rw [D.host.𝔟_spec.1]
  exact Ideal.mul_le_inf.trans inf_le_left

theorem isIntegral_mul_of_mem (D : D7) {z : 𝓞 D.host.E} (hz : z ∈ D.host.𝔟) {a : D.host.E} (ha : a ∈ D.host.AA) :
    IsIntegral ℤ ((z : D.host.E) * a) := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have : (z : D.host.E) * a = (w : D.host.E) := by
    rw [mul_comm]; exact hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem absNorm_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, D.host.ccE.mul_mem_right z h1, ?_⟩
  rw [map_mul, map_natCast]

theorem host_clear : ∀ (D : D7) (L : ℝ), 2 ≤ L → lrd D ≤ 2 * L → Real.log D.host.d ≤ 2 * L → Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * L → (∃ NA : ℕ, 0 < NA ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ ((NA : D.host.E) * a)) ∧ Real.log NA ≤ 4 * L) ∧ ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA ∧ 0 < Ideal.absNorm D.host.ccK ∧ (∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : D.host.E) * (2 * D.host.xi0)) ∧ Real.log m ≤ 4 * L) ∧ Real.log (1 / (2 * xiR D)) ≤ 3 * L ∧ fdeg D.host.E = D.R.f ∧ Real.log (dE D.host.E) ≤ 4 * fdeg D.host.E * L ∧ Real.log (rdE D.host.E) ≤ 2 * L ∧ D.R.f ≤ D.R.r ∧ 1 ≤ D.R.f ∧ ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 ∧ D.host.xi0 ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D) := by
  intro D L hL hrd hd hc
  have hN := absNorm_pos D
  have hd0 := d_pos D
  have hNR : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd0
  have hNE : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := sqrt_ne_zero D
  have hfin := GlobalTheory.PinNum.finrank_host D
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg; rw [hfin]; omega
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hlog : Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| ≤ 4 * D.R.f * L := by
    unfold lrd at hrd
    rw [div_le_iff₀ (by positivity)] at hrd
    linarith
  refine ⟨?_, absNorm_mem_AA D, hN, ?_, ?_, hfd, ?_, ?_, ?_, hf1, conj_xi0_alt D, ?_, ?_⟩
  · have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨N, hN0, hNm, hNle⟩ := _root_.GlobalTheory.exists_natCast_mem_differentIdeal_pow_le D.host.E
    refine ⟨N, hN0, fun a ha => ?_, ?_⟩
    · have := isIntegral_mul_of_mem D (different_le D hNm) ha
      simpa using this
    · have hNR' : (0 : ℝ) < N := by exact_mod_cast hN0
      have h1 := Real.log_le_log (by positivity) hNle
      rw [Real.log_pow, Real.log_pow, hfin] at h1
      push_cast at h1
      have h2 : (D.R.f : ℝ) * Real.log N ≤ D.R.f * (4 * L) := by linarith
      exact le_of_mul_le_mul_left h2 (by linarith)
  · refine ⟨Ideal.absNorm D.host.ccK * D.host.d, Nat.mul_pos hN hd0, ?_, ?_⟩
    · have h1 : ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : D.host.E) * (2 * D.host.xi0) =
          2 * D.host.sqrtMinusD := by
        have h2 : (D.host.d : D.host.E) = -D.host.sqrtMinusD ^ 2 := by
          rw [D.host.sqrtMinusD_sq, neg_neg]
        unfold Formalism.BasicNotions.Host.xi0
        push_cast
        rw [h2]
        field_simp
      rw [h1]
      exact IsIntegral.mul (by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2) (sqrtMinusD_isIntegral D)
    · push_cast
      rw [Real.log_mul hNR.ne' hdR.ne']
      linarith
  · have hsq : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 hdR
    have h1 : 1 / (2 * xiR D) = (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 := by
      unfold xiR
      rw [norm_embedding_hostFormConstant_eq]
      field_simp
    rw [h1, Real.log_div (by positivity) two_ne_zero, Real.log_mul hNR.ne' hsq.ne', Real.log_sqrt hdR.le]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  · rw [hfd]; exact hlog
  · unfold rdE dE
    rw [Real.log_rpow hdisc, hfin]
    unfold lrd at hrd
    push_cast
    rw [one_div_mul_eq_div]
    exact hrd
  · have h1 := D.R.f_le_k
    have h2 := D.R.two_le_m
    unfold Ranks.f Ranks.n Ranks.r
    omega
  · unfold Formalism.BasicNotions.Host.xi0
    exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hNE hs)
  · intro τ
    unfold xiR
    rw [norm_embedding_hostFormConstant_eq, norm_embedding_hostFormConstant_eq]

end GlobalTheory.HostClear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverShortThetaValueData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H) :
    Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h2 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h2
    have h3 : (l.M : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr (by have := l.three_le; omega)
    exact h3 h2
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot l.Mb hne
  have : Module.Finite (𝓞 E) Dw.La := Dw.fin
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) :=
    Module.Finite.of_restrictScalars_finite (𝓞 E) (𝓞 E ⧸ l.Mb) (LevQ Dw l)
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem exists_cover_shortVal_data :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo y'.x z ∧ (∀ q b, tp q b ^ N = levPt Xo y'.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) ∧ (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (z i b) (tp q b) (F q i b)) := by
  intro hL E _ _ _ H Dw l Xo c n Λ N hU hT hN S _ _ y
  have hN0 : 0 < N := hN.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := le_trans hN.2.2 inf_le_left
  have hlev : ∀ {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ Xo.X) (x' : Sp R' ⟶ Xo.X)
      (h : ptO Xo x' ⟶ ptO Xo x) (a : Dw.La), h ≫ levPt Xo x a = levPt Xo x' a := by
    intro R R' _ _ x x' h a
    rw [levPt, levPt, ← Category.assoc, comp_toUnit]
  have hkill : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), KilledBy Xo l.Mb (levPt Xo x a) := by
    intro R _ x a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  have hpowM : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ l.M = 1 := by
    intro R _ x a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hpowN : ∀ {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x a ^ N = 1 := by
    intro R _ x a
    obtain ⟨k, hk⟩ := hN.2.1
    rw [hk, pow_mul, hpowM, one_pow]
  have : Finite (LevQ Dw l) := finite_levQ Dw l
  let _ : Fintype ((Fin n → LevQ Dw l) × Fin n) := Fintype.ofFinite _
  obtain ⟨B1, _, φ1, w, hφ1, hw⟩ := _root_.GlobalTheory.exists_faithfullyFlat_roots hL E H Dw l Xo S y.x N l.M hN0
    (by have := l.three_le; omega) ((Fin n → LevQ Dw l) × Fin n)
    (fun j => levPt Xo y.x (levRep (j.1 j.2))) (fun j => hpowM _ _)
  have hw' : ∀ j, w j ^ N = levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2)) := by
    intro j
    apply Over.OverMorphism.ext
    rw [hw j, ← hlev y.x (spMap φ1 ≫ y.x) (Over.homMk (spMap φ1) rfl), Over.comp_left]
    rfl
  have hroot := fun j => (exists_root_killedBy_pow E H Dw l Xo (ptO Xo (spMap φ1 ≫ y.x))
    (levPt Xo (spMap φ1 ≫ y.x) (levRep (j.1 j.2))) (w j) N hN0 (hkill _ _) (hw' j)).1
  choose tp1 htp1 htp1k using hroot
  obtain ⟨B2, _, φ2, z, hφ2, hz, hzg⟩ := _root_.GlobalTheory.exists_faithfullyFlat_split_Zh hL E H Dw l Xo B1 (spMap φ1 ≫ y.x) n Λ N hU hN0 hle
  let _ : Algebra c.F B2 := ((φ2.comp φ1).comp (algebraMap c.F S)).toAlgebra
  let φA : S →ₐ[c.F] B2 := { toRingHom := φ2.comp φ1, commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c S B2 φA y
  have hyx : y'.x = spMap φ2 ≫ spMap φ1 ≫ y.x := by
    rw [hy'.1, ← Category.assoc, FramedBaseChange.spMap_spMap]
  let hA : ptO Xo y'.x ⟶ ptO Xo (spMap φ1 ≫ y.x) := Over.homMk (spMap φ2) hyx.symm
  let hB : ptO Xo y'.x ⟶ ptO Xo (spMap φ2 ≫ spMap φ1 ≫ y.x) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact hyx.symm)
  have hI := _root_.GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  have hz' : ∀ i, InZh Xo Λ N (fun b => hB ≫ z i b) := fun i => hI.1 _ _ hB (z i) (hz i)
  have htpN : ∀ q b, (hA ≫ tp1 (q, b)) ^ N = levPt Xo y'.x (levRep (q b)) := by
    intro q b
    rw [← MonObj.comp_pow, htp1, hlev]
  have hUU := (exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN.1 (ptO Xo y'.x) y'.s).2
  have hF : ∀ (q : Fin n → LevQ Dw l) (i : Fin (Λ.zCard N (Dw.p + Dw.q))) (b : Fin n), ∃ F,
      IsUUOver Xo.univ.t.G Xo.univ.t.PP N y'.s (hB ≫ z i b) (hA ≫ tp1 (q, b)) F := by
    intro q i b
    refine (hUU _ _ ((hz' i).1 b) ?_).exists
    rw [pow_two, pow_mul, htpN, hpowN]
  choose F hF using hF
  refine ⟨B2, inferInstance, inferInstance, φA, y', fun i b => hB ≫ z i b, fun q b => hA ≫ tp1 (q, b), F,
    RingHom.FaithfullyFlat.stableUnderComposition φ1 φ2 hφ1 hφ2, hy', hz', ?_, ?_, hF⟩
  · exact hI.2.2.1 B2 B2 _ y'.x (RingHom.id B2) hB
      (Spec.map_id (CommRingCat.of B2)).symm _ z hzg
  · intro q b
    obtain ⟨j, hj⟩ := htp1k (q, b)
    exact ⟨htpN q b, j, fun a ha => by rw [Category.assoc, hj a ha, MonObj.comp_one]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore : ∀ (D : D7) (T : Core D), LawsCore T → GamAt T := by
  intro D T h j hj σ hσ k γ h1 h2
  exact _root_.GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ k γ h1 h2

end GlobalTheory.RunIn
end

