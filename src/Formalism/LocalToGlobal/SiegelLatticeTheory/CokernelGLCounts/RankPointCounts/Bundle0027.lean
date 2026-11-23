module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdScal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SubOneMulVecFix
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormGeTwo
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
  Formalism.L2.SG.DataInst Formalism.L2.SG.Pf.ProdConvCut Formalism.L2.SG.Pf.AlTie

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

theorem etaV_pm (v : PlX X) :
    ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = 1 ∨ ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = -1 := by
  unfold etaV
  split_ifs <;> simp

theorem absNorm_ge_two (v : PlX X) : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem exp_bounds_prod_one_sub_pow_div (q η : ℝ) (hq : 2 ≤ q) (hη : η = 1 ∨ η = -1) (k a N : ℕ) (hk : 1 ≤ k)
    (ha : k ≤ a) :
    Real.exp (-(4 * q⁻¹ ^ k)) ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ∧
      ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ≤ Real.exp (2 * q⁻¹ ^ k) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hxq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0.ne'
  have hx2 : q⁻¹ ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hq hx0]
  have hterm : ∀ i : ℕ, |η ^ i / q ^ i| = q⁻¹ ^ i := by
    intro i
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hq0, inv_pow]
    rcases hη with rfl | rfl <;> simp
  have hsum : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ 2 * q⁻¹ ^ k := by
    have h1 : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ q⁻¹ ^ a / (1 - q⁻¹) := by
      have hI : Finset.Icc a N = Finset.Ico a (N + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hI]
      exact geom_sum_Ico_le_of_lt_one hx0 (by linarith)
    have h2 : q⁻¹ ^ a / (1 - q⁻¹) ≤ 2 * q⁻¹ ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (pow_nonneg hx0 a) (by linarith : (0 : ℝ) ≤ 1 / 2 - q⁻¹)]
    have h3 : q⁻¹ ^ a ≤ q⁻¹ ^ k := pow_le_pow_of_le_one hx0 (by linarith) ha
    linarith
  constructor
  · have hfac : ∀ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) ≤ 1 - η ^ i / q ^ i := by
      intro i hi
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hy0 : 0 ≤ q⁻¹ ^ i := pow_nonneg hx0 i
      have hy : q⁻¹ ^ i ≤ 1 / 2 := le_trans (pow_le_of_le_one hx0 (by linarith) hi1) hx2
      have hle : η ^ i / q ^ i ≤ q⁻¹ ^ i := (abs_le.mp (le_of_eq (hterm i))).2
      have he : 1 + 2 * q⁻¹ ^ i ≤ Real.exp (2 * q⁻¹ ^ i) := by
        linarith [Real.add_one_le_exp (2 * q⁻¹ ^ i)]
      have hEF : Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) = 1 := by
        rw [← Real.exp_add]
        simp
      have hE0 : 0 < Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_pos _
      have hE12 : Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i) ≤ 1 := by
        calc Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)
            ≤ Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) := mul_le_mul_of_nonneg_left he hE0.le
          _ = 1 := hEF
      have hc : 1 ≤ (1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i) := by nlinarith
      calc Real.exp (-(2 * q⁻¹ ^ i))
          ≤ Real.exp (-(2 * q⁻¹ ^ i)) * ((1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i)) := le_mul_of_one_le_right hE0.le hc
        _ = (Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)) * (1 - q⁻¹ ^ i) := by ring
        _ ≤ 1 * (1 - q⁻¹ ^ i) := mul_le_mul_of_nonneg_right hE12 (by linarith)
        _ ≤ 1 - η ^ i / q ^ i := by linarith
    calc Real.exp (-(4 * q⁻¹ ^ k))
        ≤ Real.exp (∑ i ∈ Finset.Icc a N, -(2 * q⁻¹ ^ i)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) :=
          Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) hfac
  · have hfac : ∀ i ∈ Finset.Icc a N, 1 - η ^ i / q ^ i ≤ Real.exp (q⁻¹ ^ i) := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).1
      linarith [Real.add_one_le_exp (q⁻¹ ^ i)]
    have hnn : ∀ i ∈ Finset.Icc a N, 0 ≤ 1 - η ^ i / q ^ i := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).2
      have hy : q⁻¹ ^ i ≤ 1 := pow_le_one₀ hx0 (by linarith)
      linarith
    calc ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i)
        ≤ ∏ i ∈ Finset.Icc a N, Real.exp (q⁻¹ ^ i) := Finset.prod_le_prod₀ hnn hfac
      _ = Real.exp (∑ i ∈ Finset.Icc a N, q⁻¹ ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * q⁻¹ ^ k) := Real.exp_le_exp.mpr hsum

theorem aP_bounds (hk : 1 ≤ D.R.k) (v : PlX X) (T : ℕ) :
    Real.exp (-(4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ aP (E := X.B.I.E) v D.R.k X.B.I.n T ∧
      aP (E := X.B.I.E) v D.R.k X.B.I.n T ≤ Real.exp (2 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  unfold aP
  exact exp_bounds_prod_one_sub_pow_div _ _ (absNorm_ge_two X v) (etaV_pm X v) _ _ _ hk (by split_ifs <;> omega)

private theorem exp_bounds_mul_of_exp_bounds (a b y : ℝ) (hy : 0 ≤ y)
    (ha : Real.exp (-(4 * y)) ≤ a ∧ a ≤ Real.exp (2 * y)) (hb : Real.exp (-(4 * y)) ≤ b ∧ b ≤ Real.exp (2 * y)) :
    (Real.exp (-(8 * y)) ≤ a ∧ a ≤ Real.exp (4 * y)) ∧
      (Real.exp (-(8 * y)) ≤ a * b ∧ a * b ≤ Real.exp (4 * y)) := by
  have ha0 : 0 ≤ a := le_trans (Real.exp_pos _).le ha.1
  have hb0 : 0 ≤ b := le_trans (Real.exp_pos _).le hb.1
  refine ⟨⟨le_trans (Real.exp_le_exp.mpr (by linarith)) ha.1, le_trans ha.2 (Real.exp_le_exp.mpr (by linarith))⟩, ?_, ?_⟩
  · calc Real.exp (-(8 * y)) = Real.exp (-(4 * y)) * Real.exp (-(4 * y)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ a * b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ha0
  · calc a * b ≤ Real.exp (2 * y) * Real.exp (2 * y) := mul_le_mul ha.2 hb.2 hb0 (Real.exp_pos _).le
      _ = Real.exp (4 * y) := by
          rw [← Real.exp_add]
          ring_nf

theorem alX_bounds (hk : 1 ≤ D.R.k) (v : PlX X) :
    Real.exp (-(8 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ alX X u u' v ∧
      alX X u u' v ≤ Real.exp (4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  have h := exp_bounds_mul_of_exp_bounds _ _ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) (by positivity)
    (aP_bounds X hk v (Tw u)) (aP_bounds X hk v (Tw u'))
  unfold alX
  split_ifs
  · exact h.1
  · exact h.2

theorem summable_qk (hk2 : 2 ≤ D.R.k) :
    Summable fun v : PlX X => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k with hs
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hk2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have h1 : Summable fun v : PlX X => a (plEquiv X v) := (plEquiv X).summable_iff.2 haS
  refine h1.congr fun v => ?_
  show (Formalism.L2.SG.DataCut.qP (plEquiv X v) ^ s)⁻¹ = _
  have hq : Formalism.L2.SG.DataCut.qP (plEquiv X v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    rw [← absNorm_plEquiv X v]
    exact Formalism.L2.SG.Pf.LocModel.qPl_eq _
  rw [hq, inv_pow]

theorem AlConvC_holds : AlConvC X u u' := by
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hpos : ∀ v, 0 < alX X u u' v := fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds X u u' hk1 v).1
  have hlog : Summable fun v : PlX X => Real.log (alX X u u' v) := by
    refine Summable.of_norm_bounded ((summable_qk X hk2).mul_left 8) fun v => ?_
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨b1, b2⟩ := alX_bounds X u u' hk1 v
    have h1 := Real.log_le_log (Real.exp_pos _) b1
    have h2 := Real.log_le_log (hpos v) b2
    rw [Real.log_exp] at h1 h2
    have hy0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k :=
      pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _
    constructor <;> linarith
  have hlogO : Summable fun v : OrdX X => Real.log (alX X u u' v.1) :=
    hlog.comp_injective (i := fun v : OrdX X => v.1) Subtype.val_injective
  have hposO : ∀ v : OrdX X, 0 < alX X u u' v.1 := fun v => hpos v.1
  refine ⟨Real.multipliable_of_summable_log hposO hlogO, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hposO hlogO]
  exact Real.exp_pos _

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DecompPhaseCOf
section
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def DecompPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ ∧
        Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                  ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
          (X.psiInfU u g * conj (X.psiInfU u' g')) =
          Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem decompPhaseC_of (h3 : LiftDecompC X Y u u' κ) (h6 : PhaseTieC X Y u u' κ) : DecompPhaseC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := h3 R ρ s hrel
  exact ⟨hpt, g, hg, g', hg', hdec, h6 R ρ s hrel g hg g' hg' hdec⟩

theorem normalFormC_of' (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  obtain ⟨hpt, g, hg, g', hg', hdec, hph⟩ := h3 R ρ s hrel
  have hDF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ hpt (h4' R ρ s hrel)
    exact ⟨(h, h'), hh⟩
  have hcS : hDF.choose.1 ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hDF.choose_spec.1
  have hcS' : hDF.choose.2 ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.choose_spec.2.1
  have hcSi : hDF.choose.1⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hcS
  refine ⟨(Formalism.L2.SG.RealObj.InfCut.piIso X u hDF.choose.1 hcS).trans (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg),
    (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').trans (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg'), ?_⟩
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcT : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) :=
    Formalism.L2.SG.PairVal.cTerm_of_atPt vR _ hat (fun w' hw' => h2 _ w' _ hw' hat)
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      (X.piU u hDF.choose.1⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
          (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
        (X.piU u' hDF.choose.2)) := by
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [if_pos hpt, dite_eq_left hDF]
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have e1 : ∀ z, X.piU u hDF.choose.1 (X.piU u hDF.choose.1⁻¹ z) = z := fun z => by
    rw [← ContinuousLinearMap.mul_apply, ← (X.piU_rep u).2.1 _ hcS _ hcSi, mul_inv_cancel, (X.piU_rep u).1,
      ContinuousLinearMap.one_apply]
  have e2 : ∀ y, X.piU u' hDF.choose.2 ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').symm y) = y :=
    fun y => (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').apply_symm_apply y
  unfold chiOO frameVal
  rw [hO, hcT, hV, smul_smul, ← hph]
  have hsc : ∀ a c r : ℂ, a * (r * c) = a * c * r := fun a c r => by ring
  rw [hsc]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, e1, e2]

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1c

variable {D : D7} {X : HidaSetting D}

theorem isIdentity_of_equal_flags (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a)
    (hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus)
    (hrel : Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl) : t.isId := by
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hfix : FixedHyp D t.lam (lf D (X.Fu u)) := hrow.2.1
  have hPD : TermDef.PD D t.lam (lf D (X.Fu u)) u (frq X t.rep) := t.rep.2.2.2.2
  have hlift : IsLift t.lam (frq X t.rep) := hPD.1
  have hadm : IsAdmissible t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) := hPD.2.1
  have hconv : IsFixedConv t.lam (gS D) (frq X t.rep) := hPD.2.2.1
  obtain ⟨c, hcc, he, hz⟩ := id_scal D.host.F D.host.E (hS D) D.R.rS _ (lf D (X.Fu u)).fl (frq X t.rep).fl hT0
    (tie_trace D.sp.cm) hXa hXp hrel
  have hX : (frq X t.rep).fl.X = (lf D (X.Fu u)).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := id_unit D.host.E (hS D) D.R.rS _ t.lam (lf D (X.Fu u)) (frq X t.rep) c (p_starConj D)
    hlift.1 hfix.2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine id_cong D.host.E (hS D) D.R.rS (Tu D u) t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) o hfix.2.1
      hfix.2.2.1.1 hadm (by rw [ho]; exact hz) P ?_ ?_
    · unfold gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := id_over D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := id_over D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := id_root (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := id_lift D _ t.lam (lf D (X.Fu u)) (frq X t.rep) hfix hlift hconv he hz
  have hzo : (lf D (X.Fu u)).fl.z ∈ orth (hS D) (Xsp (lf D (X.Fu u))) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (lf D (X.Fu u)).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have hzz : n (lf D (X.Fu u)).fl.z - (frq X t.rep).fl.z =
      (n (lf D (X.Fu u)).fl.z - (lf D (X.Fu u)).fl.z) - ((frq X t.rep).fl.z - (lf D (X.Fu u)).fl.z) := by abel
  refine ⟨frq X t.rep, TermDef.rep_mk (⟨frq X t.rep, hPD⟩ : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u)),
    n, hn, hne, ?_⟩
  rw [hzz]
  exact Submodule.sub_mem _ h3' hz

theorem one_le_index_of_relevant (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) : 1 ≤ jT t := by
  obtain ⟨hr, hG, hid⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  rw [index_eq_normalForm t hN]
  by_contra hj0
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨k1, -, k3⟩ := Formalism.HermitianLatticeCounting.Final.S6.nFJZero _ _ _ _ _ _ c hN.1
  have hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a := fun a => by
    exact (nf_Xa (frq X t.rep).fl (nf_T_ne D u) a).symm.trans
      ((k1 a).trans (nf_Xa (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u) a))
  have k3' : (frq X t.rep).fl.z - c • (lf D (X.Fu u)).fl.z ∈ (lf D (X.Fu u)).fl.X := by
    rw [← normal_form_z_eq (frq X t.rep).fl (nf_T_ne D u),
      ← normal_form_z_eq (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u),
      ← nf_X (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)]
    exact k3
  have hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus :=
    nf_Xplus_eq _ _ (by rw [nf_X_eq, nf_X_eq]; exact hXa _) c hN.1.1 k3'
  exact hid (isIdentity_of_equal_flags hTg Y t hXa hXp (relRepC D X Y u u t hr hG).1)

end ZsC1c

theorem JPosC_holds : JPosC := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hK _ t ht
  refine one_le_index_of_relevant (fun w => ?_) Y t ht

  have hc : Nat.Coprime (D.mem w).A.T (D.host.g 0 * D.host.g 1) := (hK.2.2.2.2.2.2.1 w).2
  have key : ∀ i : Fin 2, D.host.g i ∣ D.host.g 0 * D.host.g 1 → (D.mem w).A.T ≠ D.host.g i := by
    intro i hd h
    rw [h] at hc
    have h1 : Nat.Coprime (D.host.g i) (D.host.g i) := Nat.Coprime.coprime_dvd_right hd hc
    exact (D.host.g_prime i).one_lt.ne' (by simpa [Nat.coprime_self] using h1)
  exact ⟨key 0 (dvd_mul_right _ _), key 1 (dvd_mul_left _ _)⟩

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def orbR (M : Loc.Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {Z' | ∃ l ρ : Matrix (Fin n) (Fin n) E, Formalism.MainNotions.S.TieN.IntLow M l ∧ Formalism.MainNotions.S.TieN.IntUp M ρ ∧ Z' = l * Z * ρ}

def zAt {m : ℕ} (a : Loc.Pt E (m + 1)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2

def muA (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) :
    Measure ((Loc.IL (m + 1) → E) × (Loc.IN a → E)) :=
  (Measure.pi fun _ : Loc.IL (m + 1) => M.mu).prod (Measure.pi fun _ : Loc.IN a => M.mu)

def IsZO (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) :
    Prop :=
  ∃ xy, (∀ i j, zAt a xy i j ∈ M.R) ∧ O = orbR M (zAt a xy)

def wtZ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) : ℝ :=
  (muA M a {xy | zAt a xy ∈ O}).toReal

def OrbCut (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∀ (k : ℂ) (V : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) → ℂ),
    (∀ O, ¬ IsZO M a O → V O = 0) →
    (∀ O, IsZO M a O → ∃ xy, zAt a xy ∈ O ∧ V O = k * M.bbIntegrand a c xy * (wtZ M a O : ℂ)) →
    HasSum V (k * M.BB a c) ∧ Summable (fun O => ‖V O‖)

end Loc

section Shift

variable {D : Formalism.BasicNotions.D7}

def shM (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0

def ModShift (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ a, modPt δ T T' p w = some a → a.mat = modMat δ T T' p w + shM δ T T' p w

def NAutNe (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  ∀ c : (M p).Cls D.R.rS, (M p).nAut c ≠ 0

end Shift

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurNFCOf
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schurNFC_of (hA : SchurCoreA) (hB : GeomB) : SchurNFC := by
  intro D X u u' Λ Λ' q hdiff hrel hG P hP
  obtain ⟨C, hC, hM⟩ := hB D X u u' Λ Λ' q hrel hG
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  refine hA D.R.k (InfinitePlace X.B.I.F) (X.Vloc u) (X.Vloc u') (X.Vpi u) (X.Vpi u') (X.tensU u) (X.tensU u')
    (X.tensU_inner u) (X.tensU_span u) (X.tensU_inner u') (X.tensU_span u') (X.piLoc u) (X.piLoc u')
    (fun v i => ((D.hcW u (X.pl v)).u i : ℝ)) (fun v i => ((D.hcW u' (X.pl v)).u i : ℝ))
    (fun v => X.piLoc_type u v) (fun v => X.piLoc_type u' v) v₀ (hdiff (X.pl v₀)) C hC P ?_
  intro M hMu
  obtain ⟨h, hh, h1, h2⟩ := hM M hMu
  exact ⟨X.piU u h, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1), h1, h2, hP h hh⟩

end PI.SchurPlaces

theorem schurNFC : Formalism.L2.SG.KappaOffDiagonal.SchurNFC :=
  PI.SchurPlaces.schurNFC_of (PI.SchurPlaces.schurCoreA_of Formalism.MainNotions.BridgeLemma.schur_lemma_unitary_distinct_params)
    (PI.SchurPlaces.Geo.geomB_of PI.SchurPlaces.leviTens PI.SchurPlaces.wfrSpan PI.SchurPlaces.cplxNF)
end
end

