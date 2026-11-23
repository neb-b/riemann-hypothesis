module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0111
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSFinal
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.ThmSOwn

section Ev

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData

variable (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps)

theorem countOwn_of_rowsPEv (Cg cb Cu cT CT C0 : ℝ) (n0 : ℕ) (A C c cb7 : ℝ) (hC : 0 ≤ C) (hA : 2 * Cg ≤ A)
    (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hR : ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (h30 : CountRowsClassFamily P Fm n0 A C c cb7) : CountOwn Fm Cg cb Cu cT CT C0 c := by
  obtain ⟨xR, HR⟩ := hR
  obtain ⟨-, hcb, h30⟩ := h30
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (max (Fm.x1 + 1) x4) xR, fun x hx i hH => ?_⟩
  have hxa := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hxa
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) hxa)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hh : AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT := ⟨hH.2.1, hH.1, hH.2.2⟩
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  obtain ⟨X, hX⟩ := HR x (le_trans (le_max_right _ _) hx) hx1 i
  refine admissibility_ten_of_rows_class P (Fm.L x i) X hX n0 A C cb7 c (h30 x i)
    (count_parameters_of_hyp (Fm.L x i) C0 _ _ Cg cb Cu cT CT n0 A C cb7 hC hcb hA ?_ hCl2 hCl3 ?_ hh)
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

end Ev

theorem kExpTied_holds : KExpTied :=
  kExpTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.InHHC_holds Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.OOFundIndepC_holds Formalism.L2.SG.Closed.AmpWellDefC_holds
    Formalism.L2.SG.Closed.AbsConvC_outright Formalism.L2.SG.Closed.KExpansionC_holds

theorem absConvTied_holds : Formalism.L2.SG.RowsConc.AbsConvTied :=
  Formalism.L2.SG.RowsConc.absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright

variable (C0 : ℝ)



end Formalism.L2.SG.ThmSOwn
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc Formalism.FourierDecayAlt

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RowsPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TypeP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def PairsDegCutP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

def KppDiagP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
      Formalism.L2.SG.RowsOther.KppDiag (Y.tO u u) (duC X Y u) D.R.k D.R.f

def RowNGP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C4 : ℝ, 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y → (Y.tO u u').AbsConv →
      (Y.tO u u').RowNG (epsNG D large₂ C4) (ddC X Y u u')

def RowMainEqP : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowMain (gamB D large₂ CB) (ddC X Y u u)

def DiagLP : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∀ CG : ℝ, max CB C4 + 1 ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      (Y.tO u u).RowBig (epsL D) (ddC X Y u u) → (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u) →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

section Asm

variable {D : D7} {X : HidaSetting D}

theorem pairs_degree_bound (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC)
    (hIV : IrrVecC) (hJP : JPosC) (hTy : TypeP) (hDl : DelC) (hCo : CosetsC) (hDim : DimFormC) (hPg : PgLeC) :
    PairsDegCutP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, hT⟩ := hTy Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ct₀, hT2⟩ := hT (Cp + 4) le_rfl
  obtain ⟨Cd₀, hD2⟩ := hDl Cg cb Cw cT CT C0 CH hCH
  set C := max (max Ct₀ Cd₀) 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  obtain ⟨C'₁, Cl₁, hT3⟩ := hT2 C (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨C'₂, Cl₂, hD3⟩ := hD2 C (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨Cc, hCc, C'₃, Cl₃, hC3⟩ := hCo Cg cb Cw cT CT C0 CH hCH
  obtain ⟨C'₄, Cl₄, hP4⟩ := hPg Cg cb Cw cT CT C0
  refine ⟨max (max C'₁ C'₂) (max C'₃ C'₄), max (max (max Cl₁ Cl₂) (max Cl₃ Cl₄)) (k2C0 (k2Cf C Ch Cc)),
    fun C' Cl h1 h2 D large₂ X Y u hTs hH hTie => ?_⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a3 : C'₃ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) h2
  have b3 : Cl₃ ≤ Cl := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have tAt := hT3 C' Cl a1 b1 D large₂ X Y u hTs hH hTie
  have dAt := hD3 C' Cl a2 b2 D large₂ X Y u hH hTie
  have cAt := hC3 C' Cl a3 b3 D large₂ X Y u hH hTie
  have pg := hP4 C' Cl a4 b4 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := hDim D X Y u hTie
  have hJ := hJP Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := hFE D X Y u u
  have hI := hOI D X Y u u (hFold D X Y u hL hWd) (hFold D X Y u hL hWd) hF
  have hIrr := hIV D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ Formalism.L2.SG.RowsConc.PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ Formalism.L2.SG.RowsConc.duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤
      Formalism.L2.SG.RowsConc.duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc Formalism.L2.SG.RowsConc.PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ Formalism.L2.SG.RowsConc.PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ Formalism.L2.SG.RowsConc.PgC Y *
        (Formalism.L2.SG.RowsConc.duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (Formalism.L2.SG.RowsConc.duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * Formalism.L2.SG.RowsConc.duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end Asm

theorem diagonalBound_pos_of_degreeCutoff (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily)
    (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound) (hC : CorankPosC) (hN : NormExpDegC)
    (hc : PairsDegCutP) : KppDiagP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 hcb hcT
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hTs hH hT ha => ?_⟩
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) hP hE hS hSub (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg (h C' Cl h1 h2 D large₂ X Y u hTs hH hT))

theorem kernel_diagonal_positive (hTy : TypeP) : KppDiagP :=
  diagonalBound_pos_of_degreeCutoff Formalism.FourierDecayAlt.P.price_of_index Formalism.FourierDecayAlt.P.equal_index
    Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.L2.SG.Closed.TermsGGBound_holds
    Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds Formalism.L2.SG.Pf.normExpDegC_holds
    (pairs_degree_bound Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Pf.fundExistsC_holds
      Formalism.L2.SG.Closed.OOIntAllC_outright IrrVecC_holds JPosC_holds hTy DelC_holds cosetsC_holds kappa_off_diagonal_dim_form_C
      (PgLe.pgLeC_of Formalism.L2.SG.Pf.splitPrimeLoc_holds Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds))

theorem diagLP_of_rows (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound)
    (hNS : NormExpSatTied) (hC : CorankPosC) (hId : IdOneC) (hNG : RowNGP) (hM : RowMainEqP)
    (hNum : DiagNumC) : DiagLP := by
  intro Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨CB, hCB, C'₁, Cl₁, hM'⟩ := hM Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨C4, hC4, C'₂, Cl₂, hNG'⟩ := hNG Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C'₄, Cl₄, hNum'⟩ := hNum Cg cb Cw cT CT C0 A CB C4 hCB hC4
  refine ⟨CB, C4, hCB, hC4, fun CG hCG => ⟨max (max C'₁ C'₂) C'₄, max (max Cl₁ Cl₂) Cl₄,
    fun C' Cl h1 h2 D large₂ X Y u hTs hH hK2 hT ha hG r1 r2 => ?_⟩⟩
  have a1 : C'₁ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have a2 : C'₂ ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have a4 : C'₄ ≤ C' := le_trans (le_max_right _ _) h1
  have b1 : Cl₁ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  have b2 : Cl₂ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
  have b4 : Cl₄ ≤ Cl := le_trans (le_max_right _ _) h2
  have h0 : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 := hH.1
  have hs : Formalism.MainNotions.S.Cnt.Stand D u u := hH.2.1
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdd := dd_nonneg hT u u
  have r3 := hM' C' Cl a1 b1 D large₂ X Y u hTs hH hT ha
  have r4 := hNG' C' Cl a2 b2 D large₂ X Y u u hTs h0 hs hT ha
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hK2 Y.TR v)
  have hD := Formalism.L2.SG.RowsOther.diag_of_abstract (Y.tO u u) hA hP hE hS hSub (oneC X Y u) (PgC Y)
    (gamB D large₂ CB) (epsL D) (epsNG D large₂ C4) (ddC X Y u u) hPg hdd ha (hNS D X Y u u hT) hGB
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hId D X Y u hT)
    r1 r2 r3 r4
  unfold Formalism.L2.SG.RowsOther.DiagRow at hD ⊢
  exact hD.trans (mul_le_mul_of_nonneg_right (hNum' C' Cl a4 b4 D large₂ X Y u hH hK2 hT (hG ▸ hCG)) hdd)

theorem diagonal_positive_final (hNG : RowNGP) (hM : RowMainEqP) : DiagLP :=
  diagLP_of_rows Formalism.FourierDecayAlt.P.pair_bound_abstract Formalism.FourierDecayAlt.P.price_of_index Formalism.FourierDecayAlt.P.equal_index
    Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt Formalism.L2.SG.Closed.TermsGGBound_holds
    normExpSatTied_holds Formalism.L2.SG.KappaOffDiagonal.corankPosC_holds idOneC_holds hNG hM Formalism.L2.SG.Pf.diagNumC_holds

end Formalism.L2.SG.RowsPos
end
end

