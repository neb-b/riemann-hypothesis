module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0015
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Local

variable {D : Formalism.BasicNotions.D7}

abbrev MatP (D : Formalism.BasicNotions.D7) (p : PlF D) : Type :=
  Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)

def kkOrb (p : PlF D) (Y : MatP D p) : Set (MatP D p) :=
  {Y' | ∃ l ρ : MatP D p, Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧ Y' = l * Y * ρ}

def IntP (p : PlF D) (Y : MatP D p) : Prop := ∀ a b, Y a b ∈ (M p).R

def InOrbP (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Prop :=
  ∃ w₀, modPt δ T T' p w = some w₀ ∧
    ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2

def phL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℂ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 then
      dfac M δ T T' p w *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def wtL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℝ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y}).toReal

def thL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) (Y + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0)

def nIsoO (p : PlF D) (o o' : Option ((M p).Cls D.R.rS)) : ℕ :=
  match o, o' with
  | some c, some c' => (M p).nIso (Quotient.out c) (Quotient.out c')
  | _, _ => 0

def IsLCls (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : Prop :=
  ∃ Y, IntP M p Y ∧ InOrbP δ T T' p w Y ∧ O = kkOrb M p Y

def repL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : MatP D p :=
  if h : IsLCls M δ T T' p w O then h.choose else 0

def fL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ) *
      (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ)
  else 0

def gL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def hL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def kL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ) else 0

def eL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then 1 else 0

def sgnP (p : PlF D) : MatP D p := Matrix.diagonal fun b : Fin (D.R.rS + 1) => (-1) ^ (D.R.rS - b.val)

def x0L (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Set (MatP D p) := kkOrb M p (modMat δ T T' p w)

end Local

section Glob

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def nrep (γ : TermDef.Term D u u' F0 what₂) :
    Option (Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D) :=
  if h : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 then some h.choose else none

def zT (γ : TermDef.Term D u u' F0 what₂) : PairVal.MatR D :=
  match nrep γ with
  | some x => ZhatL (lf D F0) x.2.1
  | none => 0

def ptT (γ : TermDef.Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  match nrep γ with
  | some x => x.1
  | none => PairVal.junkPoint D u u'

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def thT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ))

def locT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p)

def dnT (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (γ : TermDef.Term D u u' F0 what₂) : ℝ :=
  ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') (zT γ) p

end Glob

end Formalism.L2.SG.LsDatumB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.NormalInvariants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PG {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) : ℝ := ∏ w : InfinitePlace D.host.E, w (GPt TT γ)

def NmlInv : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₁ →
            PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NormCount : Prop :=
  ∀ (D : D7) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m : D.host.E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset D.host.E, (∀ x ∈ S, x ∈ J ∧ x * star x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤ 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

private theorem eight_mul_sq_le_eightyOne_pow (f : ℕ) : 8 * f ^ 2 ≤ 81 ^ f := by
  induction f with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    · have h1 : 1 ≤ n := h
      rw [pow_succ 81 n]
      nlinarith [ih, h1]

theorem nat_bound (f : ℕ) : (64 : ℝ) * (f : ℝ) ^ 4 ≤ 6561 ^ f := by
  have h' : ((8 * f ^ 2 : ℕ) : ℝ) ≤ ((81 ^ f : ℕ) : ℝ) := by exact_mod_cast eight_mul_sq_le_eightyOne_pow f
  push_cast at h'
  have e : (6561 : ℝ) ^ f = (81 : ℝ) ^ f * (81 : ℝ) ^ f := by
    rw [← mul_pow]
    norm_num
  rw [e]
  calc (64 : ℝ) * (f : ℝ) ^ 4 = (8 * (f : ℝ) ^ 2) * (8 * (f : ℝ) ^ 2) := by ring
    _ ≤ (81 : ℝ) ^ f * (81 : ℝ) ^ f := mul_le_mul h' h' (by positivity) (by positivity)

theorem rd_one_le (D : D7) : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
    exact_mod_cast h'
  · positivity

theorem ngPt_eq {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) :
    NGPt D.host.rdE TT γ = ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹ * PG TT γ := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have hcard : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
    have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    omega
  unfold NGPt PG
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, inv_pow]

theorem rd_cancel (D : D7) :
    D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6 = 1 := by
  have h0 : D.host.rdE ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (rd_one_le D))
  rw [inv_pow, ← pow_mul, ← pow_mul]
  rw [show 12 * D.R.rS * (D.R.rS + 1) * D.R.f = 2 * D.R.rS * (D.R.rS + 1) * (D.R.f * 6) by ring]
  exact mul_inv_cancel₀ (pow_ne_zero _ h0)

theorem count_bound (f : ℕ) (T T' P c1 c2 : ℝ) (hT1 : 3 ≤ T) (hT2 : 3 ≤ T') (hP1 : 1 ≤ P)
    (hc1 : c1 ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) (hc2 : c2 ≤ 8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2))
    (_h1 : 0 ≤ c1) (h2 : 0 ≤ c2) :
    c1 * c2 ≤ (T * T') ^ (6 * f) * P ^ 6 := by
  have hf := nat_bound f
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hT0' : (0 : ℝ) ≤ T' := by linarith
  have hTT0 : (0 : ℝ) ≤ T * T' := mul_nonneg hT0 hT0'
  have hTT : (9 : ℝ) ≤ T * T' := by nlinarith
  have h4 : (6561 : ℝ) ≤ (T * T') ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hTT 4
    norm_num at this
    exact this
  have h9 : (6561 : ℝ) ^ f ≤ (T * T') ^ (4 * f) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) h4 f
  have hP : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hB : (0 : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hT0 _) (sq_nonneg _))
  have hA : c1 * c2 ≤ (8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) * (8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2)) :=
    mul_le_mul hc1 hc2 h2 hB
  calc c1 * c2 ≤ _ := hA
    _ = (64 * (f : ℝ) ^ 4) * ((T * T') ^ (2 * f) * P ^ 4) := by
        rw [mul_pow]
        ring
    _ ≤ (T * T') ^ (4 * f) * ((T * T') ^ (2 * f) * P ^ 6) :=
        mul_le_mul (hf.trans h9) (mul_le_mul_of_nonneg_left hP (pow_nonneg hTT0 _))
          (mul_nonneg (pow_nonneg hTT0 _) (by positivity)) (pow_nonneg hTT0 _)
    _ = (T * T') ^ (6 * f) * P ^ 6 := by ring

theorem stepNormals_of (hA : NmlInv) (hB : NormCount) (hO : StepNormOne) : StepNormals := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u u' hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u' : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  have hIsPt : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ := ⟨cl, ν0, hS ν0 hν0⟩
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u u' hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith

  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hT1 ⊢
  generalize ((Tu D u' : ℕ) : ℝ) = T' at hN' hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T' P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

def NormCountG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset E, (∀ x ∈ S, x ∈ J ∧ x * NumberField.IsCMField.complexConj E x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
        2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

theorem normCount_of (h : NormCountG) : NormCount := by
  intro D J m hJ hm S hS
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have h1 := h D.host.E J m hJ hm S (fun x hx => ⟨(hS x hx).1, (hS x hx).2⟩)
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by rw [hfin]; push_cast; ring
  rw [hf] at h1
  calc (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2
      ≤ 2 * (2 * (D.R.f : ℝ)) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := h1
    _ = 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by ring

end Formalism.L2.SG.NGCut.NormalInvariants
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
section
noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

variable {D : D7}

theorem gPoint_eq_gval {T T' : ℕ} (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (Formalism.MainNotions.S.ZhatOM (ZhatL F F')) w) :
    Gpt T T' w = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hL' : IsLo L := ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩
  have hU' : IsUp U := ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩
  have hS : Formalism.MainNotions.S.ZhatOM (ZhatL F F') = ZhatL F F' * Sg D.host.E D.R.rS := by
    ext a b
    simp [Formalism.MainNotions.S.ZhatOM, Sg, mul_diagonal, mul_comm]
  have key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE (ZhatL F F') l * epsL (D := D) D.R.rS l hl = Dmin w l := by
    intro l hl
    rw [← leadMinor_Sg, ← hS, hZ, leadMinor_LMU hL' hU', dmin_eq']
  have n1 := norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)
  have n2 := norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)
  simp only [Gval, Gflag, Gpt, conjF_star]
  unfold Formalism.MainNotions.S.Dl
  rw [n1, n2]

theorem atPt_totPos {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (t : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (h : t.atPt w) :
    TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) := by
  obtain ⟨F', ⟨hP, -⟩, hG, hc⟩ := h
  have e := gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D F0) F' w hc
  intro τ
  change 0 < (D.host.emb (D.eTau τ) (Gpt (Tu D u) (Tu D u') w)).re
  rw [e]
  exact (Formalism.MainNotions.LatticeGluingRadicals.b_G_pos (Formalism.MainNotions.LatticeGluingRadicals.p_starConj D) (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) (lf D F0) F' rfl
    hP.1.2 hG (Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) _) _).1

end Pos

section Use

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem eligTotPos_holds : EligTotPos X Y u u' := fun t w _ h => atPt_totPos t w h

theorem kapN_pos : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _
  have hg : 0 < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  exact mul_pos (pow_pos hr _) (inv_pos.mpr (pow_pos hg _))

theorem weightBound_holds {nc : ℝ} (hnc : 0 < nc) : Formalism.L2.SG.RowsAbsX.WeightBound X Y u u' nc := by
  refine ⟨Real.sqrt (Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc)), fun p w hp hreal ht => ?_⟩
  obtain ⟨t, -, hat⟩ := ht
  have hT := atPt_totPos t w hat
  rw [nW_eq X u u' p w hp hreal hT hnc]
  have hK : 0 ≤ Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc) := by
    refine div_nonneg ?_ (mul_pos kapN_pos hnc).le
    unfold Formalism.L2.SG.MassDataConc.ngFac
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hn0 : 0 ≤ n0 nc (D.mem u).A.T (D.mem u').A.T w := by
    unfold n0
    exact mul_nonneg hnc.le (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Real.sqrt_mul hK, Real.sqrt_mul hn0, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

end Use

end Formalism.L2.SG.WConst
end
end

