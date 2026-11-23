module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LogbHBNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfAssemble
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfArcChoices
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0032
public import Formalism.SharpRestriction.LevelLetterCocycles.FrameInvPoly
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusStatementOfFontaine
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

def C0 : ℝ := 320

section Num

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem colLeR_mono {PD : PeriodData G Qp K₀ K B BdR} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {x y : ℝ} (h : TruncatedSeriesCountingBounds.ColLeR PD F x) (hxy : x ≤ y) : TruncatedSeriesCountingBounds.ColLeR PD F y := by
  obtain ⟨mm, k, h1, h2, h3⟩ := h
  exact ⟨mm, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg k))⟩

end Num

theorem logb_two_mul_nonneg (l h : ℕ) (hl : 2 ≤ l) : 0 ≤ Real.logb l (2 * (h : ℝ)) := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · apply Real.logb_nonneg
    · exact_mod_cast (show 1 < l by omega)
    · have : (1 : ℝ) ≤ h := by exact_mod_cast hpos
      linarith

theorem sg_le_alt {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (bd : ℝ) (hl : 2 ≤ l) (hbd : 0 ≤ bd) :
    Sg l b w S η size ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 +
      Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + η * bd := by
  unfold Sg
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have h1 : ((w : ℝ) + S + η) / l = ((w : ℝ) + η) / l + (S : ℝ) / l := by ring
  have h2 : (S : ℝ) / l ≤ S := div_le_self (Nat.cast_nonneg S) hl'
  have h3 : 0 ≤ (η : ℝ) * bd := mul_nonneg (Nat.cast_nonneg η) hbd
  linarith

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arith_alt {C N r m e z e' a b' S lg η bd Sgv : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hSg : Sgv ≤ a + b' + S + 1 + lg) (he : e ≤ 55 * Sgv + 13 * S + η * bd)
    (hz : z ≤ 4 * N * m) :
    (N + 1) * r * e + z * e' ≤ C * (N + 1) * r * (a + b' + S + 1 + lg + η * bd) + C * N * m * e' := by
  have hX : e ≤ C * (a + b' + S + 1 + lg + η * bd) := by
    have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
    have h2 : e ≤ 69 * (a + b' + S + 1 + lg + η * bd) := by nlinarith
    have h3 : 0 ≤ a + b' + S + 1 + lg + η * bd := by linarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e ≤ (N + 1) * r * (C * (a + b' + S + 1 + lg + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have hNm : 0 ≤ N * m := mul_nonneg hN hm
  have h5 : z * e' ≤ C * N * m * e' := by
    have : z ≤ C * N * m := by nlinarith
    exact mul_le_mul_of_nonneg_right this he'
  nlinarith

theorem arith_big {C N r m e₀ e' a b' S lg η bd Sgv : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hSg : Sgv ≤ a + b' + S + 1 + lg) (he : e₀ ≤ 160 * Sgv) :
    (N + 1) * r * e₀ + 0 * e₀ ≤ C * (N + 1) * r * (a + b' + S + 1 + lg + η * bd) + C * N * m * e' := by
  have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
  have hX : e₀ ≤ C * (a + b' + S + 1 + lg + η * bd) := by
    have h3 : 0 ≤ a + b' + S + 1 + lg + η * bd := by linarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e₀ ≤ (N + 1) * r * (C * (a + b' + S + 1 + lg + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have h5 : 0 ≤ C * N * m * e' := by
    have : 0 ≤ C := by linarith
    positivity
  nlinarith

theorem arith_one {C N r m e z e' a b' S lg η bd Sgv R : ℝ} (hC : 320 ≤ C) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (he' : 0 ≤ e') (ha : 0 ≤ a) (hb' : 0 ≤ b') (hS : 0 ≤ S) (hlg : 0 ≤ lg) (hη : 0 ≤ η)
    (hbd : 0 ≤ bd) (hR : 1 ≤ R) (hSg : Sgv ≤ a + b' + S + 1 + lg)
    (he : e ≤ 18 * Sgv + 3 * R ^ 2 * (S + 1 + lg) + 1) (hz : z ≤ (R + 1) * N * m) :
    (N + 1) * r * e + z * e' ≤
      C * (N + 1) * r * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) + C * N * m * R ^ 2 * e' := by
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hU : 1 ≤ S + 1 + lg := by linarith
  have hRU : S + 1 + lg ≤ R ^ 2 * (S + 1 + lg) := by nlinarith
  have h1 : 0 ≤ η * bd := mul_nonneg hη hbd
  have hY1 : 1 ≤ a + b' + R ^ 2 * (S + 1 + lg) + η * bd := by nlinarith
  have hX : e ≤ C * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) := by
    have h2 : e ≤ 40 * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd) := by nlinarith
    nlinarith
  have hNr : 0 ≤ (N + 1) * r := by positivity
  have h4 : (N + 1) * r * e ≤ (N + 1) * r * (C * (a + b' + R ^ 2 * (S + 1 + lg) + η * bd)) :=
    mul_le_mul_of_nonneg_left hX hNr
  have hNm : 0 ≤ N * m := mul_nonneg hN hm
  have h5 : z * e' ≤ C * N * m * R ^ 2 * e' := by
    have h6 : R + 1 ≤ C * R ^ 2 := by nlinarith
    have : z ≤ C * N * m * R ^ 2 := by
      calc z ≤ (R + 1) * (N * m) := by linarith
        _ ≤ (C * R ^ 2) * (N * m) := mul_le_mul_of_nonneg_right h6 hNm
        _ = C * N * m * R ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right this he'
  nlinarith

theorem thmB_at (C : ℝ) (hC : C0 ≤ C) {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    TruncatedSeriesCountingBounds.ThmB ((D.loc l).PD K) ((HW l).W K 1 LL hG) C := by
  have hdvr : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  intro hp T₁ T₂ f b w S η m up size Mi hi hS hw hη hS20 hnt
  dsimp only
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi :=
    ⟨hp, hS, hw, hη, hS20, hnt⟩
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := by
    rw [hpl]
    intro h0
    have h1 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp only [ZeroMemClass.coe_zero] at h1
    exact (Nat.cast_ne_zero.2 (show l ≠ 0 from (Fact.out : l.Prime).ne_zero)) h1
  have hgen := hU.a10 l K LL hS.1.1 T₂ hS.2.1.2.1
  have hlift : f.LiftF ((D.loc l).PD K) (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi) :=
    hU.a2.2.2.2.2.2.2.2.1 l K 1 LL hG hS.1 T₁ T₂ f Mi hi hS.2.1 hS.2.2.2.2.2.2
  have hC0 : (320 : ℝ) ≤ C := hC
  rw [hpl]
  have hlg0 : 0 ≤ Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := logb_two_mul_nonneg l _ hl2
  have hSg := sg_le_alt l b w S η size 0 hl2 le_rfl
  rw [mul_zero, add_zero] at hSg
  have ha0 : 0 ≤ (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have hb0 : 0 ≤ ((w : ℝ) + η) / (l : ℝ) := by positivity
  have hbd0 : 0 ≤ (if TruncatedSeriesCountingBounds.Band l b S η size
      (Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) C then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hbdI : bandI l b w S η size C = (if TruncatedSeriesCountingBounds.Band l b S η size
      (Real.logb (l : ℝ) (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) C then (1 : ℝ) else 0) := rfl
  refine ⟨fun hAlt => ?_, fun R hR hup hrun => ?_⟩
  ·
    have hAlt' : Alt b η up size := hAlt
    by_cases hbig : (∃ i, TruncatedSeriesCountingBounds.Thick b η size i) ∧ (b : ℝ) / 4 < 40 * Sg l b w S η size
    · obtain ⟨e₀, he₀, hL₀⟩ := exists_liftF_le_sg_of_thick D HW F Cm hU l K LL hG hK T₁ T₂ f b w S η m up size Mi hi hB
        hAlt' hbig.1 hbig.2
      have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e₀ e₀ hgen ∅ (by simp)
        (fun c hc => Submodule.mem_sup_left (hL₀ c hc)) hL₀
      refine colLeR_mono hc ?_
      have := arith_big (N := (Module.finrank ℚ_[l] ↥(K0 K) : ℝ)) (m := (m : ℝ)) (e' := ((TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi : ℕ) : ℝ))
        hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V)) (Nat.cast_nonneg m)
        (Nat.cast_nonneg _) ha0 hb0 (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hSg he₀
      rw [Finset.card_empty, Nat.cast_zero]
      push_cast at this ⊢
      linarith
    · have hsm : (¬ ∃ i, TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg l b w S η size ≤ (b : ℝ) / 4 := by
        by_cases ht : ∃ i, TruncatedSeriesCountingBounds.Thick b η size i
        · right; exact not_lt.mp fun h' => hbig ⟨ht, h'⟩
        · left; exact ht
      obtain ⟨e, Z, he, hZc, hZ, hZe⟩ := sum_alt D HW F Cm hU hJ l K LL hG hK T₁ T₂ f b w S η m up
        size Mi hi hB hAlt' C (by linarith) hsm
      have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e _ hgen Z hZ hZe hlift
      refine colLeR_mono hc ?_
      rw [hbdI] at he
      have hz : (Z.card : ℝ) ≤ 4 * (Module.finrank ℚ_[l] ↥(K0 K) : ℝ) * m := by exact_mod_cast hZc
      have := arith_alt hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V))
        (Nat.cast_nonneg m) (Nat.cast_nonneg (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi)) ha0 hb0
        (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hSg he hz
      push_cast at this ⊢
      linarith
  ·
    have hOne : One b η R up size := ⟨hup, hrun⟩
    obtain ⟨e, Z, he, hZc, hZ, hZe⟩ := sum_one D HW F Cm hU hJ l K LL hG hK T₁ T₂ f b w S η m up size
      Mi hi hB R hR hOne
    have hc := colLeR_of_exponent ((D.loc l).PD K) hp0 f _ e _ hgen Z hZ hZe hlift
    refine colLeR_mono hc ?_
    have hz : (Z.card : ℝ) ≤ ((R : ℝ) + 1) * (Module.finrank ℚ_[l] ↥(K0 K) : ℝ) * m := by
      exact_mod_cast hZc
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have := arith_one hC0 (Nat.cast_nonneg _) (Nat.cast_nonneg (Module.finrank ↥LL.1 T₂.V))
      (Nat.cast_nonneg m) (Nat.cast_nonneg (TruncatedSeriesCountingBounds.eLift ((HW l).W K 1 LL hG) T₁ Mi hi)) ha0 hb0
      (Nat.cast_nonneg S) hlg0 (Nat.cast_nonneg η) hbd0 hR1 hSg he hz
    push_cast at this ⊢
    linarith

theorem frobenius_statement_of_inputs (C : ℝ) (hC : C0 ≤ C) {CR CA CB CK : ℝ}
    (p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F) (p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F) (p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK) (a5 : ArcLiftingSetup.adm5 D HW F)
    (sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F) (kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F)
    (kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F) (a9 : ArcLiftingSetup.adm9 D) (a10 : ArcLiftingSetup.adm10 D)
    (a11 : ArcLiftingSetup.adm11 D HW F) (a12 : ArcLiftingSetup.adm12 D HW F Cm) (a13 : ArcLiftingSetup.adm13 D HW F Cm)
    (a14 : ArcLiftingSetup.adm14 D HW F Cm) (a15 : ArcLiftingSetup.adm15 D) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    ArcLiftingSetup.aux₃ D HW F C := by
  intro l _ K LL hG hKur _ _ h11
  have hl : 11 ≤ l := (D.loc l).PD_p K ▸ h11
  exact thmB_at D HW F Cm C hC ⟨p2, p3, p4, p5, p9, a2, a5, sP, kLev, kMod, a9, a10, a11, a12, a13, a14, a15⟩ ⟨a22, a23, c4⟩ l K LL hG
    ⟨hKur, by omega, hG⟩ h11

theorem stmt_holds (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F)
    (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) (C : ℝ) (hC : C0 ≤ C)
    (CR CA CB CK Ckap : ℝ) : ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := fun hA =>
  let h := admBoundsB_of_adm hA
  frobenius_statement_of_inputs D HW F Cm C hC h.p2 h.p3 h.p4 h.p5 h.p9 h.a2 h.a5 h.sP h.kLev h.kMod h.a9 h.a10 h.a11 h.a12 h.a13 h.a14 h.a15
    a22 a23 c4

theorem frobenius_statement_of_fontaine (C CR CA CB CK Ckap : ℝ) (hC : (320 : ℝ) ≤ C) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F) :
    ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  stmt_holds D HW F Cm a22 a23 c4 C hC CR CA CB CK Ckap

end Record

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.Realised2Pf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows IsLocalRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem basis_of {I : BaseId W} {T : LocLat G Qp LL O} (hInj : I.Inj) (hFull : I.Full)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T) (i : ZMod n) :
    ∃ (r : ℕ) (e : Fin r → C.V) (b : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i)),
      ∀ k, (b k : C.V) = e k := by
  obtain ⟨r, e, hli, hsp⟩ := free_of hInj hFull hmod C i
  refine ⟨r, e, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp), fun k => ?_⟩
  simp [Module.Basis.span_apply]

theorem matrix_of {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] {N₂ : Submodule (PowerSeries O) V₂} {r₁ r₂ : ℕ} (f : V₁ → V₂)
    (e₁ : Fin r₁ → V₁) (e₂ : Fin r₂ → V₂) (b₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥N₂)
    (hb₂ : ∀ k, (b₂ k : V₂) = e₂ k) (hf : ∀ k, f (e₁ k) ∈ N₂) :
    ∃ P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O), ∀ k, ∃ a : Fin r₂ → PowerSeries O,
      f (e₁ k) = ∑ l, a l • e₂ l ∧ ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l) := by
  refine ⟨Matrix.toLin' (Matrix.of fun l k => PowerSeries.constantCoeff (b₂.repr ⟨_, hf k⟩ l)),
    fun k => ⟨fun l => b₂.repr ⟨_, hf k⟩ l, ?_, fun l => by simp⟩⟩
  have h := b₂.sum_repr ⟨_, hf k⟩
  have h' := congrArg (fun x : ↥N₂ => (x : V₂)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb₂] at h'
  exact h'.symm

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero LL]
  [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]

theorem realised2_pf (Lb : LevB W) (hR : Ring9 W) (e : W.DD W.one) (uZ : ℤ_[PD.p]ˣ)
    (ιZ : ℤ_[PD.p] →+* O)
    (hLevN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hCmp : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (hLevBφ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) • φVB PD (LL := LL) (V := T.V)
            (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (hLevBΓ : ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL)
      (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hLevΓ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ), IsPrimitiveRoot ζ (PD.p ^ j) →
      (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) → ζ' = ζ ^ a →
      ∀ f : LetA O n, W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (hLevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4Lev : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDdR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hHod : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ →
      F.Onto → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hV : ValRing O v) (hK : Function.Bijective (algebraMap K₀ K))
    (hpm : (PD.p : O) ∈ maximalIdeal O) (hrich : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (huZ : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (he : UnitGen W e) (hone : IsCrys PD W.one.ρ) (h5 : 5 ≤ PD.p) : Realised2 hR e := by
  intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hCu hKJ hJ hg hS hT
  obtain ⟨C₁, C₂, C₀, hC, e₀, he₀⟩ :=
    Formalism.MainNotions.N.Ln03.Pf.coordSteps_holds hR hs hP9 hLem3 hDdR he hone hK h5 T₁ T₂ F hc₁ hc₂ hon
  refine ⟨{ C₁ := C₁, C₂ := C₂, C₀ := C₀, h := hC, e₀ := e₀, Ks := KsW W, Δ := DeltaT PD.p },
    { he₀ := he₀, arcs := fun ϖ hϖ c hc => ?_ }⟩
  have hp2 : PD.p ≠ 2 := by omega
  have hp9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := fun T hT =>
    ((hP9 T hT hs hp2).2.2 (unram_of hK)).2
  obtain ⟨r₁, e₁, b₁, hb₁⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₁ hc₁.2.2.2) C₁
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨r₂, e₂, b₂, hb₂⟩ := basis_of (baseIdOf_inj hR) (baseIdOf_full hR) (hp9 T₂ hc₂.2.2.2) C₂
    (c - ((cutsOf hCu).ell c : ZMod n))
  obtain ⟨P, hP⟩ := matrix_of (latHomOf hC).f e₁ e₂ b₂ hb₂ (fun k =>
    (latHomOf hC).map_N _ _ (by rw [← hb₁ k]; exact (b₁ k).2))
  exact Formalism.MainNotions.N.Ln03.Pf.finalArc_holds Lb uZ ιZ hC c _ _ ϖ j _ _ Gp S η ty e₁ e₂ P hLevN hCmp hLevBφ
    hLevBΓ hLevΓ hLevφ hs hP4 hP4Lev hSat hP3 hP9 hP5 hDdR hHod hc₁ hc₂ hon hKJ hV hK hϖ hpm
    (Formalism.MainNotions.N.Ln03.Pf.hn_of hCu hc) hrich (glue2 hR) (cyclotomicFrobeniusPowerSeries_X W)
    (fun s _ ζ hζ => rhoZ_exp c ζ ⟨s + 1, (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 hζ⟩)
    huZ hutie (Formalism.MainNotions.N.Ln03.Pf.teichOnto_holds PD.p) h5 b₁ hb₁ b₂ hb₂ hP
    (Formalism.MainNotions.N.Ln03.Pf.hj_of hCu hc) (Formalism.MainNotions.N.Ln03.Pf.three_g_le_parameter_bound PD.hp.two_le hg)

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TmulMemFilV
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

theorem filV_sep (z : V ⊗[Qp] BdR) (h : ∀ a, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  have hfree : Module.Free Qp V := Module.Free.of_divisionRing Qp V
  let 𝔟 := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟
  have hcoord : ∀ a, ∀ w ∈ FilV PD (LL := LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by
    intro a w hw i
    obtain ⟨u, rfl⟩ := hw
    induction u using TensorProduct.induction_on with
    | zero => simp [(PD.Fil a).zero_mem]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
      simp only [Finsupp.mapRange_apply]
      have : (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR) := by
        rw [algebraMap_smul]
      rw [this]
      exact (PD.Fil a).smul_mem _ y.2
    | add u₁ u₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem h₁ h₂
  have hE : E z = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hcoord a z (h a) i
  exact E.injective (by rw [hE, map_zero])

end Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem fil_step (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

theorem fil_low (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) : x ∈ FilCris PD T.ρ (-(H : ℤ)) := by
  obtain ⟨u₀, hu₀⟩ := filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : -(H : ℤ) ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hx0
      | succ k ih =>
        intro hk
        have := fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega)
          hxD (ih (by push_cast at hk; omega))
        push_cast; rwa [← add_assoc]
    have := key (-(H : ℤ) - u₀).toNat (by omega)
    rwa [show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega] at this

theorem fil_high (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ)) (u : ℤ) (hu : (H : ℤ) < u) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) (hx : x ∈ FilCris PD T.ρ u) : x = 0 := by
  have key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have := fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih
      push_cast; rwa [← add_assoc]
  have hall : ∀ a, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by
    intro a
    by_cases ha : a ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2
    · have := (key (a - u).toNat).2
      rwa [show u + ((a - u).toNat : ℤ) = a by omega] at this
  have h0 := filV_sep (PD := PD) _ hall
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

