module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DenBound
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentBoundLevelIdeal

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenTwoThickLetters
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arc_len_two_thick_letters [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (c : ZMod n)
    (hlen : (arcOf b w S η up size).len c = 2) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
  set s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with hs
  have hlen' : sInf s = 2 := hlen
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    norm_num at hlen'
  have h2 : 2 ∈ s := hlen' ▸ Nat.sInf_mem hne
  have h1 : 1 ∉ s := fun h => by
    have := Nat.sInf_le h
    omega
  constructor
  · by_contra hT
    apply h1
    refine ⟨le_rfl, ?_⟩
    simpa using hT
  · have h22 := h2.2
    convert h22 using 2
    push_cast
    ring

theorem lifts_scale (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : lE W (e + k) * f = lE W e * (lE W k * f) := by
    simp only [lE, pow_add, mul_assoc]
  have hfun : (fun kk => if kk = k₀ then lE W (e + k) * f else 0) =
      (fun kk => if kk = k₀ then lE W e * (lE W k * f) else 0) := funext fun kk => by rw [he]
  rw [hfun]
  exact h5

theorem lE_alg (W : LocWach PD LL O v n) (k : ℕ) :
    lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp only [lE, lA, map_pow, map_natCast]

theorem algO (W : LocWach PD LL O v n) (x : O) :
    algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) := IsScalarTower.algebraMap_apply O (LetA O n) W.EE x

theorem den_step [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (Br : Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge W) (c : ZMod n) (y Bq κ : ℕ)
    (hy : 1 ≤ y) (hBq : 1 ≤ Bq) (f : W.EE) (x : O)
    (hf : InFr W c 1 (ps W 1 ^ y) f)
    (hx : InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ (de : ℕ) (x' : O), de ≤ ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ ∧
      (PD.p * y < Bq → de = 0) ∧
      InFr W c 1 (ps W 1 ^ y) (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') ∧
      InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
        (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
  haveI := Fact.mk PD.hp
  set P := Br.P
  have hp0 : P.p 0 = X := rfl
  have hps : ∀ s k, ps W s ^ k = Br.cst (P.p s ^ k) := by
    intro s k; rw [Br.cst_pow, Br.ps_eq]
  have h1 : (1 : LetA O n) = Br.cst 1 := Br.cst_one.symm
  rw [hps, h1] at hf
  rw [hps, hps, hp0] at hx
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf hx
  obtain ⟨hd1, hd2⟩ := den_bound P y Bq κ hy hBq x U₁ U₂ hU
  set D := ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ with hD
  set de : ℕ := if PD.p * y < Bq then 0 else min D κ with hde
  have hxd : ((PD.p : ℕ) : O) ^ (κ - de) ∣ x := by
    rw [hde]; split_ifs with hlt
    · simpa using hd2 hlt
    · have : κ - min D κ = κ - D := by omega
      rw [this]; exact hd1
  have hdeκ : de ≤ κ := by rw [hde]; split_ifs <;> omega
  obtain ⟨x', hx'⟩ := hxd
  refine ⟨de, x', ?_, ?_, ?_⟩
  · rw [hde]; split_ifs <;> omega
  · intro hlt; rw [hde, if_pos hlt]
  obtain ⟨u₁, hu₁, hfu⟩ := hf
  obtain ⟨F₁, hF₁⟩ := Br.range u₁ hu₁ c
  set G : PowerSeries O := C ((PD.p : ℕ) : O) ^ de * F₁ - P.p 1 ^ y * C x' with hG
  have hletu : (letE c : LetA O n) * u₁ = letE c * Br.cst F₁ := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [letE, hF₁, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst]
    · simp [letE, Pi.single_apply, hi]
  have e1 : (letE c : LetA O n) * Br.cst G =
      lA W ^ de * (letE c * Br.cst 1 * u₁) - Br.cst (P.p 1 ^ y) * (letE c * algebraMap O (LetA O n) x') := by
    rw [Br.cst_one, mul_one, hletu, hG, Br.lA_eq, ← Br.cst_pow, ← Br.cst_C]
    funext i
    simp only [Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, Pi.mul_apply, Pi.sub_apply, map_sub, map_mul, map_pow]
    ring
  have hkey : algebraMap (LetA O n) W.EE (Br.cst (P.p 1 ^ y)) *
      (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') =
      algebraMap (LetA O n) W.EE (letE c * Br.cst G) := by
    rw [algO, e1]
    simp only [map_sub, map_mul] at hfu ⊢
    rw [← lE_alg]
    linear_combination (lE W de) * hfu
  refine ⟨⟨Br.cst G, Br.cst_mem G, ?_⟩, ?_⟩
  · rw [hps 1 y, hkey, mul_one]
  have hscale : lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x =
      lE W (κ - de) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
    have hj' : lE W κ = lE W (κ - de) * lE W de := by
      unfold lE; rw [← pow_add, Nat.sub_add_cancel hdeκ]
    rw [hx', map_mul, map_pow, map_natCast, hj']
    unfold lE
    ring
  obtain ⟨u₂, hu₂, hxu⟩ := hx
  have hxu2 : algebraMap (LetA O n) W.EE (lA W ^ (κ - de) * (letE c * Br.cst G)) =
      algebraMap (LetA O n) W.EE (letE c * Br.cst (X ^ Bq) * u₂) := by
    rw [map_mul, ← hkey, ← lE_alg, ← hxu, hscale]
    ring
  have hxc := congrFun (W.EE_inj hxu2) c
  obtain ⟨F₂, hF₂⟩ := Br.range u₂ hu₂ c
  have hιeq : Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) = Br.ι (X ^ Bq * F₂) := by
    have e2 : (lA W ^ (κ - de) * (letE c * Br.cst G) : LetA O n) c = Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) := by
      rw [Br.lA_eq, ← Br.cst_pow]
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, map_mul]
    have e3 : (letE c * Br.cst (X ^ Bq) * u₂ : LetA O n) c = Br.ι (X ^ Bq * F₂) := by
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, hF₂, map_mul]
    rw [← e2, ← e3, hxc]
  have hGB := Br.inj hιeq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  have hmem : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) ∈
      Ideal.span {(X : O⟦X⟧) ^ Bq} := by
    have : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) = X ^ Bq * F₂ := by
      rw [← hGB, hu]
      simp only [map_mul, map_pow, mul_pow, ← pow_mul]
      ring
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hmem2 := Cont.mem_of_pow_mul_mem hϖ (ContPA.dist_X_pow (O := O) Bq).1 _ _ hmem
  obtain ⟨U', hU'⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hone : (C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧) * C ((↑u : O) ^ (κ - de)) = 1 := by
    rw [← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  have hG2 : G = X ^ Bq * (C ((↑(u⁻¹) : O) ^ (κ - de)) * U') := by
    linear_combination (-G) * hone + (-(C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧)) * hU'
  refine ⟨Br.cst (C ((↑(u⁻¹) : O) ^ (κ - de)) * U'), Br.cst_mem _, ?_⟩
  rw [hps 1 y, hps 0 Bq, hp0, hkey, hG2, Br.cst_mul, mul_assoc]

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourDenominator
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_four_denominator [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (κ : ℕ) (x : O)
    (hx : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ s : ℕ, (s : ℝ) ≤ max 1 ((size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p + 16 / 5 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) + 1 ∧
      ((PD.p : ℕ) : O) ^ κ ∣ ((PD.p : ℕ) : O) ^ s * x := by
  obtain ⟨hp11, hset, h20w, h20η, -, -⟩ := hB
  obtain ⟨-, -, hη, -, -, hsz, -⟩ := hset
  have hl3 : (arcOf b w S η up size).len c = 3 := hlen
  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : ({d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} : Set ℕ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Nat.sInf_empty] at hlen'
    omega
  have hT2 : ¬ TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have hm := Nat.sInf_mem hne
    rw [hlen'] at hm
    have hm' : 1 ≤ 3 ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - ((3 : ℕ) : ZMod n) + 1) := hm
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rw [e] at hm'
    exact hm'.2
  have hT0 : TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra hnt
    have hmem : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨le_refl 1, ?_⟩
      simpa using hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hT1 : TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hnt
    have hmem : (2 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨by norm_num, ?_⟩
      have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
      rw [e]
      exact hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hu1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    rw [show c - 2 + 1 = c - 1 by ring, hU] at h
    simpa using h
  have hu0 : up c = true := by
    have h := (halt (c - 1)).1
    rw [sub_add_cancel, hu1] at h
    simpa using h
  have hh : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c, hT0⟩]
  obtain ⟨s₁, hs1, hs1le, hsB, hnot⟩ := exists_s1_bound_choice PD.p b w S η (size c) (size (c - 1))
    (size (c - 2)) hp11 (Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (by unfold Formalism.MainNotions.N.Ln17.Sg; rw [hh]) hsm h20w h20η
    (by have := hη (c - 2); omega) (hsz (c - 2) hT2) hT1.1 hT0.2
  refine ⟨s₁, hs1le, ?_⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₂ hW₂.1 hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hps : ∀ s, ps W s = (fun _ => Br.ι (Br.P.p s) : LetA O n) := by
    intro s
    induction s with
    | zero =>
      funext i
      simp [ps, qA, LocWach.π₀, lA, PhiData.p, Br.ι_X]
    | succ s ih =>
      have e : ps W (s + 1) = W.φA (ps W s) := by
        simp only [ps, pow_succ', AlgHom.mul_apply]
      rw [e, ih]
      funext i
      simp [LocWach.φA, letφ, PhiData.p, Function.iterate_succ_apply', Br.ι_φ]
  have hpsc : ∀ s, Br.ι (Br.P.p s) = ps W s c := fun s => by rw [hps s]
  have hX : Br.ι PowerSeries.X = ps W 0 c := hpsc 0
  have hCι : ∀ a : O, Br.ι (PowerSeries.C a) = PowerSeries.C a := fun a => Br.ι.commutes a
  have hN : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hl3]
    simp [Finset.prod_range_succ, arcOf, hu0, hu1, hU]
  have hf1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c) f := by
    unfold InFF at hf
    exact hf.1
  obtain ⟨u₀, hu₀, h0⟩ := hf1
  obtain ⟨u, hu, h1⟩ := hx
  have key : algebraMap (LetA O n) W.EE (letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u)) = 0 := by
    have hx' : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) :=
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE x
    have hl : lE W κ = ((PD.p : ℕ) : W.EE) ^ κ := rfl
    rw [hx', hl] at h1
    simp only [map_sub, map_mul, map_pow, map_natCast, map_one] at h0 h1 ⊢
    linear_combination h1 - ((PD.p : ℕ) : W.EE) ^ κ * h0
  have key2 : letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u) = 0 := W.EE_inj (key.trans (map_zero _).symm)
  have key3 := congrFun key2 c
  rw [hN] at key3
  simp only [letE, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply,
    Pi.single_eq_same, one_mul, Pi.algebraMap_apply] at key3
  have hAC : algebraMap O (PowerSeries O) x = PowerSeries.C x := rfl
  try rw [hAC] at key3
  haveI : Fact (Nat.Prime PD.p) := ⟨PD.hp⟩
  obtain ⟨U₁, hU₁⟩ := Br.range u₀ hu₀ c
  obtain ⟨U₂, hU₂⟩ := Br.range u hu c
  refine den_of_rel Br.P hϖ (D := Br.P.p 2 ^ size (c - 2) * PowerSeries.X ^ size c)
    (U₁ := U₁) (U₂ := U₂) (B := size (c - 1) + S) (s₁ := s₁) ?_ ?_
  · apply Br.inj
    simp only [map_mul, map_sub, map_pow, map_one, mul_one, hCι, map_natCast]
    rw [hX, hpsc 2, hpsc 1, ← hU₁, ← hU₂]
    linear_combination -key3
  · intro hmem
    exact hnot (content_bound_level_ideal (P := Br.P) hϖ (size (c - 2)) (size c) (size (c - 1) + S) s₁
      (by have := hη (c - 2); omega) hs1 hsB hmem)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.StepIi
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem step_ii (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T₁ T₂ : LocLat G Qp LL O}
    (hc₁ : IsCrys PD T₁.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (F : LatHom T₁.L T₂.L) (i : ZMod n) (Ai ri : ℕ)
    (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (P : O[X])
    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P y))
    {x : W.DD T₂} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x) : InImg W F i (aeval dop₂ P x) := by
  have hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧ IsUnit (algebraMap (LetA O n) W.EE (qA W)) ∧
      IsUnit ((W.DelF.card : ℕ) : O) := by
    exact lemG_units W hcase hP9 hc₁ hO hOv hinj
  obtain ⟨hπ, hq, -⟩ := hU
  have hz : InImg W F i (qA W ^ (Ai + ri) • x) := by
    exact q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hx
  obtain ⟨z, hzN, hzx⟩ := hz
  set N := Ai + ri
  set e : W.EE := (↑hq.unit⁻¹ : W.EE) ^ N with he
  have key : algebraMap (LetA O n) W.EE (qA W ^ N) * e = 1 := by
    rw [he, map_pow, ← mul_pow, hq.mul_val_inv, one_pow]
  have hqy : qA W ^ N • (e • z) = z := by
    rw [← algebraMap_smul W.EE (qA W ^ N), smul_smul, key, one_smul]
  have hFy : W.map F (e • z) = x := by
    rw [LinearMap.map_smul, hzx, ← algebraMap_smul W.EE (qA W ^ N) x, smul_smul, mul_comm, key, one_smul]
  have hy : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P (e • z)) := by
    apply hCONS
    rw [hqy]
    exact hzN
  exact ⟨aeval dop₁ P (e • z), hy, by rw [aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂, hFy]⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

