module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsDistPow
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsUnitPi0InEE

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenLeOneOfNoThick
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem ro_le_arc_len : ∀ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n),
    Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ≤ A.len c := by
  intro n A c
  unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem arc_len_le_one_of_no_thick : ∀ {n : ℕ} [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ)
    (h : ¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) (c : ZMod n),
    (arcOf b w S η up size).len c ≤ 1 := by
  intro n _ b w S η up size h c
  unfold arcOf
  dsimp only
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq]
  exact ⟨le_rfl, fun ht => h ⟨_, ht⟩⟩

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeDescent
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

theorem liftsAt_of_scaled_power (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : (fun k' => if k' = k₀ then lE W e * (lE W k * f) else 0) =
      (fun k' => if k' = k₀ then lE W (e + k) * f else 0) := by
    funext k'
    unfold lE
    rw [← mul_assoc, ← pow_add]
  rw [← he]
  exact h5

theorem arc_length_three_descent [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η)) :
    ∃ (t₂ X₂ : O) (f₂ : W.EE),
      (∃ r : ℚ, v (algebraMap O LL t₂) = ((r : ℚ) : WithTop ℚ) ∧
        (r : ℝ) ≤ ((η : ℝ) + 2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) * bandI PD.p b w S η size Cb) ∧
      algebraMap O W.EE t₂ * f = algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂ + f₂ ∧
      InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂ ∧
      ∃ (κ : ℕ) (X₀ : O), InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
        (lE W κ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀) := by
  have hl11 : 11 ≤ PD.p := hB.1
  have hηs : ∀ i, η < size i := hB.2.1.2.2.1

  have hup1 : up (c - 1) = true := by
    have h := (halt (c - 2)).1
    have e : c - 2 + 1 = c - 1 := by ring
    rw [e, hD] at h
    simpa using h
  have hup0 : up c = false := by
    have h := (halt (c - 1)).1
    have e : c - 1 + 1 = c := by ring
    rw [e, hup1] at h
    simpa using h

  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen]
    simp [Finset.prod_range_succ, arcOf, hup0, hup1, hD]
  obtain ⟨hf1, hfd⟩ := hf
  rw [hnn] at hf1
  have hf2 := hfd 2 (by rw [hlen]; norm_num) (size (c - 2)) (by simp [arcOf, hD])
  have hf0 := hfd 0 (by rw [hlen]; norm_num) (size c) (by simp [arcOf, hup0])
  rw [hnn] at hf2 hf0

  obtain ⟨-, -, hcut, hnot⟩ := hOK.2.2.1 c hc
  rw [hlen] at hcut hnot
  have hnth : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have h := hcut
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rwa [e] at h
  have hth : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hnot 2 (by norm_num) (by norm_num)
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
    have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e] at h
  have hb1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  have hy1 : 1 ≤ size (c - 2) + S := by have := hηs (c - 2); omega
  obtain ⟨X₂, f₂, hsplit, hlev2, hlev0⟩ := ArcLengthThreeDescent.split W hcase hP9 T₁ hW₁.1 hO hinj c (size (c - 1))
    (size (c - 2) + S) (size c + S) hy1 hb1 f hf1 hf2 hf0
  have hval : v (algebraMap O LL (((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S))) =
      (((ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) : ℚ) : ℚ) : WithTop ℚ) := by
    rw [map_pow, map_natCast, AddValuation.map_pow, W.v_l, nsmul_one]
    simp
  have heq : algebraMap O W.EE (((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S)) * f =
      algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂ + f₂ := by
    rw [← hsplit, map_pow, map_natCast]; rfl
  refine ⟨((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S), X₂, f₂,
    ⟨(ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) : ℚ), hval, ?_⟩, heq, hlev2, hlev0⟩
  rw [Rat.cast_natCast]

  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hth1 : b ≤ size (c - 1) := hth.1
  have hth2 : size (c - 1) ≤ b + η := hth.2
  have hh : ((arcOf b w S η up size).h : ℕ) = Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := rfl
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c - 1, hth⟩]
  rw [hh]
  have hp1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hlog0 : 0 ≤ Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
    apply Real.logb_nonneg hp1
    rw [hhB]; push_cast
    have : (1 : ℝ) ≤ (size (c - 1) : ℝ) := by exact_mod_cast hb1
    have : ((size (c - 1) : ℕ) : ℝ) ≤ b + η := by exact_mod_cast hth2
    have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    linarith
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  by_cases hlt : size (c - 1) < PD.p * (size (c - 2) + S)
  · have hK0 : ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) = 0 := by
      unfold ArcLengthThreeDescent.Kc; rw [if_pos hlt]
    have hbd : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
    rw [hK0, Nat.cast_zero]
    exact mul_nonneg (by linarith) hbd
  · push Not at hlt
    have hK := ArcLengthThreeDescent.Kc_le PD.p (size (c - 1)) (size (c - 2) + S) η hy1 hlt hy
    have hA : (PD.p : ℝ) * size (c - 2) + PD.p * S ≤ size (c - 1) := by
      have : ((PD.p * (size (c - 2) + S) : ℕ) : ℝ) ≤ size (c - 1) := by exact_mod_cast hlt
      push_cast at this; linarith [mul_add (PD.p : ℝ) (size (c - 2)) S]
    have hB' : (size (c - 1) : ℝ) < PD.p * size (c - 2) + PD.p * S + PD.p * η := by
      have : ((size (c - 1) : ℕ) : ℝ) < ((PD.p * (size (c - 2) + S + η) : ℕ) : ℝ) := by exact_mod_cast hy
      push_cast at this; linarith [mul_add (PD.p : ℝ) (size (c - 2) + S) η, mul_add (PD.p : ℝ) (size (c - 2)) S]
    have hC1 : (b : ℝ) ≤ size (c - 1) := by exact_mod_cast hth1
    have hC2 : (size (c - 1) : ℝ) ≤ b + η := by exact_mod_cast hth2
    have hband : bandI PD.p b w S η size Cb = 1 := by
      unfold bandI
      rw [if_pos]
      refine ⟨c - 2, hnth, Or.inl (by rwa [show c - 2 + 1 = c - 1 by ring]), ?_⟩
      have hp0 : (0 : ℝ) < PD.p := by linarith
      have hbl : (0 : ℝ) ≤ (b : ℝ) / PD.p := by positivity
      have hpl : (0 : ℝ) ≤ PD.p * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) :=
        mul_nonneg hp0.le hlog0
      have hw0 : (0 : ℝ) ≤ size (c - 2) := Nat.cast_nonneg _
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have hpη : (η : ℝ) ≤ PD.p * η := by nlinarith
      set Q : ℝ := (PD.p : ℝ) * η + PD.p * S + b / PD.p + size (c - 2) +
        PD.p * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) with hQ
      have hpS : (0 : ℝ) ≤ PD.p * S := mul_nonneg hp0.le hS0
      have hQ1 : (PD.p : ℝ) * η + PD.p * S ≤ Q := by rw [hQ]; linarith
      have hQ2 : Q ≤ Cb * Q := by nlinarith
      rw [abs_le]
      constructor <;> linarith
    rw [hband, mul_one]
    have hlb : Real.logb PD.p (size (c - 1) : ℝ) ≤ Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
      apply Real.logb_le_logb_of_le hp1 (by exact_mod_cast (by omega : 0 < size (c - 1)))
      rw [hhB]; push_cast
      have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have : (1 : ℝ) ≤ (size (c - 1) : ℝ) := by exact_mod_cast hb1
      linarith
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeMapLattice
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

theorem arc_length_three_map_lattice [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  :
    ∀ x : W.DD T₁, InFP W T₁ (c - 1) 1 1 x → InFP W T₂ (c - 1) 1 1 (W.map F x) := by
  rintro x ⟨y, hy, rfl⟩
  have hN : ∀ x' : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x' → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (W.map F x') := by
    intro x' hx'
    refine ⟨TypesA.map_NΔ W F hW₁.1 hW₂.1 hx'.1, ?_⟩
    obtain ⟨m, hm, hmx⟩ := Submodule.mem_map.1 hx'.2
    refine Submodule.mem_map.2 ⟨W.map F m, W.map_N F hW₁.1 hW₂.1 m hm, ?_⟩
    rw [← hmx]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [TypesA.map_smulA]
  have h : Pp W T₁ (c - 1) 1 ≤ (Pp W T₂ (c - 1) 1).comap (W.map F).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x', hx', rfl⟩
    show W.map F (a • ((W.φD T₁) ^ 1) x') ∈ Pp W T₂ (c - 1) 1
    rw [pow_one, TypesA.map_smulA, W.map_φ]
    exact AddSubgroup.subset_closure ⟨a, ha, W.map F x', hN x' hx', by rw [pow_one]⟩
  refine ⟨W.map F y, h hy, ?_⟩
  rw [one_smul, one_smul]

theorem arc_length_three_annihilate [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  :
    ∀ u : W.DD T₂, InFNc W T₂ c 1 u → ∃ u₁ : W.DD T₁, InFNc W T₁ c 1 u₁ ∧ InI W T₁ c u₁ ∧
      W.map F u₁ = lA W ^ rr • u := by
  rintro u ⟨y, hy, hyc, rfl⟩
  have hT₁ : IsCrys PD T₁.ρ := hW₁.1
  obtain ⟨h9c, -⟩ := NTB.p9mod_of W hcase hP9 T₁ hT₁
  have hΔ : IsUnit (((PD.p - 1 : ℕ) : O)) := by
    rw [← h9c]; exact (lemG_units W hcase hP9 hT₁ hO hOv hinj).2.2
  obtain ⟨x, hx, hxc, hFx⟩ := NTB.delta_lift W hcase hP9 F hT₁ hΔ c rr (hkill c hc) hy hyc
  refine ⟨x, ⟨x, hx, hxc, (one_smul _ _).symm⟩, NTB.InI_of_N W hcase hP9 hT₁ c hx hxc, ?_⟩
  rw [hFx, one_smul]
  rfl

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CTypeT
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem C_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (Si : Finset ℕ) (hSi : ∀ s ∈ Si, s < A.len c ∧ ∃ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O) (s₀ : ℕ)
    (hlt : ∀ s ∈ Si, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T₁ (A.len c) b₁ c₁ ∈ FilS W T₁ c s bs)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ s₀) • dv W T₂ (A.len c) b (Pi.single k₀ 1))
    (f : W.EE) (hf : InFr W c 1 (∏ s ∈ Si, ps W s ^ (match A.ty (c - (s : ZMod n)) with
        | .up bs => bs | _ => 0)) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x))
    (hup : ∀ s < A.len c, s ∉ Si → ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ A.η) (∏ s' ∈ Si, ps W s' ^ (match A.ty (c - (s' : ZMod n)) with
        | .up bs' => bs' | _ => 0))
        (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    LiftsAtT W A F c b sol k₀ f (s₀ + A.σ PD.p) :=
  TC.C_typeT_of W A F c b sol k₀ hA hc hthick hcase hl hP9 hSec hGL hFL hArc hW₁ hW₂ hb Si hSi b₁ sol₁ hb₁ c₁ s₀
    hlt hpr f hf hdown hup

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantsTypeT
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

theorem N_typeT [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    (f : W.EE) (hf : InFr W c 1 (nnDen W A c) f)
    (hdown : ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c) f) :
    LiftsAtT W A F c b sol k₀ f (rr + A.σ PD.p) := by
  have hR := NTB.ringData_of_crystalline (hcase := hcase) (hP9 := hP9) (T := T₂) (hT := And.left hW₂)
  have hΔ := NTB.isUnit_prime_sub_one (W := W) (hl := hl) (hOv := hOv) (hinj := hinj)
  have hfnn := NTB.nn_of (hcase := hcase) (hP9 := hP9) (hinj := hinj) (hR := hR) (A := A) (c := c)
    (hthick := hthick) (f := f) (hf := hf) (hdown := hdown)
  exact NTB.ntype_core (hcase := hcase) (hl := hl) (hP9 := hP9) (A := A) (hA := hA) (c := c)
    (hc := hc) (F := F) (hArc := hArc) (hNN := hNN) (hW₁ := hW₁) (hW₂ := hW₂) (hΔ := hΔ) (rr := rr)
    (hrr := hrr c hc) (b := b) (sol := sol) (k₀ := k₀) (hb := hb) (hk₀ := hk₀) (f := f) (hfnn := hfnn)

theorem constants_typeT (hA : A.OK) (hc : c ∈ A.cuts)
    (hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCoreT W) (hGL : ArcGamLiftCoreT W) (hFL : ArcFilLowCoreT W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W) (hArcL : ArcLCore W)
    (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) (hk₀ : InLppT W A T₂ c b k₀)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
      ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1)) (x : O) :
    LiftsAtT W A F c b sol k₀ (algebraMap O W.EE x) (rr + A.σ PD.p) := by
  refine NTB.letter_const (A := A) (F := F) (c := c) (b := b) (sol := sol) (k₀ := k₀) (hb := hb)
    (x := x) (h := ?_)
  refine TC.C_typeT_of (hA := hA) (hc := hc) (hthick := hthick) (hcase := hcase) (hl := hl)
    (hP9 := hP9) (hSec := hSec) (hGL := hGL) (hFL := hFL) (hArc := hArc) (hW₁ := hW₁) (hW₂ := hW₂)
    (hb := hb) (Si := ∅) (hSi := by simp) (b₁ := b₁) (sol₁ := sol₁) (hb₁ := hb₁) (c₁ := c₁)
    (s₀ := rr) (hlt := by simp) (hpr := hpr) (hf := ?_) (hdown := ?_) (hup := ?_)
  · rw [Finset.prod_empty]
    unfold InFr
    refine ⟨algebraMap O (LetA O n) x, ?_, ?_⟩
    · simp
    · simp [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  · intro s _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]
  · intro s _ _ bs _
    refine ⟨0, x, ?_⟩
    unfold InFr
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [lE]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

