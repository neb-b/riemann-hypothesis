module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentStep
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0017

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthOneOrTwoCaseC
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

theorem arc_length_one_or_two_case_c [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = true) (hnb : ¬ (PD.p * (size (c - 1) + S + η) + η < size c)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  haveI : Fact PD.p.Prime := Fact.mk PD.hp
  obtain ⟨hl11, hSet, h20w, h20η, h20S, -⟩ := hB
  obtain ⟨-, hsur, hsize, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 2 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    exact absurd hlen' (by norm_num)
  have h2mem := Nat.sInf_mem hne
  rw [hlen'] at h2mem
  have hnt1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    have := h2mem.2
    rwa [e] at this
  have hthc : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra h
    have h1 : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨le_refl 1, by simpa using h⟩
    have := Nat.sInf_le h1
    omega
  have hup1 : up (c - 1) = false := by
    rw [hup] at hdiff; simpa using hdiff
  have htyc : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.up (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1)) := by
    simp [arcOf, hup1]
  have hps0 : ps W 0 = qA W := by simp [ps]
  have hnn : nnDen W (arcOf b w S η up size) c = qA W ^ size c := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one, htyc, hty1, hps0, pow_zero, mul_one]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    show (if up (c - (s : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n)))).thick = true
    split_ifs <;> rfl

  obtain ⟨hf1, hf2⟩ := hf
  rw [hnn] at hf1
  obtain ⟨κ, x, hκx⟩ := hf2 1 (by rw [hlen]; norm_num) (size (c - 1)) (by simpa using hty1)
  rw [hnn] at hκx
  change InFr W c (ps W 1 ^ (size (c - 1) + S)) (qA W ^ size c) _ at hκx
  have hw1 : 1 ≤ size (c - 1) := by have := hsize (c - 1); omega
  have hwle : size (c - 1) ≤ w := hnt (c - 1) hnt1
  have hb1 : 1 ≤ b := by omega
  have hb₀1 : 1 ≤ size c := by have := hsize c; omega

  obtain ⟨x'', hx''⟩ := ArcLengthOneTwo.content_step W hcase hP9 hO c (size c) (size (c - 1) + S) κ (by omega) f x
    hf1 hκx
  have hxE : ∀ z : O, algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) z) = algebraMap O W.EE z :=
    fun z => (IsScalarTower.algebraMap_apply O (LetA O n) W.EE z).symm
  have hlE : ∀ k : ℕ, algebraMap (LetA O n) W.EE (lA W ^ k) = lE W k := by
    intro k; simp [lA, lE]
  have hg1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c)
      (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
        algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    rw [hnn]
    obtain ⟨u₀, hu₀, e1⟩ := hf1
    refine ⟨lA W ^ ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) * u₀ - qA W ^ size c * algebraMap O (LetA O n) x'',
      Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) hu₀)
        (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (GS.qA_mem W) _) (Subalgebra.algebraMap_mem _ _)), ?_⟩
    simp only [map_mul, map_sub, map_one, mul_one, hlE, hxE] at e1 ⊢
    linear_combination lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * e1
  have hgdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c)
        (lE W (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S)) * f -
          algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x'') := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp [htyc] at hbs
    · simp only [Nat.cast_one, hty1, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hx''

  have hNg := liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ hg1 hgdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hsur rr hkill hbb
  have hC := liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0
    hSec hGL hFL hO hOv hinj hArc hArcL hW₁ hW₂ hsur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x''
  have hCL := LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hC
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hNg hCL
  rw [sub_add_cancel] at hsum
  have hfin := ArcLengthOneTwo.lifts_lE W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) + (rr + (arcOf b w S η up size).σ PD.p), ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hthc⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [CaseA.sg_eq]; unfold Formalism.MainNotions.N.Ln17.Sg; rw [hhB]; push_cast; ring
  rw [hSgeq] at hrr hσ ⊢
  obtain ⟨-, -, -, -, a5, a6, a7⟩ := CaseA.sg_ge PD.p (b + η + S) w S η hl11 (by omega)
  have hde := ArcLengthOneTwo.deA_le (l := PD.p) (size c) (size (c - 1) + S) (by omega) hb₀1
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hηb : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg _) hband0
  have hlr1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hlr0 : (0 : ℝ) < PD.p := by linarith
  push_cast
  by_cases h1c : PD.p * (size (c - 1) + S) ≤ size c
  · have hc1 := case1c PD.p hl11 b w (size (c - 1)) S η (size c) hb1 h20η h20S h20w hwle hthc.1 hthc.2 h1c
      (Nat.le_of_not_lt hnb) (ArcLengthOneTwo.deA PD.p (size c) (size (c - 1) + S) : ℝ) (by push_cast at hde; exact hde)
    have hBand : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb :=
      ⟨c - 1, hnt1, Or.inl (by rw [sub_add_cancel]; exact hthc), by rw [hhB]; exact hc1.2 Cb hCb⟩
    have hbandI : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hBand]
    rw [hbandI]
    linarith [hc1.1]
  · have hlt : (size c : ℝ) / PD.p < (size (c - 1) : ℝ) + S := by
      rw [div_lt_iff₀ hlr0]
      have : size c < PD.p * (size (c - 1) + S) := Nat.lt_of_not_le h1c
      have hr : ((size c : ℕ) : ℝ) < ((PD.p * (size (c - 1) + S) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hr
      linarith
    have hlog0 : 0 ≤ Real.logb PD.p (size c : ℝ) := Real.logb_nonneg hlr1 (by exact_mod_cast hb₀1)
    have hlogle : Real.logb PD.p (size c : ℝ) ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) := by
      apply Real.logb_le_logb_of_le hlr1 (by exact_mod_cast (by omega : 0 < size c))
      have : (size c : ℝ) ≤ b + η := by exact_mod_cast hthc.2
      push_cast
      have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      linarith
    have hmax : max 0 ((size c : ℝ) / PD.p - ((size (c - 1) + S : ℕ) : ℝ) + 2 + Real.logb PD.p (size c)) ≤
        2 + Real.logb PD.p (size c) := by
      push_cast
      exact max_le (by linarith) (by linarith)
    have hη0 : (0 : ℝ) ≤ η * (PD.p : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hlr0.le)
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeConstantTerm
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

theorem arc_length_three_constant_term [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  (X₂ : O) :
    LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂) (rr + (arcOf b w S η up size).σ PD.p) := by
  have hp11 : 11 ≤ PD.p := hB.1
  have hl5 : 5 ≤ PD.p := by omega
  have hSur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s' < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s' : ZMod n))).thick := by
    intro s' _
    show ((if up (c - (s' : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s' : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s' : ZMod n)))).thick) = true
    cases up (c - (s' : ZMod n)) <;> rfl
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  exact LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb
    (liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr X₂)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeInFPSmulPhiLambda
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

theorem arc_length_three_inFP_smul_phi_lambda [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂) (κ₀ : ℕ) (X₀ : O) (hX₀ : InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (hn₂ : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam)) :
    InFP W T₂ (c - 1) 1 1 (f₂ • W.φD T₂ lam) ∧
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ'' : ℕ, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S))
        (lA W ^ κ'' • g • (lA W ^ (κ₀ + κ) • (f₂ • W.φD T₂ lam) - lA W ^ ((arcOf b w S η up size).σ PD.p) • X₀ • ((W.φD T₂) ^ 3) Hh)) := by
  classical
  set A := arcOf b w S η up size with hA
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hc2 : IsCrys PD T₂.ρ := hW₂.1
  obtain ⟨-, hqU, -⟩ := lemG_units W hcase hP9 hc2 hO hOv hinj
  have hp1U : IsUnit (algebraMap (LetA O n) W.EE (ps W 1)) := by
    rw [show ps W 1 = W.φA (qA W) by rw [← DFD.dfd_ps_zero, ← DFD.dfd_ps_succ]]
    have e : algebraMap (LetA O n) W.EE (W.φA (qA W)) =
        W.φE (algebraMap (LetA O n) W.EE (qA W)) := (W.φE_ext _).symm
    rw [e]
    exact hqU.map W.φE
  obtain ⟨s, hs⟩ : ∃ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) := by
    obtain ⟨u, hu⟩ := hqU.pow (size (c - 1))
    refine ⟨((u⁻¹ : W.EEˣ) : W.EE) * algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)), ?_⟩
    rw [map_pow (algebraMap (LetA O n) W.EE) (qA W), ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hn2 := hn₂ s hs
  have h5 : algebraMap (LetA O n) W.EE (ps W 1 ^ size (c - 1)) * W.φE s =
      algebraMap (LetA O n) W.EE (ps W 2 ^ (size (c - 2) + S)) := by
    have e1 : ps W 1 ^ size (c - 1) = W.φA (qA W ^ size (c - 1)) := by
      rw [map_pow, ← DFD.dfd_ps_zero, ← DFD.dfd_ps_succ]
    have e2 : ps W 2 ^ (size (c - 2) + S) = W.φA (ps W 1 ^ (size (c - 2) + S)) := by
      rw [map_pow, ← DFD.dfd_ps_succ]
    rw [e1, e2]
    have := congrArg W.φE hs
    rw [map_mul, W.φE_ext, W.φE_ext] at this
    exact this
  have hsU : IsUnit s := by
    have h := (hp1U.pow (size (c - 2) + S))
    rw [← map_pow, ← hs] at h
    exact isUnit_of_mul_isUnit_right h
  have hφsU : IsUnit (W.φE s) := hsU.map W.φE
  have hφn : W.φD T₂ (s • lam) = W.φE s • W.φD T₂ lam := W.φD_smul T₂ s lam
  have hlet2 : (letE c : LetA O n) • W.φD T₂ (s • lam) = W.φD T₂ (s • lam) := by
    have hfix := Formalism.MainNotions.LiftingTheory.wmap_Nl_fix W T₂ (c - 1) _ hn2.2
    conv_rhs => rw [← hfix]
    rw [DYB.φD_smulA W, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]
  have gen : ∀ a : LetA O n, a ∈ W.AΔ → ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) x →
      a • W.φD T₂ x ∈ Pp W T₂ (c - 1) 1 := by
    intro a ha x hx
    unfold Pp
    exact AddSubgroup.subset_closure ⟨a, ha, x, hx, by rw [pow_one]⟩

  obtain ⟨u, hu, hf₂e⟩ := hf₂
  have hf₂' : f₂ = algebraMap (LetA O n) W.EE (letE c * u) * W.φE s := by
    apply (hp1U.pow (size (c - 1))).mul_left_cancel
    rw [← map_pow (algebraMap (LetA O n) W.EE), hf₂e]
    simp only [map_mul]
    rw [← h5]
    ring
  have hP1 : f₂ • W.φD T₂ lam = u • W.φD T₂ (s • lam) := by
    rw [hf₂', mul_smul, ← hφn, algebraMap_smul, mul_comm (letE c : LetA O n) u, mul_smul, hlet2]
  refine ⟨⟨_, gen u hu _ hn2, by rw [one_smul, hP1]⟩, ?_⟩

  obtain ⟨u', hu', hX₀e⟩ := hX₀
  rw [DFD.dfd_ps_zero] at hX₀e
  obtain ⟨κ', y₀, hy₀, he⟩ := h4a
  obtain ⟨Λ, hΛmem, hz₀i⟩ : ∃ Λ : LetA O n,
      W.φA Λ ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (Λ • y₀) := by
    have HA := hArc hcase hl5 A hOK c hc 2 (by rw [hA]; show 1 ≤ 2; omega) (by rw [hlen]; omega)
    obtain ⟨-, HT⟩ := HA
    obtain ⟨hΛ, -⟩ := HT T₂ hW₂
    obtain ⟨z₁, hz₁N, hz₁l, hz₁e⟩ := hΛ y₀ hy₀
    have ha : c - ((A.len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n) = c - 1 := by
      rw [hlen]; push_cast; ring
    rw [ha] at hz₁l
    refine ⟨abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2,
      DFD.dfd_φLam_mem W A _ 2, ?_⟩
    rw [hz₁e, one_smul]
    exact ⟨hz₁N, (Formalism.MainNotions.LiftingTheory.wmap_mem_Nl W T₂ (c - 1) z₁).2 ⟨z₁, ((lemGB_memNΔ W).1 hz₁N).1, hz₁l⟩⟩
  have hφz : W.φD T₂ (Λ • y₀) = W.φA Λ • W.φD T₂ y₀ := DYB.φD_smulA W T₂ Λ y₀
  have h2c : lA W ^ κ' • (lA W ^ κ • W.φD T₂ lam - lA W ^ (A.σ PD.p) • ((W.φD T₂) ^ 3) Hh) =
      W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p))) • W.φD T₂ y₀ := by
    have := congrArg (W.φD T₂) he
    simp only [DYB.φD_smulA, map_sub, DFD.dfd_φA_lA] at this
    rw [DFD.dfd_φD_three]
    exact this
  have hB' : size c + S ≤ (PD.p - 1) * A.M PD.p := by
    have hty : (A.ty c).thick = true ∧ (A.ty c).size = size c := by
      rw [hA]; unfold arcOf; dsimp only; split <;> exact ⟨rfl, rfl⟩
    have hS : A.S = S := by rw [hA]; rfl
    have hth := hOK.2.2.2.2.2.2.2.1 c hty.1
    rw [hty.2, hS] at hth
    have hq1 : 0 < PD.p - 1 := by omega
    have key := Nat.lt_mul_div_succ (2 * A.h) hq1
    exact (lt_of_le_of_lt (by omega : size c + S ≤ 2 * A.h) key).le
  obtain ⟨r, hr, hJJ⟩ : ∃ r ∈ W.AΔ, W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p))) =
      qA W ^ (size c + S) * r := by
    obtain ⟨uT, huT, -, -, -, hTr2⟩ := (hTr hcase).2.1 2 (A.M PD.p)
    have hpk : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k = ps W k := fun _ => rfl
    simp only [hpk] at hTr2
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hB'
    have hq : qA W ∈ W.AΔ := by rw [← DFD.dfd_ps_zero]; exact TypesA.ps_mem W 0
    refine ⟨uT * W.π₀ ^ A.M PD.p * qA W ^ t * ps W 1 ^ ((PD.p - 1) * A.M PD.p) *
      ps W 2 ^ (2 * A.G₀), ?_, ?_⟩
    · exact mul_mem (mul_mem (mul_mem (mul_mem huT (pow_mem (TypesA.pi0_mem_ADelta W) _)) (pow_mem hq _))
        (pow_mem (TypesA.ps_mem W 1) _)) (pow_mem (TypesA.ps_mem W 2) _)
    · have e0 : W.φA (W.φA W.π₀) = (W.φA ^ 2) W.π₀ := by rw [pow_two, AlgHom.mul_apply]
      have e2 : W.φA (W.φA (ps W 0)) = ps W 2 := by rw [← DFD.dfd_ps_succ, ← DFD.dfd_ps_succ]
      simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, map_mul, map_pow, hpk]
      rw [e0, e2, hTr2, show Finset.range 2 = Finset.range (1 + 1) from rfl, Finset.prod_range_succ,
        Finset.prod_range_one, DFD.dfd_ps_zero, ht]
      ring
  have hΛA : W.φA Λ ∈ W.AΔ := DFD.dfd_closure_AΔ W hΛmem
  have hgmem : ps W 1 ^ size (c - 1) * ps W 2 ^ (size (c - 2) + S) * W.φA Λ ∈
      Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k} := by
    refine mul_mem (mul_mem (pow_mem (Submonoid.subset_closure ?_) _)
      (pow_mem (Submonoid.subset_closure ?_) _)) hΛmem
    · exact ⟨1, le_refl _, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  have h6 : algebraMap (LetA O n) W.EE (letE c) • W.φD T₂ lam = W.φD T₂ lam := by
    have e : W.φD T₂ lam = ((hφsU.unit⁻¹ : W.EEˣ) : W.EE) • W.φD T₂ (s • lam) := by
      rw [hφn, smul_smul, hφsU.val_inv_mul, one_smul]
    rw [e, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, hlet2]
  refine ⟨_, hgmem, κ', (lA W ^ (κ' + κ) * W.φA Λ * u' * ps W 1 ^ size (c - 1)) • W.φD T₂ (s • lam) +
    (algebraMap O (LetA O n) X₀ * (ps W 1 ^ size (c - 1) * ps W 2 ^ (size (c - 2) + S) * r)) •
      W.φD T₂ (Λ • y₀), add_mem (gen _ ?_ _ hn2) (gen _ ?_ _ hz₀i), ?_⟩
  · exact mul_mem (mul_mem (mul_mem (TypesA.lA_pow_mem W _) hΛA) hu') (pow_mem (TypesA.ps_mem W 1) _)
  · exact mul_mem (W.AΔ.algebraMap_mem X₀) (mul_mem (mul_mem (pow_mem (TypesA.ps_mem W 1) _)
      (pow_mem (TypesA.ps_mem W 2) _)) hr)
  have key := DFD.smul_sub_eq_smul_add (R := W.EE)
    (algebraMap (LetA O n) W.EE (lA W ^ κ')) (algebraMap (LetA O n) W.EE (lA W ^ κ))
    (algebraMap (LetA O n) W.EE (lA W ^ (κ₀ + κ))) (lE W κ₀)
    (algebraMap (LetA O n) W.EE (lA W ^ (A.σ PD.p)))
    (algebraMap (LetA O n) W.EE (ps W 1 ^ size (c - 1) * ps W 2 ^ (size (c - 2) + S) * W.φA Λ))
    (algebraMap O W.EE X₀) (algebraMap (LetA O n) W.EE (letE c))
    (algebraMap (LetA O n) W.EE (qA W ^ (size c + S))) (algebraMap (LetA O n) W.EE u')
    (algebraMap (LetA O n) W.EE (ps W 1 ^ size (c - 1)))
    (algebraMap (LetA O n) W.EE (ps W 2 ^ (size (c - 2) + S)))
    (algebraMap (LetA O n) W.EE (W.φA Λ)) (W.φE s)
    (algebraMap (LetA O n) W.EE (W.φA (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))))
    (algebraMap (LetA O n) W.EE r)
    (algebraMap (LetA O n) W.EE (lA W ^ (κ' + κ) * W.φA Λ * u' * ps W 1 ^ size (c - 1)))
    (algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) X₀ *
      (ps W 1 ^ size (c - 1) * ps W 2 ^ (size (c - 2) + S) * r))) f₂
    (W.φD T₂ lam) (W.φD T₂ y₀) (((W.φD T₂) ^ 3) Hh) (W.φD T₂ (s • lam)) (W.φD T₂ (Λ • y₀))
    (by rw [DFD.dfd_alg_lA, DFD.dfd_alg_lA]; simp only [lE, pow_add])
    (by simp only [map_mul])
    (by simp only [pow_add, map_mul])
    (by rw [map_mul, ← IsScalarTower.algebraMap_apply, map_mul, map_mul])
    (by rw [algebraMap_smul]; exact hφz)
    (by simp only [algebraMap_smul]; exact h2c)
    hφn (by rw [hX₀e, map_mul, map_mul]) h5 h6 (by rw [hJJ, map_mul])
  simpa only [mul_smul, algebraMap_smul] using key

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

