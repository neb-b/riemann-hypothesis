module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeRepresentationOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeRepresentation
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

theorem arc_length_three_representation [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂)
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh))) :
    (∃ a₀ ∈ W.AΔ, algebraMap (LetA O n) W.EE (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) * f₂ = algebraMap (LetA O n) W.EE a₀) ∧
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1 (W.φD T₂ lam) ∧
      RepVV W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) ((arcOf b w S η up size).M PD.p) (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) bb sol (f₂ • W.φD T₂ lam)
        (fun k => if k = k₀ then lE W ((arcOf b w S η up size).σ PD.p) * f₂ else 0) :=
  arc_length_three_representation_of W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj
    hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb
    halt hsm hlen hD hOK hσ hy f₂ hf₂ lam hlam hlamγ κ Hh hHh h4a

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthTwoCaseDown
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

theorem arc_length_two_case_down [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hup : up c = false) (h2b : size (c - 1) ≤ Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨-, hSur, hηs, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega
  obtain ⟨hct, hcm⟩ := ArcLengthTwo.arc_len_two_thick_letters c hlen
  have hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) := by
    have h := hc
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hupm : up (c - 1) = true := by
    cases h : up (c - 1)
    · exact absurd (h.trans hup.symm) hdiff
    · rfl
  have hty0 : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    simp [arcOf, hupm]
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
    simp [hty0, hty1]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    simp only [arcOf]
    split <;> rfl
  obtain ⟨κ, x, hx⟩ := hf.2 0 (by rw [hlen]; norm_num) (size c) (by simpa using hty0)
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hW₁.1 hO hinj
  have hy1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  obtain ⟨de, x', hde, hde0, hg1, hg2⟩ := ArcLengthTwo.den_step W Br c (size (c - 1)) (size c + S) κ hy1
    (by have := hηs c; omega) f x (by rw [← hnn]; exact hf.1) (by rw [← hnn]; exact hx)
  set g := lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' with hgdef
  have hdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c) g := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp only [Nat.cast_zero, sub_zero, hty0, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hg2
    · simp [hty1] at hbs
  have hgl : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ g (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL
      hO hOv hinj hArc hArcL hNN hW₁ hW₂ hSur rr hkill hbb hk₀ g (by rw [hnn]; exact hg1) hdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  have hcst : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE x')
      (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x'
  have hcst' : LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') (rr + (arcOf b w S η up size).σ PD.p) :=
    LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hcst
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hcst' hgl
  have esum : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' + g = lE W de * f := by
    rw [hgdef]; ring
  rw [esum] at hsum
  have hfin := ArcLengthTwo.lifts_scale W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨rr + (arcOf b w S η up size).σ PD.p + de, ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hct⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg; rw [hhB]
  rw [hSgeq] at hrr hσ ⊢
  set Sg' := Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η with hSg'
  have hx11 : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hSg1 : 1 ≤ Sg' := by
    rw [hSg']; unfold Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    have hh1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      have := hηs c; have := hct.2; exact_mod_cast (by omega : 1 ≤ b + η + S)
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : 0 ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg (by linarith) (by linarith)
    linarith
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  have hηb0 : 0 ≤ (η : ℝ) * bandI PD.p b w S η size Cb := mul_nonneg hη0 hband0
  push_cast
  rcases lt_or_ge (PD.p * size (c - 1)) (size c + S) with hlt | hge
  · rw [hde0 hlt]; push_cast; linarith
  have hb1 : 1 ≤ b := by have := hηs c; have := hct.2; omega
  have hw' : size (c - 1) ≤ w := hnt (c - 1) hcm
  have hAI := ArcLengthTwo.aI_le W F hB' CR hWR c hct hc1
  have hwA : (size (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) + η := by exact_mod_cast h2b
  obtain ⟨k1, k2⟩ := case2b PD.p hp11 b w (size (c - 1)) S η (size c) hb1 hηb hSb hwb hw' hy1 hct.1 hct.2
    _ hAI hwA
  have hDle : (de : ℝ) ≤ η + 5 * Sg' := by
    have hm0 : 0 ≤ max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) := le_max_left _ _
    have hc' := Nat.ceil_lt_add_one hm0
    have hde' : (de : ℝ) ≤ (⌈max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ))⌉₊ : ℝ) := by exact_mod_cast hde
    have hmax : max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) ≤ η + 5 * Sg' - 1 := by
      apply max_le (by linarith)
      push_cast
      linarith
    linarith
  by_cases hband : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size
      (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb
  · have h1 : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hband]
    rw [h1]; linarith
  · have h0 : bandI PD.p b w S η size Cb = 0 := by unfold bandI; rw [if_neg hband]
    rw [hhB] at hband
    have hnb := fun hle => hband ⟨c - 1, hcm, Or.inl (by rw [sub_add_cancel]; exact hct), hle⟩
    have hη4 := k2 Cb hCb hge hnb
    rw [h0]; linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSingleTypeBound
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

namespace A1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem cmpD_add' {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    cmpD W T (x + y) = cmpD W T x + cmpD W T y := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).add_mem hx hy)]
  rw [← map_add (f := _)]
  rfl

theorem cmpD_sum' {ι : Type} (s : Finset ι) (y : ι → W.DD T) (hy : ∀ k ∈ s, y k ∈ W.N T) :
    cmpD W T (∑ k ∈ s, y k) = ∑ k ∈ s, cmpD W T (y k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact map_zero (W.cmp T)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cmpD_add' W T (hy a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun k hk => hy k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hy k (Finset.mem_insert_of_mem hk)]

theorem cmpD_smul_letter' (i : ZMod n) (a : LetA O n) {w : W.DD T} (hw : w ∈ W.N T)
    (hwi : (letE i : LetA O n) • w = w) :
    cmpD W T (a • w) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T w := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem a hw)]
  exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i a w hw hwi

end A1

theorem arc_single_type_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hone : ∀ s < (arcOf b w S η up size).len c, up (c - (s : ZMod n)) = up c) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  have hbas := arcBasic W F hB
  dsimp only at hbas
  obtain ⟨hOK, -, -, -, hσ⟩ := hbas
  have hl : 5 ≤ PD.p := by have := hB.1; omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    by_cases h : up (c - (s : ZMod n)) = true <;> simp [arcOf, h, Formalism.MainNotions.LocalTheoryWindows.LT.thick]
  refine ⟨rr + (arcOf b w S η up size).σ PD.p, by push_cast; linarith, ?_⟩
  cases hup : up c
  ·
    have hdn : ∀ s < (arcOf b w S η up size).len c,
        (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s : ZMod n))) := by
      intro s hs
      have h1 : up (c - (s : ZMod n)) = false := (hone s hs).trans hup
      simp [arcOf, h1]
    have hnn : nnDen W (arcOf b w S η up size) c = 1 := by
      unfold nnDen prodTy
      apply Finset.prod_eq_one
      intro s hs
      rw [hdn s (Finset.mem_range.1 hs)]
      simp
    have hcut' : c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) ∈ (arcOf b w S η up size).cuts :=
      (hOK.2.2.1 c hc).2.2.1
    obtain ⟨d₁, b₁, sol₁, hb₁⟩ :=
      hHF hcase hl _ hOK T₁ hW₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))
    obtain ⟨x₁, hx₁, hx₁eq⟩ := hArcL hcase T₁ T₂ F hsur _ rr ((arcOf b w S η up size).len c)
      (hkill _ hcut') (bb k₀) (hbb.1.1 k₀)
    obtain ⟨a, ⟨-, hxa⟩, -⟩ := hb₁.1.2 x₁ hx₁
    have hb₁N : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hb₁.1.1 m).1.1
    have hb₁l : ∀ m, (letE (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
      fun m => Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T₁ _ (hb₁.1.1 m).2
    have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) • cmpD W T₁ (b₁ m) := by
      rw [hxa, A1.cmpD_sum' W T₁ _ _ (fun m _ => (W.N T₁).smul_mem _ (hb₁N m))]
      exact Finset.sum_congr rfl fun m _ =>
        A1.cmpD_smul_letter' W T₁ _ (a m) (hb₁N m) (hb₁l m)
    have e1 : dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m => PowerSeries.constantCoeff
        (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)))) =
        ((φVB PD (LL := LL) (V := T₁.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₁ x₁) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcmp, map_sum]
      simp only [map_smul]
      rfl
    have e2 : dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) =
        ((φVB PD (LL := LL) (V := T₂.V)) ^ ((arcOf b w S η up size).len c)) (cmpD W T₂ (bb k₀)) := by
      unfold dv
      rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (by simp)]
      simp
    have hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ (fun m =>
        PowerSeries.constantCoeff (a m (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n))))) =
        ((PD.p : LL) ^ rr) • dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1) := by
      rw [e1, e2, hx₁eq]
    refine liftsAt_thin_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hW₁ hW₂ hbb ∅ (by simp) b₁ sol₁ hb₁ _ rr (by simp) hpr f ?_ ?_ ?_
    · have h := hf.1
      rw [hnn] at h
      rw [Finset.prod_empty]
      exact h
    · intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf.2 s hs bs hbs
      rw [hnn] at hx
      exact ⟨κ, x, by rw [Finset.prod_empty]; exact hx⟩
    · intro s hs _ bs hbs
      rw [hdn s hs] at hbs
      simp at hbs
  ·
    refine liftsAt_thick_letter_type W _ F c bb sol k₀ hOK hc hthick hcase hl hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
      hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ f hf.1 ?_
    intro s hs bs hbs
    have h1 : up (c - (s : ZMod n)) = true := (hone s hs).trans hup
    simp [arcOf, h1] at hbs

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterType
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

theorem arc_letter_type_eq_ite [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
  rfl

theorem arc_length_two_reduction [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK)
    (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hlt : dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 1 (size (c - 1)))
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
      ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p)) •
        dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  set A := arcOf b w S η up size with hA
  have hup1 : up (c - 1) = true := by
    cases h : up (c - 1) <;> simp_all
  have hty0 : A.ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    rw [hA, arc_letter_type_eq_ite, hup]; rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    rw [hA, arc_letter_type_eq_ite, hup1]; rfl
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hcase : Formalism.MainNotions.LiftingTheory.CaseA W := hB.2.1.1
  have hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick := by
    intro s _
    rw [hA, arc_letter_type_eq_ite]
    split_ifs <;> rfl
  have hden : nnDen W A c = ps W 1 ^ size (c - 1) := by
    simp only [nnDen, prodTy, hlen, Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      sub_zero, Nat.cast_one, hty0, hty1, pow_zero, one_mul]
  obtain ⟨hf1, hf2⟩ := hf
  have hL := liftsAt_thin_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
    hW₁ hW₂ hbb ({1} : Finset ℕ) (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      refine ⟨by omega, size (c - 1), ?_⟩
      rw [Nat.cast_one, hty1]) b₁ sol₁ hb₁ c₁ (2 * A.σ PD.p) (by
      intro s hs bs hbs
      rw [Finset.mem_singleton] at hs
      subst hs
      rw [Nat.cast_one, hty1] at hbs
      cases hbs
      exact hlt) hpr f (by
      simpa [Nat.cast_one, hty1, ← hden] using hf1) (by
      intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf2 s hs bs hbs
      refine ⟨κ, x, ?_⟩
      simpa [Nat.cast_one, hty1, ← hden] using hx) (by
      intro s hs hs1 bs hbs
      have hs0 : s = 0 := by
        rw [Finset.mem_singleton] at hs1
        omega
      subst hs0
      rw [Nat.cast_zero, sub_zero, hty0] at hbs
      cases hbs)
  refine ⟨2 * A.σ PD.p + A.σ PD.p, ?_, hL⟩
  push_cast
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

