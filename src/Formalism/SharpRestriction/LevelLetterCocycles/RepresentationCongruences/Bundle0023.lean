module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsHorizontalLiftOfLenThreeOfUp
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterTypeBis
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

theorem exists_liftsAt_le_of_len_three_of_up [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hth : Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2 ≤ size (c - 2)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 18 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁  := by
  classical
  have hp11 : 11 ≤ PD.p := hB.1
  have hSet := hB.2.1
  have hl5 : 5 ≤ PD.p := by omega
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hSet.2.1
  have hηs : ∀ i, η < size i := hSet.2.2.1
  have hup1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    have e : c - 2 + 1 = c - 1 := by ring
    rw [e, hU] at h
    simpa using h
  have hup0 : up c = true := by
    have h := (halt (c - 1)).1
    have e : c - 1 + 1 = c := by ring
    rw [e, hup1] at h
    simpa using h
  have hty0 : (arcOf b w S η up size).ty (c - ((0 : ℕ) : ZMod n)) = .up (size c) := by
    simp [arcOf, hup0]
  have hty1 : (arcOf b w S η up size).ty (c - ((1 : ℕ) : ZMod n)) = .down (size (c - 1)) := by
    simp [arcOf, hup1]
  have hty2 : (arcOf b w S η up size).ty (c - ((2 : ℕ) : ZMod n)) = .up (size (c - 2)) := by
    simp [arcOf, hU]
  have hthick : ∀ t < (arcOf b w S η up size).len c, ((arcOf b w S η up size).ty (c - (t : ZMod n))).thick := by
    intro t _
    simp only [arcOf]
    split <;> rfl
  have hps : ∀ t, ps W t ∈ W.AΔ := fun t => GS.ps_mem W t
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hlen]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [hty0, hty1, hty2]
    simp

  obtain ⟨κ, x, hx⟩ := hf.2 1 (by rw [hlen]; norm_num) (size (c - 1)) hty1
  obtain ⟨s, hs, hdvd⟩ := arc_length_four_denominator W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2
    hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU
    hOK hσ κ x hx
  obtain ⟨x₀, hx₀⟩ := hdvd

  have hBn : 1 ≤ size (c - 1) + S := by have := hηs (c - 1); omega
  obtain ⟨fa, si, hfa1, hfa2, hsi⟩ := exists_fraction_in_frame W hcase hP9 hO hinj T₁ hW₁.1 c (size (c - 2)) (size (c - 1) + S) η s hBn x₀

  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hlt, hpr⟩ := exists_horizontal_lift_of_len_three_of_up W hcase F hB CR hWR hW₁ hW₂ hArc hR2 hO hOv hinj hP9 hSec hHF hFL
    c hc bb sol hbb k₀ hk₀ halt hlen hU hOK hth
  set σ := (arcOf b w S η up size).σ PD.p with hσdef
  set e₄ := s - si with he₄

  have hfaC : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ fa (2 * σ + 1 + σ) := by
    refine liftsAt_thin_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv
      hinj hArc hW₁ hW₂ hbb {2} ?_ b₁ sol₁ hb₁ c₁ (2 * σ + 1) ?_ hpr fa ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact ⟨by rw [hlen]; norm_num, _, hty2⟩
    · intro t ht bs hbs
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [hty2] at hbs
      cases hbs
      exact hlt
    · simp only [Finset.prod_singleton, hty2]
      exact hfa1
    · intro t ht bs hbs
      rw [hlen] at ht
      interval_cases t
      · rw [hty0] at hbs; cases hbs
      · rw [hty1] at hbs
        cases hbs
        simp only [Finset.prod_singleton, hty2]
        refine ⟨s, ((PD.p : ℕ) : O) ^ e₄ * x₀, ?_⟩
        have e : lE W s * fa - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (((PD.p : ℕ) : O) ^ e₄ * x₀) =
            lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) := by
          rw [map_mul, map_pow, map_natCast]; unfold lE; ring
        rw [e]
        exact ArcLengthFourSecond.inFr_num_left hfa2 (W.AΔ.pow_mem (hps 0) _)
      · rw [hty2] at hbs; cases hbs
    · intro t ht hnt bs hbs
      rw [hlen] at ht
      interval_cases t
      · rw [hty0] at hbs
        cases hbs
        simp only [Finset.prod_singleton, hty2]
        refine ⟨s, ((PD.p : ℕ) : O) ^ e₄ * x₀, ?_⟩
        have e : lE W s * fa - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (((PD.p : ℕ) : O) ^ e₄ * x₀) =
            lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀) := by
          rw [map_mul, map_pow, map_natCast]; unfold lE; ring
        rw [e]
        exact ArcLengthFourSecond.inFr_num_right hfa2 (W.AΔ.pow_mem (hps 1) _)
      · rw [hty1] at hbs; cases hbs
      · exact absurd (Finset.mem_singleton_self 2) hnt

  have hfa_nn : InFr W c 1 (nnDen W (arcOf b w S η up size) c) fa := by
    rw [hnn]; exact ArcLengthFourSecond.inFr_den_mul _ hfa1 (W.AΔ.pow_mem (hps 0) _)
  have hgN : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (lE W e₄ * f - fa) (rr + σ) := by
    refine liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv
      hinj hArc hArcL hNN hW₁ hW₂ hsur rr hkill hbb hk₀ _ (ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE e₄ hf.1) hfa_nn) ?_
    intro t ht bs hbs
    rw [hlen] at ht
    interval_cases t
    · rw [hty0] at hbs; cases hbs
    · rw [hty1] at hbs
      cases hbs
      have hnum : ps W 1 ^ (size (c - 1) + (arcOf b w S η up size).S) ∈ PiPs W :=
        Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self 1))) _
      refine ArcLengthFourSecond.inFr_sat W hcase hP9 hinj hnum (ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE e₄ hf.1) hfa_nn) ⟨κ + s, ?_⟩
      have h2 : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
          (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) := by
        rw [hnn]; exact ArcLengthFourSecond.inFr_den_mul _ (ArcLengthFourSecond.inFr_num_left hfa2 (W.AΔ.pow_mem (hps 0) _)) (W.AΔ.pow_mem (hps 0) _)
      have hxE : lE W s * algebraMap O W.EE x = lE W κ * algebraMap O W.EE x₀ := by
        have := congrArg (algebraMap O W.EE) hx₀
        rw [map_mul, map_mul, map_pow, map_pow, map_natCast] at this
        unfold lE; exact this
      have e : lE W (κ + s) * (lE W e₄ * f - fa) =
          lE W (s + e₄) * (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) -
          lE W κ * (lE W s * fa - lE W e₄ * (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x₀)) := by
        unfold lE at hxE ⊢
        linear_combination (((PD.p : ℕ) : W.EE) ^ e₄ * algebraMap (LetA O n) W.EE (letE c)) * hxE
      rw [e]
      exact ArcLengthFourSecond.inFr_sub (ArcLengthFourSecond.inFr_lE _ hx) (ArcLengthFourSecond.inFr_lE _ h2)
    · rw [hty2] at hbs; cases hbs

  have hE1 : rr + σ ≤ rr + 3 * σ + 1 := by omega
  have hE2 : 2 * σ + 1 + σ ≤ rr + 3 * σ + 1 := by omega
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ hE1 hgN)
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ hE2 hfaC)
  rw [sub_add_cancel] at hsum
  refine ⟨rr + 3 * σ + 1 + e₄, ?_, ?_⟩
  ·
    have hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i := by
      refine ⟨c, ?_⟩
      have h1 : (1 : ℕ) ∉ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
        apply Nat.notMem_of_lt_sInf
        have := hlen
        simp only [arcOf] at this
        rw [this]; norm_num
      simp only [Set.mem_setOf_eq, le_refl, true_and, not_not, Nat.cast_one, sub_add_cancel] at h1
      exact h1
    rw [sigma_eq_of_thick_letter PD.p b w S η size hT] at hrr hσ hs hsm ⊢
    have hb1 : 1 ≤ b := by
      obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge PD.p (b + η + S) w S η hp11 (by
        have := hηs c; have := hT; obtain ⟨i, hi⟩ := hT; have := hηs i; have := hi.2; omega)
      have : (1 : ℝ) ≤ b := by linarith
      exact_mod_cast this
    have hsi' : (size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p - η / (PD.p : ℝ) ^ 2 - 1 ≤ si := by
      push_cast at hsi; exact hsi
    exact arc_length_four_cost_bound PD.p hp11 b w (size (c - 2)) S η hb1 ((size (c - 1) : ℝ) + S) s si rr σ hs hsi' hrr hσ
  · have e : lE W (rr + 3 * σ + 1 + e₄) * f = lE W (rr + 3 * σ + 1) * (lE W e₄ * f) := by
      unfold lE; ring
    obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := hsum
    exact ⟨w₁, z, h1, h2, h3, h4, by rw [e]; exact h5⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVSmulA
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

open scoped TensorProduct

namespace ArcLengthTwo

variable (W : LocWach PD LL O v n)

theorem φVB_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.φ.toLinearMap.restrictScalars Qp) := PD.φ_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem crisMap_φ {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V') (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dv, map_sum, map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) :=
  dv_succ W T e b _

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun m' _ hm' => by simp [Pi.single_apply, hm']) (by simp)]
  simp

theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : Type} (s : Finset I)
    (a : I → O) (c₀ : I → Fin d → O) :
    dvO W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, algebraMap O LL (a i) • dvO W T e b (c₀ i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dvO, dv, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (x : O) (c₀ : Fin d → O) :
    dvO W T e b (fun m => x * c₀ m) = algebraMap O LL x • dvO W T e b c₀ := by
  simp only [dvO, dv, map_mul, Finset.smul_sum, smul_smul]

theorem filS_φ (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, ?_⟩
  · rw [hac]
    simpa using hy
  · simp

theorem filS_φ_inv (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u) : x ∈ FilS W T a 0 u := by
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := φVB_inj (by simpa using hyx)
  subst this
  refine ⟨y, ?_, by simp⟩
  rw [← hac]
  simpa using hy

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

theorem RepVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      rw [smul_sub, smul_sub, smul_sub, smul_comm a (lA W ^ κ') (lA W ^ κ • Λ • x), smul_comm a (lA W ^ κ) (Λ • x),
        smul_comm a Λ x, smul_comm a (lA W ^ κ')]
    rw [key]
    exact TypesA.inMultiple_smul W ha hP

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, Pi.single_apply, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem avg_props {T : LocLat G Qp LL O} (a : ZMod n) {z : W.DD T} (hz : z ∈ W.N T)
    (hza : (letE a : LetA O n) • z = z) :
    (∑ δ ∈ W.DelF, W.γD T δ z) ∈ W.NΔ T ∧
      (letE a : LetA O n) • (∑ δ ∈ W.DelF, W.γD T δ z) = ∑ δ ∈ W.DelF, W.γD T δ z := by
  refine ⟨⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ' hδ' => ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
      (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp)
      (fun g _ => ?_)
    rw [W.γD_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← γA_letE W δ a, ← γD_smulA, hza]

end ArcLengthTwo

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

