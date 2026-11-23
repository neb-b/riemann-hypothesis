module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0010
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourCostBound
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

theorem arc_length_four_cost_bound (l : ℕ) (hl : 11 ≤ l) (b wm w S η : ℕ) (hb : 1 ≤ b) (B : ℝ) (s si rr σ : ℕ)
    (hs : (s : ℝ) ≤ max 1 ((w : ℝ) - B / l + 16 / 5 * Sg l (b + η + S) wm S η) + 1)
    (hsi : (w : ℝ) - B / l - η / (l : ℝ) ^ 2 - 1 ≤ si)
    (hrr : (rr : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) (hσ : (σ : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) :
    ((rr + 3 * σ + 1 + (s - si) : ℕ) : ℝ) ≤ 18 * Sg l (b + η + S) wm S η + 1 := by
  have h4 := max_sub_le_errorScale l hl b wm w S η hb B ((s : ℝ) - 1) (si : ℝ)
    (max_le (Nat.cast_nonneg _) hsi) (by linarith)
  obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge l (b + η + S) wm S η hl (by omega)
  have hsub : ((s - si : ℕ) : ℝ) ≤ max 0 ((s : ℝ) - 1 - si) + 1 := by
    rcases le_total si s with h | h
    · rw [Nat.cast_sub h]
      have := le_max_right (0:ℝ) ((s : ℝ) - 1 - si)
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      have := le_max_left (0:ℝ) ((s : ℝ) - 1 - si)
      simp only [Nat.cast_zero]
      linarith
  push_cast
  linarith

theorem sigma_eq_of_thick_letter {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) :
    Formalism.MainNotions.N.Ln17.Sg l b w S η size = Sg l (b + η + S) w S η := by
  unfold Formalism.MainNotions.N.Ln17.Sg Sg Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  rw [if_pos hT]

namespace ArcLengthFourSecond

section EEh
variable {W : LocWach PD LL O v n}

theorem lE_eq (k : ℕ) : lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp [lE, lA, map_pow, map_natCast]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c

theorem lA_mem : lA W ∈ W.AΔ := by
  exact natCast_mem _ _

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f) (hg : InFr W a num den g) :
    InFr W a num den (f - g) := by
  obtain ⟨u, hu, hf⟩ := hf
  obtain ⟨u', hu', hg⟩ := hg
  refine ⟨u - u', sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hg, ← map_sub, mul_sub]

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (k : ℕ) (hf : InFr W a num den f) :
    InFr W a num den (lE W k * f) := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨lA W ^ k * u, mul_mem (pow_mem lA_mem k) hu, ?_⟩
  rw [lE_eq, mul_left_comm, hf, ← map_mul]
  congr 1
  ring

theorem inFr_num_left {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₂ : n₂ ∈ W.AΔ) :
    InFr W a n₁ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₂ * u, mul_mem h₂ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_num_right {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₁ : n₁ ∈ W.AΔ) :
    InFr W a n₂ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₁ * u, mul_mem h₁ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_den_mul {a : ZMod n} {num d : LetA O n} (d' : LetA O n) {f : W.EE} (hf : InFr W a num d f) (hd' : d' ∈ W.AΔ) :
    InFr W a num (d' * d) f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨d' * u, mul_mem hd' hu, ?_⟩
  rw [map_mul, mul_assoc, hf, ← map_mul]
  congr 1
  ring

end EEh

end ArcLengthFourSecond

theorem ArcLengthFourSecond.inFr_sat [IsDomain O] [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL)) {c : ZMod n} {num den : LetA O n}
    (hnum : num ∈ PiPs W) {g : W.EE} (h1 : InFr W c 1 den g) (hK : ∃ K : ℕ, InFr W c num den (lE W K * g)) :
    InFr W c num den g := by
  obtain ⟨u₀, hu₀, e₀⟩ := h1
  obtain ⟨K, u₁, hu₁, e₁⟩ := hK
  have key : lA W ^ K * (1 * (letE c * u₀)) = num * (letE c * u₁) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (lA W ^ K * (1 * (letE c * u₀)))
        = lE W K * algebraMap (LetA O n) W.EE (letE c * 1 * u₀) := by
          rw [ArcLengthFourSecond.lE_eq, ← map_mul]; congr 1; ring
      _ = algebraMap (LetA O n) W.EE den * (lE W K * g) := by rw [← e₀]; ring
      _ = _ := by rw [e₁]; congr 1; ring
  obtain ⟨y, hy, hxy⟩ := saturation_fraction_ring W hcase hP9 hinj num 1 1 hnum (one_mem _) (one_mem _) (letE c * u₀)
    (by rw [one_mul]; exact W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₀)
    ⟨K, letE c * u₁, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₁, key⟩
  refine ⟨letE c * y, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hy, ?_⟩
  rw [e₀]
  congr 1
  have hidem : (letE c : LetA O n) * letE c = letE c := by
    unfold letE; rw [← Pi.single_mul, one_mul]
  linear_combination (letE c : LetA O n) ^ 2 * hxy - (((letE c : LetA O n) + 1) * u₀) * hidem

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoefStep
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

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem coef_step (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0) (hinj : Function.Injective (algebraMap O LL))
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (bi : ℕ) (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (j : ℕ) (hj : j ≤ bi) (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ h ∈ W.AΔ, W.γE W.gam (algebraMap (LetA O n) W.EE (qA W ^ j * g) * s) -
        algebraMap (LetA O n) W.EE (qA W ^ j * g) * s =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ j *
        (algebraMap O (LetA O n) (cc ((bi : ℤ) - j)) * g + qA W * h)) * s := by
  exact coef_step_of (W := W) hcase hP9 hT hgpi0
    (fun f hf => gamma_sub_self_mem_pi0_q (W := W) hcase hP9 f hf) hA3 hA4 hinj cc hcc bi s s' hs' hs j hj g hg

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure CoresW [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (CR : ℝ)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop where
  l5 : 5 ≤ PD.p
  hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)
  hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x
  inj : Function.Injective (algebraMap O LL)
  wr : Formalism.MainNotions.LiftingTheory.coreWR W CR
  H : Formalism.MainNotions.LiftingTheory.coreH W
  Tr : Formalism.MainNotions.LiftingTheory.coreTr W
  dc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL
  relay : RelayCore W
  arc : ArcCore W
  arcL : ArcLCore W
  split : SplitCore W
  nn : UnivNNCore W
  univ : UnivCore PD W
  sat : SATcore W
  satP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W
  kLev : KillerLevCore W
  kMod : KillerModCore W
  r2 : R2
  P2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W
  P3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W
  P4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt
  ptEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
    ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ
  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W
  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W
  pi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u
  ext : ExtYCore PD W
  cj : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O
  c4 : Formalism.MainNotions.N.LetterConditionLocal W
  sec : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore W
  gl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W
  hf : Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W
  fl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W
  jq : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a
  jy : ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
    cc ∈ latticeCocycles T₂.L → IsCrys PD T₂.ρ → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD Y.ρ τ a → a = 0 ∨ IsJumpV PD T₂.ρ τ a

end Core

section PPts

variable {l : ℕ} [Fact l.Prime]

theorem primitive_root_pow_l_eq_one (P : LocPrime l) : P.ζQ 1 ^ l = 1 := by
  have h := P.ζQ_succ 0
  simpa [P.ζQ_zero] using h

theorem primitive_root_mem_cyclotomic (P : LocPrime l) (K : FinExt l) : P.ζQ 1 ∈ Ks K 1 := by
  unfold Ks
  apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ K0 K ⊔ _)
  apply IntermediateField.subset_adjoin
  show P.ζQ 1 ^ (l ^ 1) = 1
  rw [pow_one]
  exact primitive_root_pow_l_eq_one P

def galoisEmbedding {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 where
  toFun y := ⟨g y, hG.2.2.2 (g.toAlgHom.comp (Ks K 1).val) y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

theorem galoisEmbedding_coe {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) (y : ↥(Ks K 1)) :
    ((galoisEmbedding hG g y : ↥LL.1) : Om l) = g y := rfl

theorem exists_galois_extending_algHom {F : IntermediateField ℚ_[l] (Om l)} (τ : F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : F, g x = τ x := by
  classical
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have h := τ.liftNormal_commutes (Om l) x
  simpa using h

end PPts

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

structure UsedJ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop where
  a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F
  a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F
  c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F

theorem ptEx_at (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] :
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hG) τ i →
      ∃ ζ : ↥LL.1, ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG i ζ τ := by
  intro i τ hτ
  classical
  have hτ' := hτ
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ'
  obtain ⟨g, hg⟩ := exists_galois_extending_algHom ((LL.1).val.comp τ)
  have hz := primitive_root_mem_cyclotomic (D.loc l) K
  have h1 : ((galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩ : ↥LL.1) : Om l) = g ((D.loc l).ζQ 1) :=
    galoisEmbedding_coe hG g _
  refine ⟨galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩, ?_, ?_, ?_⟩
  · rw [(D.loc l).PD_p K]
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, h1, OneMemClass.coe_one]
    rw [← map_pow, primitive_root_pow_l_eq_one, map_one]
  · intro h
    apply (D.loc l).ζQ_one
    have h2 := congrArg (fun z : ↥LL.1 => (z : Om l)) h
    simp only [h1, OneMemClass.coe_one] at h2
    exact g.injective (h2.trans (map_one g).symm)
  · unfold Formalism.MainNotions.DeltaInvariantLattices.ptK Formalism.BasicNotions.LocHW.IsPt
    refine ⟨galoisEmbedding hG g, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
    · rw [← hτ']
      apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact hg (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x)
    · exact congrArg (galoisEmbedding hG g) (Subtype.ext hy)
    · apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact (hg x).symm

end Record

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ProdTwoLevelsEqConst
section
open scoped TensorProduct

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

variable [IsDomain O] [IsDiscreteValuationRing O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

def ea (a : ZMod n) (F : PowerSeries O) : W.EE :=
  algebraMap (LetA O n) W.EE (letE a * Br.cst F)

theorem letE_mul_self (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Formalism.BasicNotions.letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem ea_add (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F + F') = ea Br a F + ea Br a F' := by
  have h : Br.cst (F + F') = Br.cst F + Br.cst F' := funext fun _ => map_add Br.ι F F'
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_add, map_add (f := _)]

theorem ea_zero (a : ZMod n) : ea Br a 0 = 0 := by
  have h : Br.cst 0 = 0 := funext fun _ => map_zero Br.ι
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_zero, map_zero]

theorem cst_mul_ea (a : ZMod n) (G F : PowerSeries O) :
    algebraMap (LetA O n) W.EE (Br.cst G) * ea Br a F = ea Br a (G * F) := by
  have h : Br.cst (G * F) = Br.cst G * Br.cst F := funext fun _ => map_mul Br.ι G F
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [← map_mul, h]
  congr 1
  ring

theorem ea_C_mul (a : ZMod n) (x : O) (F : PowerSeries O) :
    ea Br a (C x * F) = algebraMap O W.EE x * ea Br a F := by
  have h1 : Br.cst (C x * F) = algebraMap O (LetA O n) x * Br.cst F := by
    funext i
    show Br.ι (C x * F) = (algebraMap O (LetA O n) x) i * Br.ι F
    rw [← PowerSeries.smul_eq_C_mul, map_smul, Algebra.smul_def]
    rfl
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h1, mul_left_comm, map_mul, ← IsScalarTower.algebraMap_apply]

theorem ea_sum (a : ZMod n) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries O) :
    ea Br a (∑ i ∈ s, F i) = ∑ i ∈ s, ea Br a (F i) := by
  have h1 : Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i) := by
    funext j
    rw [Finset.sum_apply]
    exact map_sum Br.ι F s
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, Finset.mul_sum, map_sum]

theorem ea_inj (a : ZMod n) {F F' : PowerSeries O} (h : ea Br a F = ea Br a F') : F = F' := by
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea at h
  have h1 := congrFun (W.EE_inj h) a
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE, Pi.single_eq_same, one_mul] at h1
  exact Br.inj h1

theorem letE_mul_AΔ (a : ZMod n) {u : LetA O n} (hu : u ∈ W.AΔ) :
    ∃ U : PowerSeries O, letE a * u = letE a * Br.cst U := by
  obtain ⟨U, hU⟩ := Br.range u hu a
  refine ⟨U, ?_⟩
  funext i
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE]
  by_cases h : i = a
  · subst h
    simp only [Pi.single_eq_same, one_mul]
    exact hU
  · simp [Pi.single_apply, h]

theorem inFr_ea (a : ZMod n) {N D : PowerSeries O} {f : W.EE} (h : InFr W a (Br.cst N) (Br.cst D) f) :
    ∃ U : PowerSeries O, algebraMap (LetA O n) W.EE (Br.cst D) * f = ea Br a (N * U) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.InFr at h
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  refine ⟨U, ?_⟩
  rw [h]
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  congr 1
  have hc : Br.cst (N * U) = Br.cst N * Br.cst U := funext fun _ => map_mul Br.ι N U
  rw [hc]
  calc (letE a : LetA O n) * Br.cst N * u = Br.cst N * ((letE a : LetA O n) * u) := by ring
    _ = Br.cst N * ((letE a : LetA O n) * Br.cst U) := by rw [hU]
    _ = (letE a : LetA O n) * (Br.cst N * Br.cst U) := by ring

theorem p_zero : Br.P.p 0 = X := rfl

theorem ps_cst (s : ℕ) : ps W s = Br.cst (Br.P.p s) := by
  induction s with
  | zero =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps
    rw [pow_zero, AlgHom.one_apply]
    funext i
    show W.π₀₁ + ((PD.p : ℕ) : PowerSeries O) = Br.ι X
    rw [Br.ι_X, map_natCast]
  | succ s ih =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps at ih ⊢
    rw [pow_succ', AlgHom.mul_apply, ih]
    funext i
    show W.φ₀ (Br.ι (Br.P.p s)) = Br.ι (Br.P.p (s + 1))
    rw [← Br.ι_φ]
    congr 1
    show Br.P.φ ((Br.P.φ : PowerSeries O → PowerSeries O)^[s] X) = (Br.P.φ : PowerSeries O → PowerSeries O)^[s + 1] X
    rw [Function.iterate_succ_apply']

theorem prod_two_levels_eq_const (F : ℕ → ℕ) :
    (∏ s ∈ Finset.range 2, ps W s ^ F s) = Br.cst (X ^ F 0 * Br.P.p 1 ^ F 1) := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [ps_cst Br, ps_cst Br]
  funext i
  simp only [Pi.mul_apply, Pi.pow_apply]
  show Br.ι X ^ F 0 * Br.ι (Br.P.p 1) ^ F 1 = Br.ι (X ^ F 0 * Br.P.p 1 ^ F 1)
  rw [map_mul, map_pow, map_pow]

theorem toNat_split (m : ℕ) (α : ℤ) (h : -(m : ℤ) ≤ α) :
    m + α.toNat = (-α).toNat + (m + α).toNat := by
  omega

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

