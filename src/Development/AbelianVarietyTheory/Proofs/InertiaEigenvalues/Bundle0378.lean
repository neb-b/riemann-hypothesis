module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LetterFree

theorem letters_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachLatticeFreeGlobal D HW F := by
  intro D HW F l _ K s LL h T hT
  obtain ⟨hd, -, hb⟩ := letters_loc (HW l) K s LL h T hT
  refine ⟨hd.2.symm, fun i => ?_⟩
  obtain ⟨b, hb1, hb2⟩ := hb i
  exact ⟨_, b, hb1, hb2⟩

end GlobalTheory.NL.LetterFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair

namespace GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_cong_one [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  obtain ⟨b, hb⟩ := exists_int_cong P z hz
  obtain ⟨a, ha⟩ := (hef P hP).2.2 b
  have h3 := OrderUnits.val_int_le P 1 _ (by simpa using ha)
  refine ⟨a, ?_⟩
  rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
  have := Valuation.map_sub_le _ hb h3
  rw [sub_sub_sub_cancel_left] at this
  exact this

theorem exists_cong [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (m : ℕ) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  induction m with
  | zero => exact ⟨0, by simpa [iota_zero, zero_coord] using hz⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top m
    have hv : Valued.v (iota t P) = WithZero.exp (-(m : ℤ)) := by
      refine eq_exp_of_le (val_iota_le_of_mem hP m ht) fun h3 => ht' ?_
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      convert h3 using 2
      push_cast; ring
    have ht0 : iota t P ≠ 0 := fun h => by
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨c, hc⟩ := exists_cong_one hs hP ((iota a P - z) / iota t P) (by
      rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]; exact ha)
    refine ⟨a - t * c, ?_⟩
    have : iota (a - t * c) P - z = -(iota t P * (iota c P - (iota a P - z) / iota t P)) := by
      rw [iota_sub, iota_mul, sub_coord, mul_coord]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, hv]
    refine (mul_le_mul' le_rfl hc).trans_eq ?_
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring


end GlobalTheory.LamTie.ConjLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeOfLe
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (h : χ.LevelLe w m) (hm : m ≤ m') : χ.LevelLe w m' := by
  intro x hx hv

  refine h x hx (le_trans hv ?_)
  rw [WithZero.exp_le_exp]
  omega

theorem expAt_mul_inv : ∀ (E : Type) [Field E] [NumberField E] (χ χ' : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ),
    1 ≤ n → ExpAt χ w n → χ'.LevelLe w (n - 1) → ExpAt (χ' * χ⁻¹) w n := by
  intro E _ _ χ χ' w n hn hχ hχ' m
  constructor
  · intro hm

    by_contra hlt
    have h1 : (χ' * χ⁻¹).LevelLe w (n - 1) := levelLe_of_le hm (by omega)
    have h2 : χ.LevelLe w (n - 1) := by
      have h3 := Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.inv h1) hχ'
      have h4 : (χ' * χ⁻¹)⁻¹ * χ' = χ := by group
      rwa [h4] at h3
    have := (hχ (n - 1)).mp h2
    omega
  · intro hm

    have hc : χ.LevelLe w m := (hχ m).mpr hm
    have hc' : χ'.LevelLe w m := levelLe_of_le hχ' (by omega)
    exact Formalism.L2.Host.HChar.LevelLe.mul hc' (Formalism.L2.Host.HChar.LevelLe.inv hc)

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.StepLiftPf

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem liftF_mono {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

section MonoLoc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_mono_loc {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' :=
  liftF_mono PD F hF he

end MonoLoc

section Core

variable {l : ℕ} [Fact l.Prime]

theorem incl_cont {K K' : FinExt l} (h : K.1 ≤ K'.1) : Continuous (Subgroup.inclusion (GK_le h)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem sub_props (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x))
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ))
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Set ℤ) (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ U)
    (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hW : IsSubFam Ms W) :
    (pc P h hN hF hS).IsPotCrys W.ρ ∧ (pc P h hN hF hS).InertiaThrough W.ρ Sig ∧
      ∀ τ, JumpsInV (P.PD K) W.ρ τ U := by
  refine ⟨?_, GlobalTheory.inertiaThrough_of_isSubFam l P K K' LL h hN hF hS ι k Ms W hW Sig htr hcop hin,
    fun τ => GlobalTheory.Pass.jumpsInV_of_isSubFam l P K LL ι k Ms W hW τ U fun x => hJ x τ⟩
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := incl_cont h
  let W' : GRep ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W.V, ρ := W.ρ.comp incl, cont := fun x => (W.cont x).comp hincl }
  let Ms' : ι → (↥(GK K') →* Matrix (Fin k) (Fin k) ↥LL.1) := fun x => (Ms x).comp incl
  have hc' : ∀ x v, Continuous fun g => (Ms' x g).mulVec v :=
    fun x v => ((hc x).comp hincl).matrix_mulVec continuous_const
  have hcr' : ∀ x, IsCrys (P.PD K') (matRep (Ms' x)) := fun x =>
    (GlobalTheory.PcRes.main l P K K' LL h hN hF hS _ (matRep (Ms x))).2.1 (hpot x)
  have hsub : IsSubOfSums W'.ρ (fun x => ⇑(Ms' x)) := by
    obtain ⟨a, x, p, hp, hinj⟩ := hW
    refine ⟨a, x, LinearMap.pi p, ?_, fun g v => funext fun j => hp j (incl g) v⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  have hW' : IsCrys (P.PD K') W'.ρ :=
    (subsum_crys (PD := P.PD K') (Ms := Ms') (hc := hc') (hF := hFont) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact (GlobalTheory.PcRes.main l P K K' LL h hN hF hS W.V W.ρ).2.2 hW'

end Core

section Apply

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
theorem liftFam_core (P : LocPrime l) (K' LL : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (CT : ℕ) (hT : thmT (pc P h hN hF hS) LL CT)
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK (qlExt l)) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l)))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK (qlExt l))) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD (qlExt l)) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD (qlExt l)) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  intro W₁ W₂ hW₁ hW₂ L₁ L₂ F hFo
  have k₁ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₁ hW₁
  have k₂ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₂ hW₂
  let T₁ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₁.V, modO := W₁.modO, towO := W₁.towO, ρ := W₁.ρ, cont := W₁.cont, L := L₁ }
  let T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₂.V, modO := W₂.modO, towO := W₂.towO, ρ := W₂.ρ, cont := W₂.cont, L := L₂ }
  obtain ⟨h4, hL⟩ := hT T₁ T₂ F N η H U Sig Fr k₁.1 k₂.1 hFo hFr hSt h1 hcard hN2 k₁.2.1 k₂.2.1 hU hU0
    hUc hη hηH k₁.2.2 k₂.2.2 hsize
  have hr : rPrime (pc P h hN hF hS).Iner Fr Sig ≤ N ^ 2 / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [mul_comm]; exact h4)
  have he : CT * (N * rPrime (pc P h hN hF hS).Iner Fr Sig + η * (N + rPrime (pc P h hN hF hS).Iner Fr Sig)) ≤
      CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4)) := by
    gcongr
  exact liftF_mono_loc (P.PD (qlExt l)) (T₁ := T₁) (T₂ := T₂) F hL he

end Apply

section Wrap

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
theorem liftFam_of_eq (P : LocPrime l) (K K' LL : FinExt l) (hK : K = qlExt l) (CT : ℕ)
    (hT : ∀ (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
      thmT (pc P h hN hF hS) LL CT)
    (hFont : ∀ K'' : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt (P.PD K'') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK K))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (hx : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)) ∧
      (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD K) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  subst hK
  by_cases hne : Nonempty ι
  · obtain ⟨x0⟩ := hne
    exact liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      Sig Fr hFr hSt h1 hcard (hx x0).2.1 (hx x0).2.2.1 (fun x => (hx x).1) (fun x => (hx x).2)
      U hU hU0 hUc hJ
  · have hemp : ∀ x : ι, False := fun x => hne ⟨x⟩
    refine liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      {1} Fr hFr ?_ (Finset.mem_singleton_self _) (by rw [Finset.card_singleton]; omega) ?_ ?_
      (fun x => (hemp x).elim) (fun x => (hemp x).elim) U hU hU0 hUc hJ
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨1, Finset.mem_singleton_self _, fun _ _ _ => rfl⟩
    · intro a ha g _
      rw [Finset.mem_singleton] at ha
      subst ha
      rfl
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [orderOf_one]
      exact Nat.coprime_one_left _

end Wrap

theorem main : StepLift := by
  intro D CT hT hFont i w hw hdeg ι Ms hc eta H hlt hsize hPot hJump
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hSt, h1, hcard, hx⟩ := hPot
  obtain ⟨U, hU, hU0, hUc, hJ⟩ := hJump
  have hK : (D.nbr i w hw).Kw = Formalism.MainNotions.ElementDenominator.qlExt (D.nd.l i) :=
    Subtype.ext (IntermediateField.finrank_eq_one_iff.1 hdeg)
  have hT' : Formalism.MainNotions.ElementDenominator.CorollaryALocal D.loc CT := hT
  have hnV : 2 ≤ D.R.nV + 1 := by
    have h5 := D.R.rank_add_five_le
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hcl : ∀ x, Continuous (Br.loc D.nbr i w hw (Ms x)) := by
    intro x
    have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h1' : Continuous fun g : Br.G D.nbr i w hw => Ms x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
      (hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    exact h1'.matrix_map hfc
  exact liftFam_of_eq (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK CT
    (fun K' h hN hF hS => hT' (D.nd.l i) K' h hN hF hS (D.nbr i w hw).LL)
    (fun K'' => hFont (D.nd.l i) K'' (D.nbr i w hw).LL)
    (fun x => Br.loc D.nbr i w hw (Ms x)) hcl (D.R.nV + 1) (eta + D.R.t + 1) H hnV (by omega) hlt hsize
    h hN hF hS Sig Fr hFr hSt h1 hcard hx U hU hU0 hUc hJ

end GlobalTheory.StepLiftPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapTensorOneCommDiagonalAction
section
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section PotTransport

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem linearMap_tensorOne_comm_diagonalAction {H : Type} [Group H] {K₁ K₂ : Type} [Field K₁] [Field K₂]
    [Algebra Qp K₁] [Algebra Qp K₂] [Algebra K₁ K₂] [IsScalarTower Qp K₁ K₂]
    [Algebra K₁ B] [IsScalarTower Qp K₁ B]
    [Algebra K₁ BdR] [Algebra K₂ BdR] [IsScalarTower Qp K₂ BdR]
    [IsScalarTower K₁ K₂ BdR] [IsScalarTower Qp K₁ BdR]
    (PD : PeriodData H Qp K₁ K₂ B BdR) {σ : Representation LL H V} {σ' : Representation LL H V'}
    (f : V →ₗ[LL] V') (hf : ∀ g v, f (σ g v) = σ' g (f v)) (g : H) (x : V ⊗[Qp] B) :
    SumJumps.ext1 Qp B f (actVB PD σ g x) = actVB PD σ' g (SumJumps.ext1 Qp B f x) := by
  unfold actVB
  rw [SumJumps.ext1_comm f (σ g) (σ' g) (hf g)]

theorem eq_map_of_equiv_tensor (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] B)) (S' : Submodule LL (V' ⊗[Qp] B))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp B e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp B e.symm.toLinearMap x ∈ S) :
    S = S'.map (SumJumps.ext1 Qp B e.symm.toLinearMap) := by
  apply le_antisymm
  · intro x hx
    refine ⟨_, a x hx, ?_⟩
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  · rintro _ ⟨y, hy, rfl⟩
    exact b y hy

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dpcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ PC.Dpcris ρ, SumJumps.ext1 Qp B f x ∈ PC.Dpcris ρ' :=
  SumJumps.dcris_map PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') f (fun h v => hf (h : G) v)

theorem eig_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (I : Subgroup G)
    (a : I →* LLˣ) : ∀ x ∈ PC.Eig ρ I a, SumJumps.ext1 Qp B f x ∈ PC.Eig ρ' I a := by
  intro x hx
  simp only [PotCrysData.Eig, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨dpcris_map PC f hf x hx.1, fun g => ?_⟩
  rw [← linearMap_tensorOne_comm_diagonalAction PC.PD f hf, hx.2 g, map_smul]

theorem potCrys_inertiaThrough_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧
      ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S := by
  have he' : ∀ g v, e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) :=
    symm_equivariant e he
  refine ⟨fun h => isCrys_of_equiv PC.PD' (ρ := PC.resH ρ) (ρ' := PC.resH ρ') e (fun h v => he (h : G) v) h, fun S hS => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨h1, h2, ?_⟩
  have hD : PC.Dpcris ρ = (PC.Dpcris ρ').map (SumJumps.ext1 Qp B e.symm.toLinearMap) :=
    eq_map_of_equiv_tensor e _ _ (dpcris_map PC e.toLinearMap he)
      (dpcris_map PC e.symm.toLinearMap he')
  have hE : ∀ a, PC.Eig ρ PC.Iner a =
      (PC.Eig ρ' PC.Iner a).map (SumJumps.ext1 Qp B e.symm.toLinearMap) := fun a =>
    eq_map_of_equiv_tensor e _ _ (eig_map PC e.toLinearMap he _ a)
      (eig_map PC e.symm.toLinearMap he' _ a)
  rw [hD, h3, Submodule.map_iSup]
  congr 1; ext a
  rw [Submodule.map_iSup, hE]

end PotTransport

end GlobalTheory.HTW.Rec

theorem GlobalTheory.HTW.Rec.potCrysData_transport : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (e : V ≃ₗ[LL] V'),
    (∀ g v, e (ρ g v) = ρ' g (e v)) →
    (PC.IsPotCrys ρ' → PC.IsPotCrys ρ) ∧ ∀ S : Finset (PC.Iner →* LLˣ), PC.InertiaThrough ρ' S → PC.InertiaThrough ρ S :=
  by
  intros
  exact GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ ‹_› ‹_›
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNat
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_abelian_nat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ),
      OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ),
        σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  intro F _ _ _ _ M _ _ p e n h σ hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M n] at hσ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M
    (min (2 * n) (n + e)), ← map_pow]
  exact Subgroup.mem_map_of_mem _ (GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min F p e n h x hx)

end GlobalTheory.PMon.Ram
end

