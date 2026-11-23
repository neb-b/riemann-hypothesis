module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0038
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IndepStep
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem cmpD_sum (T : LocLat G Qp LL O) (a : ZMod n) {d : ℕ} (c : Fin d → LetA O n) (z : Fin d → W.DD T)
    (hz : ∀ m, z m ∈ W.N T) (hzl : ∀ m, (letE a : LetA O n) • z m = z m) :
    cmpD W T (∑ m, c m • z m) =
      ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) • cmpD W T (z m) := by
  have hmem : ∀ m, c m • z m ∈ W.N T := fun m => (W.N T).smul_mem _ (hz m)
  have hs : ∑ m, c m • z m ∈ W.N T := (W.N T).sum_mem fun m _ => hmem m
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hs]
  have e : (⟨∑ m, c m • z m, hs⟩ : ↥(W.N T)) = ∑ m, (⟨c m • z m, hmem m⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T a (c m) (z m) (hz m) (hzl m),
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (hz m)]

variable [NeZero n]

theorem indep_step (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) :
    ∀ m, ∃ c₁ ∈ W.AΔ, letE (c' + (e : ZMod n)) * c₁ = c₁ ∧ c m = W.π₀ * c₁ := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  have hz : ∀ m, InFNc W T a 1 (Λ • ((W.φD T) ^ e) (b m)) := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e (hb.1 m))
  have hzN : ∀ m, Λ • ((W.φD T) ^ e) (b m) ∈ W.N T := fun m => by
    obtain ⟨y, hy, -, hye⟩ := hz m; rw [hye, one_smul]; exact hy.1
  have hzl : ∀ m, (letE a : LetA O n) • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ((W.φD T) ^ e) (b m) := fun m => by
    obtain ⟨y, -, hyl, hye⟩ := hz m; rw [hye, one_smul]; exact hyl
  have hsum : ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = 0 := by
    rw [show ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ∑ m, c m • ((W.φD T) ^ e) (b m) by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun m _ => smul_comm _ _ _, h0, smul_zero]
  have hcmp := cmpD_sum W T a c _ hzN hzl
  rw [hsum] at hcmp
  have hc0 : cmpD W T (0 : W.DD T) = 0 := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact (W.cmp T).map_zero
  rw [hc0] at hcmp
  obtain ⟨t, ht⟩ := cmpD_lam W hs hR hp0 h5 T h3 A hA c' hc' hT e
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hrel : ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
      dv W T e b (Pi.single m 1) = 0 := by
    have hpt : ((PD.p : LL) ^ t) ≠ 0 := pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W)
    rw [← hadef, ← hΛdef] at ht
    have e1 : ((PD.p : LL) ^ t) • ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
        dv W T e b (Pi.single m 1) = 0 := by
      rw [hcmp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ht (b m) (hb.1 m), Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, smul_comm]
    exact (smul_eq_zero.1 e1).resolve_left hpt
  have hcc : ∀ m i, PowerSeries.constantCoeff (c m i) = 0 := by
    intro m i
    by_cases hi : i = a
    · subst hi
      have := Fintype.linearIndependent_iff.1 hfb _ hrel m
      exact hinj (by rw [this, map_zero])
    · have := congrFun (hcl m) i
      rw [Pi.mul_apply, letE, Pi.single_eq_of_ne hi, zero_mul] at this
      rw [← this, map_zero]
  intro m
  have hinv : ∀ i, Formalism.MainNotions.WachCoordinates.Br.Inv1 W (c m i) := fun i δ hδ => by
    have := congrFun (hc m δ hδ) i
    rwa [γA_apply] at this
  choose f hf using fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf_full hR (c m i) (hinv i)
  have hf0 : ∀ i, PowerSeries.constantCoeff (f i) = 0 := fun i => by
    rw [← Formalism.MainNotions.WachCoordinates.Br.ιOf_const hR, hf i, hcc m i]
  choose g hg using fun i => (PowerSeries.X_dvd_iff.2 (hf0 i))
  let c₂ : LetA O n := fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf hR (g i)
  have hc₂ : c₂ ∈ W.AΔ := fun δ hδ => by
    funext i
    rw [γA_apply]
    exact Formalism.MainNotions.WachCoordinates.Br.ιOf_inv hR (g i) δ hδ
  have hcm : c m = W.π₀ * c₂ := by
    funext i
    rw [← hf i, hg i, map_mul, Formalism.MainNotions.WachCoordinates.Br.ιOf_X]
    rfl
  refine ⟨letE a * c₂, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hc₂,
    by rw [← mul_assoc, letE_mul_self], ?_⟩
  rw [← hcl m, hcm]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QPowSmulFrobeniusMem
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section LemGAxF

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

def lemGAx_F (B K : ℤ) (c : M) (k : ℤ) : Submodule R M :=
  if k < -B then ⊥ else if k < K then Submodule.span R {c} else ⊤

theorem lemGAx_F_mono (B K : ℤ) (c : M) : Monotone (lemGAx_F (R := R) B K c) := by
  intro a a' h
  unfold lemGAx_F
  split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | (exfalso; omega)

end LemGAxF

section LemGAx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGAx_pull1N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1, Formalism.MainNotions.LiftingTheory.qp W ^ k • p ∈ W.N T := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, ⟨hxN, hxD⟩, rfl⟩ := hg
    simpa using hgen x hxN hxD
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem q_pow_smul_frobenius_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hs : W.s = 1) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) :
    ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ M (c + 1) • W.φD T x ∈ W.N T := by
  intro x hxN hxD
  have hxl : x ∈ W.Nl T (c + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hxN, by rw [LinearMap.smul_apply, LinearMap.id_apply, hxD.1]⟩
  exact (Formalism.MainNotions.LiftingTheory.lifta_Qq W hR hs T _ _).1 (h5.1 (c + 1) x hxl)

theorem lemGAx_parity {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    ((i - 1).val + d) % 2 = 0 := by
  have := parity_succ hn d (i - 1)
  rw [sub_add_cancel] at this
  omega

theorem lemGA_x_of [NeZero n] (W : LocWach PD LL O v n)
    (hER : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W) (hEU : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W)
    (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hJ : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η)) :
    GammaActionLemma W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD hFil la hla
  obtain ⟨htr, hlaD, hlaP, -⟩ := hla
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hπ : W.π₀ ∈ W.AΔ := hR.πΔ
  have hq : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  have hp1 : Formalism.MainNotions.LiftingTheory.pk W 1 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.pk_mem_AΔ W hπ 1
  have hJ2 := hJ d T₁ T₂ F b S η m hS
  have hp5 := h5 T₂ (MiW d b S η) (hiW d b S η) hT hJ2
  have hpar1 := lemGAx_parity hn d i hi
  have hMi : MiW d b S η i = η := by unfold MiW; rw [if_neg (by omega)]
  have hM2 : MiW d b S η (i - 1 + 1) = η := by rw [sub_add_cancel]; exact hMi
  have hbH : b i ≤ hpar n b S := by
    unfold hpar; exact le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_add_right _ _)
  set H := hpar n b S + η with hH
  set σ := lemG_sig PD.p H with hσ
  set h₂ := b (i - 1) + S with hh₂

  have hg2 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ x ∈ W.N T₂ := by
    intro x hxN hxD
    have := q_pow_smul_frobenius_mem W T₂ hR hA.2.1 hp5 (i - 1) x hxN hxD
    rwa [hM2] at this
  have hm0 : Formalism.MainNotions.LiftingTheory.qp W ^ η • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) ∈ W.N T₂ :=
    lemGAx_pull1N W T₂ (i - 1) η hg2 _ hlaP

  obtain ⟨Uq, hUq⟩ := hR.qU
  set x : W.DD T₂ := ((Uq⁻¹ : W.EEˣ) : W.EE) ^ b i • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) with hxdef
  have hxe : Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by
    rw [hxdef, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i), smul_smul, map_pow, ← hUq, ← mul_pow,
      Units.mul_inv, one_pow, one_smul]
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) := by
    rw [map_pow]; exact hR.qU.pow _
  have hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      rw [smul_comm, hxe, smul_comm, hlaD.1]
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      calc Formalism.MainNotions.LiftingTheory.qp W ^ b i • W.γD T₂ δ x
          = W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • W.γD T₂ δ x := by rw [(W.AΔ.pow_mem hq (b i)) δ hδ]
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i • x) :=
            (Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ x).symm
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) := by rw [hxe]
        _ = W.γA δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • W.γD T₂ δ la :=
            Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ la
        _ = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by rw [(W.AΔ.pow_mem hp1 h₂) δ hδ, hlaD.2 δ hδ]
        _ = Formalism.MainNotions.LiftingTheory.qp W ^ b i • x := hxe.symm
  have hmx : Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x ∈ W.N T₂ := by
    rw [pow_add, mul_comm, mul_smul, hxe]; exact hm0

  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨⟨u, hu, hlq⟩, -, -⟩ := hER hA i ζ hζ
  have hu0 : PowerSeries.constantCoeff u ≠ 0 := (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero
  have hlevq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) =
      PowerSeries.X ^ (b i + η) * u ^ (b i + η) := by
    rw [map_pow, hlq, mul_pow, mul_comm]
  have hlev0 : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) ≠ 0 := by
    rw [hlevq]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hu.ne_zero)
  obtain ⟨dx, hdx, -⟩ := (hEU hA T₂ hT i ζ hζ).1 x _ hmx hlev0
  obtain ⟨m₀, hm₀⟩ := hdx.1
  have hLB : LB m₀ dx := hm₀
  have hrel : W.levN T₂ i ζ ⟨_, hmx⟩ = fun k => smulS (u ^ (b i + η)) dx (k - ((b i + η : ℕ) : ℤ)) := by
    have h1 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_smulA W T₂ i ζ hdx (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η))
    have h2 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_self W T₂ i ζ hmx
    rw [Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_unique W T₂ i ζ h2 h1, hlevq, smulS_mul hLB,
      smulS_X_pow (LB_smulS hLB _)]
  have hsh : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k =
      W.levN T₂ i ζ ⟨_, hmx⟩ (k + ((b i + η : ℕ) : ℤ)) := by
    intro k; rw [hrel]; simp

  have hyΔ : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (i - 2) y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T₂ (i - 2) ⟨hy, hyD.2⟩ hyD.1
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := Formalism.MainNotions.LiftingTheory.coreH_graded_of W h9 hA T₂ hT (i - 2) 0 y hyΔ
    refine ⟨x', hx'.1.1, hx'.1.2, ?_⟩
    simpa using he
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 2 1 (2 * H) σ := Or.inr ⟨rfl, rfl, rfl⟩
  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la ∈ W.N T₂ := by
    rw [mul_smul]; exact hm0
  have hmm : (⟨Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x, hmx⟩ : ↥(W.N T₂)) = ⟨_, hk⟩ := by
    apply Subtype.ext
    show Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x = (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la
    rw [pow_add, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ b i), mul_smul, hxe, mul_smul]
  obtain ⟨hneg, hcoef⟩ := hTH hA hl 2 1 (2 * H) σ hTC T₂ hT (i - 2) y la hy hyI htr ζ (η + 2 * H) η
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) hk (Or.inl ⟨hζ, rfl⟩)
  have e2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by push_cast; ring
  rw [e2] at hneg hcoef
  set c0 : TensorProduct Qp T₂.V BdR := (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T₂.V)
    ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) with hc0
  have hlevk : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) =
      PowerSeries.X ^ η * (u ^ η * W.lev i ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) := by
    rw [map_mul, map_pow (W.lev i ζ) (Formalism.MainNotions.LiftingTheory.qp W) η, hlq, mul_pow, mul_comm (u ^ η), mul_assoc]
  have hc00 : ∀ r : ℕ, r < η →
      PowerSeries.coeff r (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) = 0 := by
    intro r hr
    rw [hlevk, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

  have hg : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k ∈
      lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0 k := by
    intro k
    rw [hsh, hmm]
    unfold lemGAx_F
    by_cases hk0 : k + ((b i + η : ℕ) : ℤ) < 0
    · rw [hneg _ hk0]
      split_ifs <;> exact Submodule.zero_mem _
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, k + ((b i + η : ℕ) : ℤ) = r :=
        ⟨(k + ((b i + η : ℕ) : ℤ)).toNat, by omega⟩
      rw [hr]
      push_cast at hr
      split_ifs with h1 h2
      · rw [hcoef r (by omega), hc00 r (by omega), zero_smul]
        exact Submodule.zero_mem _
      · rw [hcoef r (by push_cast at h2; omega)]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · trivial
  have hF := Formalism.MainNotions.UnusedSlot80.LevR.laurent_div (lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0)
    (lemGAx_F_mono _ _ _) hm₀ (u ^ (b i + η)) (by rw [map_pow]; exact pow_ne_zero _ hu0) hg

  have hcy : W.cmp T₂ ⟨y, hy⟩ ∈ DcrisL PD T₂.ρ (W.emb (i - 2)) := by
    have h := W.cmp_letter T₂ (i - 2) ⟨y, hy⟩
    have e : ((letE (i - 2) : LetA O n) • (⟨y, hy⟩ : ↥(W.N T₂))) = ⟨y, hy⟩ := Subtype.ext hyD.1
    rwa [e] at h
  have hφy : (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩) ∈ DcrisL PD T₂.ρ (W.emb i) := by
    have h := Formalism.MainNotions.UnusedSlot80.UnivC.φVB_pow_letter W T₂ (i - 2) 2 hcy
    rwa [e2, Module.End.pow_apply] at h
  have hc0mem : ∀ k : ℤ, -(b i : ℤ) ≤ k →
      c0 ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ⊓ FilV PD (LL := LL) (V := T₂.V) (-k) := by
    intro k hk
    refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ ⟨_, hφy, rfl⟩, Submodule.smul_mem _ _ ?_⟩
    have hF0 : ιV PD (LL := LL) (V := T₂.V)
        ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) ∈
          FilV PD (LL := LL) (V := T₂.V) (b i : ℤ) := (Submodule.mem_inf.1 hFil).2
    exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ (b i : ℤ) by omega) hF0
  set τ := Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf W hA.1 i with hτ
  have hover : Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ i := by
    apply AlgHom.ext
    intro c
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i c
  have hjump : ∀ a, IsJumpV PD T₂.ρ τ a → -(η : ℤ) ≤ a := by
    intro a ha
    have := (hJ2 τ i hover a ha).1
    rwa [hMi] at this
  have hDi : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ FilV PD (LL := LL) (V := T₂.V) (-(η : ℤ)) := by
    intro z hz
    have h1 := Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T₂ i τ (Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i) hA.1.2 hz
    rw [← Formalism.MainNotions.UnusedSlot80.UnivF.fildR_eq_top_of (PD := PD) (ρ := T₂.ρ) τ (-(η : ℤ)) hjump] at h1
    exact (Submodule.mem_inf.1 h1).2

  have hxN : x ∈ W.N T₂ := by
    refine ((hEC hA T₂ hT i ζ hζ x dx hxD hdx).1 ⟨b i + η, hmx⟩).2 fun k => ?_
    have hk := hF k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero W T₂ i (-k)]
    unfold lemGAx_F at hk
    split_ifs at hk with h1 h2
    · rw [(Submodule.mem_bot LL).1 hk]; exact Submodule.zero_mem _
    · exact (Submodule.span_le.2 (Set.singleton_subset_iff.2 (hc0mem k (by omega)))) hk
    · refine Submodule.mem_inf.2 ⟨(hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k, ?_⟩
      refine Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ -(η : ℤ) by push_cast at h2; omega)
        (hDi ((hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k))
  exact ⟨x, hxN, hxD, hxe⟩

end LemGAx

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

