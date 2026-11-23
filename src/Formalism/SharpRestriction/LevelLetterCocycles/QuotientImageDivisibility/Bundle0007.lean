module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0006
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.JumpKernelCokernel.JumpShiftProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsInIInPNPowSmulSubMap
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n)

theorem qp_mem_AΔ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem hR.1 (W.AΔ.natCast_mem _)

theorem inI_qpphi [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {c : ZMod n} {kB : ℕ} (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ kB • W.φD T z ∈ W.N T)
    {x : W.DD T} (hxN : x ∈ W.N T) (hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x) (pad : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T c (((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x)) := by
  obtain ⟨hN, -⟩ := cmp_qpphi W T hs hR h3 hM hxN hxD.1
  set z := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x) with hz
  have hzN : z ∈ W.N T := by
    rw [hz, ← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ hN
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    rw [hz, map_smul, Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', ← W.φγ_comm, hxD.2 δ hδ,
      (W.AΔ.pow_mem (qp_mem_AΔ W hR) kB) δ hδ]
  have hzl : (letE c : LetA O n) • z = z := by
    rw [hz, osmul_comm W T, aself_comm W T, letter_phi W T c hxD.1]
  refine ⟨⟨hzl, hzΔ⟩, ⟨0, 0, by simpa using hzN⟩, ?_⟩
  obtain ⟨x', hx', he⟩ := hmod.2 z ⟨hzN, hzΔ⟩
  exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

theorem exists_inI_inPN_pow_smul_sub_map [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) {d1 d2 d3 : T₂.V ⊗[Qp] B}
    {s₁ s₂ bb hh e pad : ℕ} {k : ℤ}
    (h1 : (PD.p : LL) ^ s₁ • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y =
      (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) d1)
    (h2 : (PD.p : LL) ^ bb • d1 = φVB PD (LL := LL) (V := T₂.V) d2)
    (h3 : (PD.p : LL) ^ s₂ • d2 = (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) d3)
    (hG : (PD.p : LL) ^ k • φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) ∈
      Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    (hexp : (e : ℤ) + hh = pad + k + bb) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨n', hn'N, hmN, hn'D, hcmp⟩ := hG
  set x := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₁ n') with hxdef
  refine ⟨x, inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad, ?_⟩
  have hyN : y ∈ W.N T₂ := NDl_N W T₂ hy
  have hyl : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c y := NDl_DL W T₂ hy

  have hml : (letE (c - 1) : LetA O n) • W.map F n' = W.map F n' := by
    rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hn'D.1]
  obtain ⟨hqN, hqc⟩ := cmp_qpphi W T₂ hs hR h3₂ hM₂ hmN hml
  have hFx : W.map F x = ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₂ (W.map F n')) := by
    rw [hxdef, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, W.map_φ]
  have hFxN : W.map F x ∈ W.N T₂ := by
    rw [hFx, ← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hqN
  have hxI := inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad
  have hFxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F x) := by
    refine ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hxI.1.1], fun δ hδ => ?_⟩
    rw [← W.map_γ, hxI.1.2 δ hδ]
  have hpyN : ((PD.p : O) ^ (e + s₁ + s₂)) • y ∈ W.N T₂ := by
    rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hyN
  have hzmem : ((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c :=
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).sub_mem ((Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).smul_mem _ hy) ⟨hFxN, hFxD⟩
  refine ker_NDl W T₂ c h3₂ hmod₂ hR hzmem ?_

  have hsub : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y) - Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (W.map F x) := by
    have := cmpD_add W T₂ ((W.N T₂).sub_mem hpyN hFxN) hFxN
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub, sub_eq_zero, cmpD_osmul W T₂ _ hyN, hFx, cmpD_osmul W T₂ _ hqN, hqc,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hmN, ← hcmp, map_pow, map_pow, map_natCast]

  have hsc : (PD.p : LL) ^ e * (PD.p : LL) ^ hh = (PD.p : LL) ^ bb * ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hp,
      ← zpow_add₀ hp, ← zpow_add₀ hp]
    congr 1
    omega
  have key : (PD.p : LL) ^ (e + s₂) • d1 = ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) •
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) := by
    apply smul_right_injective _ (pow_ne_zero bb hp)
    simp only
    rw [smul_comm, h2, pow_add, mul_smul, ← map_smul, h3, map_smul, smul_smul, smul_smul, hsc]
  rw [pow_add, pow_add, mul_smul, mul_smul, smul_comm ((PD.p : LL) ^ s₁), h1, ← mul_smul,
    ← pow_add, smul_comm, ← map_smul, key, map_smul, map_smul, smul_smul]
  simp only [smul_smul]
  congr 1
  ring

end Core

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem exists_X_pow_mul (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (w : ℕ) (u : PowerSeries LL), PowerSeries.constantCoeff u ≠ 0 ∧ f = PowerSeries.X ^ w * u := by
  have hex : ∃ w, PowerSeries.coeff w f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (PowerSeries.ext fun w => by simpa using h w)
  obtain ⟨w, h1, hmin⟩ : ∃ w, PowerSeries.coeff w f ≠ 0 ∧ ∀ m < w, PowerSeries.coeff m f = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      push Not at this
      exact this⟩
  have hdvd : PowerSeries.X ^ w ∣ f := PowerSeries.X_pow_dvd_iff.2 hmin
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨w, u, ?_, hu⟩
  rw [hu, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
  exact h1

theorem smulS_div {m : ℤ} {e : ℤ → V} (he : LB m e) (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_inj {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (f : PowerSeries LL)
    (hf : f ≠ 0) (h : smulS f d = smulS f d') : d = d' := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  have h0 : smulS (PowerSeries.X ^ w * u) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS u (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + w)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') u hu
  rw [h1] at h2
  have h3 : smulS u⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

theorem smulS_comm {m : ℤ} {d : ℤ → V} (hd : LB m d) (f g : PowerSeries LL) :
    smulS f (smulS g d) = smulS g (smulS f d) := by
  rw [← smulS_mul hd, ← smulS_mul hd, mul_comm]

theorem smulS_mem {m : ℤ} {d : ℤ → V} (hd : LB m d) (D : Submodule LL V) (hD : ∀ k, d k ∈ D)
    (f : PowerSeries LL) (k : ℤ) : smulS f d k ∈ D := by
  have := Dg_smulS (Fil := fun _ : ℤ => D) (fun _ _ _ => le_rfl) hd (s := 0)
    (fun k => hD k) f k
  simpa using this

end Div

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem conv_eq {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv f d = smulS f d := rfl

theorem p_ne_zero_LL (W' : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h
  have := W'.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem eat_qp :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]

theorem expRing_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := by
  intro hA i ζ hζ
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨u₀, hu₀, hq⟩ := MC.lev_q_eq W i hζ hp
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_qp] at hw

  have hqp : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) =
      (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) * PowerSeries.X := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hq]
    ring
  have hunit : IsUnit (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) :=
    ((Units.isUnit _).map _).mul
      (PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hu₀))
  have hcq : PowerSeries.constantCoeff (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W)) = 0 := by
    rw [hqp, map_mul, PowerSeries.constantCoeff_X, mul_zero]
  have hcpi : PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
    rw [e, map_add (f := _), map_natCast, map_add (f := _), map_natCast] at hcq
    linear_combination hcq
  refine ⟨⟨_, hunit, hqp⟩, hcpi, ?_⟩

  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.1
  rw [eat_qp] at hw'
  have hp1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hcφ : PowerSeries.constantCoeff (W.lev i ζ (W.φA W.π₀)) = 0 := by
    rw [hw', map_mul, map_mul, map_pow, map_mul, map_mul, map_pow, hcq,
      zero_pow (by omega), mul_zero]
  have e2 : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA W.π₀ + ((PD.p : ℕ) : LetA O n) := by
    simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, map_natCast]
  rw [e2, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _), map_natCast, map_add (f := _), hcφ, zero_add,
    map_natCast]
  exact isUnit_iff_ne_zero.2 hp

def GamN : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : ↥(W.N T)) (hx : W.γ T (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γ T x, hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T i ζ x k

def GamA : Prop :=
  ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
    W.lev i ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ f)

theorem gam_of_tie (hs : W.s = 1) {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamN W ∧ GamA W := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    simp only [Nat.cast_one]
    rw [W.gam_gen, hs, Nat.cast_one]
  refine ⟨fun T hT i ζ hζ x hx k => ?_, fun i ζ hζ f => ?_⟩
  · rw [C.levN_eq, C.levN_eq]
    have e := C.levB_Γ T hT W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) x hx k
    have e' : (⟨W.γ T x, hx⟩ : ↥(W.N T)) = ⟨W.γD T W.gam x, hx⟩ := rfl
    rw [e', e, map_smul]
  · exact C.lev_Γ W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) f

end Exp

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.GammaLevelsExpansion
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Gam

variable (W : LocWach PD LL O v n)

theorem cc_φ₀ (f : PowerSeries O) : constantCoeff (W.φ₀ f) = constantCoeff f := by
  have e := PowerSeries.eq_X_mul_shift_add_const f
  have hC : ∀ r : O, W.φ₀ (C r) = C r := fun r => by
    have := W.φ₀.commutes r
    rwa [show (algebraMap O (PowerSeries O) r) = C r from rfl] at this
  conv_lhs => rw [e]
  rw [map_add (f := _), map_mul, W.φ₀_X, hC]
  simp

theorem gam_q [IsDomain O] (g : W.Gam) :
    ∃ v : LetA O n, W.γA g W.q = W.q * v ∧ IsUnit v := by
  obtain ⟨V, hV⟩ := PowerSeries.X_dvd_iff.mpr (W.γ₀_X g).1
  have hcV : constantCoeff V = (W.χΓ g : O) := by
    have := (W.γ₀_X g).2
    rw [hV, PowerSeries.coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at this
    exact this
  have hVu : IsUnit V := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hcV]; exact Units.isUnit _
  have hφVu : IsUnit (W.φ₀ V) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, cc_φ₀, hcV]; exact Units.isUnit _
  have key : W.q₀ * W.φ₀ V = V * W.γ₀ g W.q₀ := by
    have h := W.γ₀_comm g PowerSeries.X
    rw [hV, map_mul, W.φ₀_X, map_mul, hV] at h
    have h2 : PowerSeries.X * (W.q₀ * W.φ₀ V) = PowerSeries.X * (V * W.γ₀ g W.q₀) := by
      rw [← mul_assoc, ← mul_assoc]; exact h
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h2
  obtain ⟨Vu, hVu'⟩ := hVu
  refine ⟨fun _ => W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O), ?_, ?_⟩
  · funext i
    show W.γ₀ g W.q₀ = W.q₀ * (W.φ₀ V * ((Vu⁻¹ : (PowerSeries O)ˣ) : PowerSeries O))
    rw [← mul_assoc, key, ← hVu', mul_comm (Vu : PowerSeries O), mul_assoc, Units.mul_inv, mul_one]
  · refine Pi.isUnit_iff.2 fun _ => hφVu.mul (Units.isUnit _)

end Gam

section ArithmeticCylinders

theorem cc_rescale {LL' : Type} [Field LL'] (χ : LL') (u : PowerSeries LL') :
    constantCoeff (PowerSeries.rescale χ u) = constantCoeff u := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, pow_zero, one_mul]

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gamma_levels_expansion [IsDomain O] (hs : W.s = 1) (c : ZMod n) (ζ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ f))
    (u : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu0 : constantCoeff u ≠ 0)
    {K : ℕ} {w : W.DD T} (hwN : W.Q ^ K • w ∈ W.N T) (hγw : W.γ T w - w ∈ W.N T) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ ⟨W.Q ^ K • w, hwN⟩ = smulS ((X * u) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) := by
  have hQ : W.Q = W.q := Q_eq_q W hs
  set x : ↥(W.N T) := ⟨W.Q ^ K • w, hwN⟩ with hxdef
  obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ x
  obtain ⟨d, hdLB, hde⟩ := div_exists (m := m₀) hm₀ u hu0 K
  refine ⟨d, ⟨_, hdLB⟩, hde.symm, ?_⟩

  obtain ⟨vv, hvv, hvu⟩ := gam_q W W.gam
  obtain ⟨vU, hvU⟩ := hvu
  set v' : LetA O n := ((vU⁻¹ : (LetA O n)ˣ) : LetA O n)

  have hlv : W.lev c ζ vv = PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ := by
    have h1 := hγA W.q
    rw [hvv, map_mul, hu, map_mul, PowerSeries.rescale_X] at h1
    have h2 : X * (u * W.lev c ζ vv) = X * (PowerSeries.C χ * PowerSeries.rescale χ u) := by
      rw [← mul_assoc, h1]; ring
    have h3 := mul_left_cancel₀ PowerSeries.X_ne_zero h2
    rw [← h3, mul_comm u, mul_assoc, PowerSeries.mul_inv_cancel _ hu0, mul_one]
  have hv'vv : v' * vv = 1 := by rw [← hvU]; exact Units.inv_mul vU
  have hlv' : W.lev c ζ v' = PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ := by
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have h1 : W.lev c ζ vv * W.lev c ζ v' = 1 := by
      rw [← map_mul, mul_comm, hv'vv, map_one]
    rw [hlv] at h1
    have hAA : (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
        (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹) = 1 := by
      calc (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
            (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)
          = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) * (u * u⁻¹) *
            ((PowerSeries.rescale χ u)⁻¹ * PowerSeries.rescale χ u) := by ring
        _ = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hχ0, map_one, PowerSeries.mul_inv_cancel _ hu0,
            PowerSeries.inv_mul_cancel _ hr0]
          ring
    calc W.lev c ζ v' = ((PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹)) * W.lev c ζ v' := by rw [hAA, one_mul]
      _ = (PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹) *
          (PowerSeries.C χ * PowerSeries.rescale χ u * u⁻¹ * W.lev c ζ v') := by ring
      _ = _ := by rw [h1, mul_one]

  have hγx : W.γ T (W.Q ^ K • w) ∈ W.N T := W.N_Γ T W.gam _ hwN
  have hγw' : W.Q ^ K • W.γ T w = v' ^ K • W.γ T (W.Q ^ K • w) := by
    have e1 : W.γ T (W.Q ^ K • w) = W.γA W.gam (W.Q ^ K) • W.γ T w :=
      Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T W.gam _ w
    rw [e1, map_pow, hQ, hvv, smul_smul]
    congr 1
    calc W.q ^ K = (v' * vv) ^ K * W.q ^ K := by rw [hv'vv, one_pow, one_mul]
      _ = v' ^ K * (W.q * vv) ^ K := by ring
  have hQγN : W.Q ^ K • W.γ T w ∈ W.N T := by
    rw [hγw']; exact (W.N T).smul_mem _ hγx
  have hlevγ : W.levN T c ζ ⟨W.Q ^ K • W.γ T w, hQγN⟩ = smulS ((X * u) ^ K) (resc χ d) := by
    have e2 : (⟨W.Q ^ K • W.γ T w, hQγN⟩ : ↥(W.N T)) = v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩ :=
      Subtype.ext hγw'
    have hLBγ : LB m₀ (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) := fun k hk => by
      rw [hγN _ hwN hγx k, hm₀ k hk, smul_zero]
    rw [e2]
    have e3 : W.levN T c ζ (v' ^ K • ⟨W.γ T (W.Q ^ K • w), hγx⟩) =
        smulS (W.lev c ζ (v' ^ K)) (W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩) :=
      funext fun k => W.levN_smul T c ζ _ _ k
    have e4 : W.levN T c ζ ⟨W.γ T (W.Q ^ K • w), hγx⟩ = resc χ (W.levN T c ζ x) :=
      funext fun k => hγN _ hwN hγx k
    rw [e3, e4, ← hde, ← smulS_rescale hdLB χ hχ0, ← smulS_mul (LB_resc hdLB χ), map_pow, hlv']
    congr 1
    rw [map_pow, map_mul, PowerSeries.rescale_X, ← mul_pow]
    congr 1
    have hr0 : constantCoeff (PowerSeries.rescale χ u) ≠ 0 := by
      rw [cc_rescale]; exact hu0
    have hC : PowerSeries.C χ⁻¹ * PowerSeries.C χ = (1 : PowerSeries LL) := by
      rw [← map_mul, inv_mul_cancel₀ hχ0, map_one]
    calc PowerSeries.C χ⁻¹ * u * (PowerSeries.rescale χ u)⁻¹ *
          (PowerSeries.C χ * X * PowerSeries.rescale χ u)
        = (PowerSeries.C χ⁻¹ * PowerSeries.C χ) *
          (PowerSeries.rescale χ u * (PowerSeries.rescale χ u)⁻¹) * (X * u) := by ring
      _ = X * u := by rw [hC, PowerSeries.mul_inv_cancel _ hr0]; ring

  have hdiffN : W.Q ^ K • (W.γ T w - w) ∈ W.N T := (W.N T).smul_mem _ hγw
  have hg : W.levN T c ζ ⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ =
      smulS ((X * u) ^ K) (W.levN T c ζ ⟨W.γ T w - w, hγw⟩) := by
    have e5 : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) = W.Q ^ K • ⟨W.γ T w - w, hγw⟩ := rfl
    rw [e5]
    have := funext fun k => W.levN_smul T c ζ (W.Q ^ K) ⟨W.γ T w - w, hγw⟩ k
    rw [this, map_pow, hQ, hu]
    rfl
  have hsplit : (⟨W.Q ^ K • (W.γ T w - w), hdiffN⟩ : ↥(W.N T)) =
      ⟨W.Q ^ K • W.γ T w, hQγN⟩ - x := Subtype.ext (by simp [hxdef, smul_sub])
  rw [hsplit, map_sub, hlevγ] at hg
  obtain ⟨m₁, hm₁⟩ := W.levN_supp T c ζ ⟨W.γ T w - w, hγw⟩
  have hLBr := LB_resc hdLB χ
  have heq : resc χ d - d = W.levN T c ζ ⟨W.γ T w - w, hγw⟩ := by
    have hx' : W.levN T c ζ x = smulS ((X * u) ^ K) d := hde.symm
    rw [hx', ← smulS_sub hLBr hdLB] at hg
    exact div_unique (m := min (m₀ - K) m₁) (LB_mono (LB_sub hLBr hdLB) (min_le_left _ _))
      (LB_mono hm₁ (min_le_right _ _)) u hu0 K hg
  intro i
  have h := hLv ⟨W.γ T w - w, hγw⟩ i
  rw [← heq] at h
  simpa [resc, sub_smul] using h

end ArithmeticCylinders

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

