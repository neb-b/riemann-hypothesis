module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IndepPhiCmp
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section PhiInj

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem φVB_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj hab

end PhiInj

section CritB2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem isExp_zero (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (0 : W.DD T) (fun _ => 0) := by
  have h0 : (1 : LetA O n) • (0 : W.DD T) ∈ W.N T := by rw [smul_zero]; exact (W.N T).zero_mem
  refine ⟨⟨0, fun _ _ => rfl⟩, 1, h0, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • (0 : W.DD T), h0⟩ : ↥(W.N T)) = 0 := Subtype.ext (smul_zero _)
  rw [e, map_zero, conv_eq]
  simp [smulS]

theorem pullJ_exp (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) :
    ∀ x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1, ∃ d : ℤ → T.V ⊗[Qp] BdR,
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d ∧ ∀ k : ℤ, k < 0 → d k = 0 := by
  have hs : W.s = 1 := hA.2.1
  obtain ⟨hN, hAg⟩ := gam_of_tie W hs C
  obtain ⟨-, -, hAdd, -, -, -, -⟩ := expRules_of W h4 hN hAg hA T hT i ζ hζ
  intro x hx
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hy, hyD⟩, rfl⟩ := hx
    rw [pow_one]
    obtain ⟨d, hd, hn, -⟩ := phi_exp W hs C h4W T hT i hζ y hy hyD.1
    exact ⟨d, hd, hn⟩
  | zero => exact ⟨fun _ => 0, isExp_zero W T i ζ, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hn⟩ := hx
    obtain ⟨e, he, hn'⟩ := hy
    exact ⟨d + e, hAdd _ _ _ _ hd he, fun k hk => by simp [hn k hk, hn' k hk]⟩
  | smul a x _ hx =>
    obtain ⟨d, hd, hn⟩ := hx
    exact ⟨smulS (W.lev i ζ a) d, isExp_smulA W T i ζ hd a, fun k hk => LB_smulS hn _ k hk⟩

theorem indep_phi_cmp (hdom : IsDomain O) (hFr : IsFractionRing O LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T)
    (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (c : Fin r → LL)
    (hc : ∑ m, c m • ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
      (W.cmp T ⟨e m, (he.1 m).1⟩)) = 0) : c = 0 := by
  haveI := hdom
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  have hsum : ∑ m, c m • W.cmp T ⟨e m, (he.1 m).1⟩ = 0 := by
    apply φVB_inj PD (LL := LL) (V := T.V)
    apply Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_zero, map_sum, map_sum]
    simpa [map_smul] using hc
  obtain ⟨⟨dd, hdd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r)) c
  choose o ho using fun m => hint m (Finset.mem_univ m)
  have hdne : algebraMap O LL dd ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdd
  set z : W.DD T := ∑ m, o m • e m with hz
  have hzN : z ∈ W.N T := Submodule.sum_mem _ fun m _ => by
    rw [← algebraMap_smul (LetA O n) (o m) (e m)]; exact (W.N T).smul_mem _ (he.1 m).1
  have hzD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [smul_comm, (he.1 m).2.1]
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (he.1 m).2.2 δ hδ]
  have hcz : W.cmp T ⟨z, hzN⟩ = 0 := by
    have e1 : (⟨z, hzN⟩ : ↥(W.N T)) = ∑ m, o m • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp [hz, Submodule.coe_sum])
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [W.cmp_smul]
    calc ∑ m, algebraMap O LL (o m) • W.cmp T ⟨e m, (he.1 m).1⟩
        = ∑ m, algebraMap O LL dd • (c m • W.cmp T ⟨e m, (he.1 m).1⟩) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ho m, Algebra.smul_def, mul_smul]
      _ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]
  have hPN := ker_NDl W T i h3 hmod hR (x := z) ⟨hzN, hzD⟩
    (by unfold Formalism.MainNotions.ArcLiftingSetup.cmpD; rw [dite_eq_left hzN]; exact hcz)
  obtain ⟨y, hy, hyΔ, hzy⟩ := hPN
  rw [pow_one] at hzy
  have hyl : (letE i : LetA O n) • y = y := by
    apply RL.pi0_pow_smul_injective W T hR.2.2.1 1
    rw [pow_one, smul_comm, ← hzy, hzD.1]
  obtain ⟨b, hb, -⟩ := he.2 y hy ⟨hyl, hyΔ⟩
  have rep1 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C (o m)) • e m := by
    rw [hz]
    exact Finset.sum_congr rfl fun m _ => by rw [evalZero_C, algebraMap_smul]
  have rep2 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X * b m) • e m := by
    rw [hzy, hb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul, evalZero_mul W hR, evalZero_X_eq_pi0 W hR]
  have heq := (he.2 z hzN hzD).unique rep1 rep2
  funext m
  have h0 : o m = 0 := by
    have := congrArg (fun f => PowerSeries.constantCoeff (f m)) heq
    simpa using this
  have : algebraMap O LL dd * c m = 0 := by
    rw [← Algebra.smul_def, ← ho m, h0, map_zero]
  exact (mul_eq_zero.1 this).resolve_left hdne

end CritB2

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevBasicsOf
section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Fin

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F] [Algebra ℤ_[PD.p] O]

theorem evAt_γ (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O)) (a : ZMod n) (s : ℕ)
    (g : W.Gam) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ (W.γA g x) = evAt hlm F a s (powR F PD.p s (redU PD.p s (z g)) ζ) x := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have h0 := (W.γ₀_X g).1
  have h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) := by
    rw [(W.γ₀_X g).2, hz g]
  have hbs := Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W)
    (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1
  set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA
  have hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  rw [evAt_apply, evAt_apply]
  have e1 : (W.γA g x) a = W.γ₀ g (x a) := rfl
  have huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1 := by
    have e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1 := by
      rw [← hbs]; ring
    rw [e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]
  rw [e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0,
    evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]
  exact evR_congr PD.p (s + 1) hlm hyA _ rfl _


omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert (redU PD.p s (z W.gam))
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ := by
  obtain ⟨z0, hz0, hv⟩ := hγz
  have hzg : z W.gam = z0 := Units.ext (hZinj (by rw [hz, hz0]))
  have hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at hv; exact zero_ne_one hv
  have hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])
    rwa [pow_one] at this
  have hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2} := by
    intro h
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h
    rw [hv] at this; omega
  have htop := hGen PD.p hp2 s z0 hu1 hu2

  have hl2 := hpF.out.two_le
  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = PD.p - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

  have hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1 := by
    intro δ
    apply Units.ext
    apply hZinj
    rw [Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow,
      hexp δ δ.2, map_one]
    simp
  let zΔ : ↥W.DelF → DeltaT PD.p := fun δ => ⟨z δ, hzΔ δ⟩
  have hinj : Function.Injective zΔ := by
    intro δ δ' h
    have h1 : z δ = z δ' := congrArg Subtype.val h
    have h2 : W.χΓ δ = W.χΓ δ' := Units.ext (by rw [← hz, ← hz, h1])
    exact Subtype.ext (W.χΓ_inj h2)
  haveI : NeZero (PD.p - 1) := ⟨by omega⟩
  let e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p]) :=
    Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm
  haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm
  have hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF := by
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hcard]
    exact card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  rw [eq_top_iff, ← htop]
  apply Subgroup.closure_mono
  intro u hu
  rcases Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩
  · exact Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))
  · obtain ⟨δ, hδ⟩ := hsurj d
    refine Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩
    show redU PD.p s (z δ) = redU PD.p s d.1
    rw [← hδ]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
theorem gen_of' (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert ((fun g => redU PD.p s (z g)) W.gam)
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ :=
  gen_of W z hz hZinj hγz hcard hp2 hGen s

def levBasics_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsAlgClosed F] [CharZero F]
    (hinjF : Function.Injective (algebraMap O F))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hχ : ∀ g : W.Gam, ∃ z : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (a : ZMod n) (s : ℕ) :
    LevBasics W a s where
  F := F
  fF := inferInstance
  algOF := inferInstance
  inj := hinjF
  hp := Nat.cast_ne_zero.2 hpF.out.ne_zero
  root := exists_prim _ (pow_pos hpF.out.pos _)
  ev := evAt hlm F a s
  ev_O ζ x := by
    rw [evAt_apply]
    exact (evR PD.p (s + 1) hlm (rs_root F s ζ)).commutes x
  ev_letE ζ := by
    rw [evAt_apply]
    simp [letE]
  ev_π ζ := by
    rw [evAt_apply]
    exact evR_X PD.p (s + 1) hlm (rs_root F s ζ)
  ev_ps ζ := (evAt_ps_iff W hlm F hR a s s ζ).2 rfl
  ev_pt t ht ζ := fun h => ht ((evAt_ps_iff W hlm F hR a s t ζ).1 h)
  σ g := redU PD.p s (Classical.choose (hχ g))
  ev_γ g ζ x := evAt_γ W hlm F (fun g => Classical.choose (hχ g))
    (fun g => Classical.choose_spec (hχ g)) a s g ζ x
  gen := gen_of' W (fun g => Classical.choose (hχ g)) (fun g => Classical.choose_spec (hχ g))
    hZinj hγz hcard hp2 hGen s

end Fin

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end

