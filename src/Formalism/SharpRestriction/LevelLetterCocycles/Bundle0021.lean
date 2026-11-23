module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
public import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]

theorem OL_le {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) (x : ↥(OL LL)) :
    IntermediateField.inclusion hLL (x : ↥LL.1) ∈ OL LL' := by
  obtain ⟨p, hp, hx⟩ := x.2
  exact ⟨p, hp, by
    have := congrArg (IntermediateField.inclusion hLL) hx
    rw [map_zero] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    rfl⟩

def jO {LL LL' : FinExt l} (hLL : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion hLL (x : ↥LL.1), OL_le hLL x⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem isFrac_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)

end Formalism.MainNotions.UnusedSlot80.BCF
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemGA0ConvVanish
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

section LemGA0

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGA0_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := Qp) (M := T.V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lemGA0_one_root (l : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (l ^ j) := ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem lemGA0_cc_letπ (W : LocWach PD LL O v n) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (lemGA0_one_root PD.p)
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add (f := _), map_one, hE0, one_mul] at h
  linear_combination h

theorem lemGA0_cc_π₀₁ (W : LocWach PD LL O v n) (hcard : W.DelF.card = PD.p - 1) (hp : 1 ≤ PD.p) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  unfold LocWach.π₀₁
  have h2 : ∀ δ, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = (0 : O) := fun δ => (W.γ₀_X δ).1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sub, map_one, map_natCast, map_sum, h2, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hcard]
  push_cast [Nat.cast_sub hp]
  ring

theorem lemGA0_cc_π₀ (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have e : W.π₀ = (letπ : LetA O n) * (fun _ => g) := by
    funext j
    show W.π₀₁ = PowerSeries.X * g
    exact hg
  rw [e, map_mul, map_mul, lemGA0_cc_letπ, zero_mul]

theorem lemGA0_cc_qp (W : LocWach PD LL O v n) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W)) = (PD.p : LL) := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add (f := _), map_natCast, map_add (f := _), lemGA0_cc_π₀ W i h0, map_natCast, zero_add]

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem lemGA0_cc_pk (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (i : ZMod n) (h0 : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.pk W 1)) = (PD.p : LL) := by
  have e : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA (Formalism.MainNotions.LiftingTheory.qp W) := by
    unfold Formalism.MainNotions.LiftingTheory.pk; rw [pow_one]
  rw [e, C.lev_φ i 1 (lemGA0_one_root PD.p) (Formalism.MainNotions.LiftingTheory.qp W), one_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, lemGA0_cc_qp W (i - 1) h0]

theorem lemGA0_conv_vanish {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hsupp : ∃ m : ℤ, ∀ k < m, d k = 0)
    (hneg : ∀ r : ℤ, r < 0 → ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) = 0) :
    ∀ r : ℤ, r < 0 → d r = 0 := by
  obtain ⟨m, hm⟩ := hsupp
  have key : ∀ t : ℕ, ∀ r : ℤ, r < m + t → r < 0 → d r = 0 := by
    intro t
    induction t with
    | zero => intro r hr _; exact hm r (by simpa using hr)
    | succ t ih =>
      intro r hr hr0
      by_cases hlt : r < m + t
      · exact ih r hlt hr0
      · have hs : ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (r - j) =
            PowerSeries.coeff 0 f • d (r - ((0 : ℕ) : ℤ)) := by
          apply finsum_eq_single _ 0
          intro j hj
          rw [ih (r - j) (by push_cast at hr; omega) (by omega), smul_zero]
        have h := hneg r hr0
        rw [hs, Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
        have h' := congrArg (fun z => (PowerSeries.constantCoeff f)⁻¹ • z) h
        simpa [inv_smul_smul₀ hf] using h'
  intro r hr
  by_cases h : r < m
  · exact hm r h
  · apply key (r - m + 1).toNat r _ hr
    rw [Int.toNat_of_nonneg (by omega)]
    omega

theorem lemGA0_conv_zero {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M)
    (hd : ∀ r : ℤ, r < 0 → d r = 0) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (0 - j) = PowerSeries.constantCoeff f • d 0 := by
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hd _ (by have : (0 : ℕ) < j := Nat.pos_of_ne_zero hj; omega), smul_zero]

theorem lemGA0_of_tools [NeZero n] (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (hT : Formalism.MainNotions.CrystallineLiftingInputs.THor W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    LemGA_0 W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD la hla x hx hxD hxe
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hcr : IsCrys PD T₂.ρ := by unfold Formalism.MainNotions.LiftingTheory.Sur at hsur; exact hsur.2.1
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
    have hpos : 0 < PD.p := by omega
    have : NeZero PD.p := ⟨hpos.ne'⟩
    exact (hζ.neZero').out

  have hfr : finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h9K⟩ := h9 T₂ hcr hA.2.1 hA.2.2
  rw [hfr, Nat.div_one] at hcard
  have h0 : PowerSeries.constantCoeff W.π₀₁ = 0 := lemGA0_cc_π₀₁ W hcard (by omega)
  obtain ⟨-, hmod⟩ := h9K hfr
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := hmod.2 y ⟨hy, hyD.2⟩
    exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la ∈ W.N T₂ := by
    rw [pow_zero, one_mul, ← hxe]
    exact Submodule.smul_mem _ _ hx
  have hTH := hT hA hp11 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η))
    (Or.inr ⟨rfl, rfl, rfl⟩) T₂ hcr (i - 2) y la hy hyI hla.1 1 ((PD.p - 1) * 1) 0
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) hk (Or.inr ⟨rfl, rfl⟩)
  have hneg := hTH.1
  have h0v := hTH.2 0 (by omega)
  have hi2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by rw [Nat.cast_ofNat, sub_add_cancel]
  have hsub : (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S)) • la, hk⟩ : ↥(W.N T₂)) =
      (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, pow_zero, one_mul]
    exact hxe.symm
  rw [hi2, hsub] at hneg h0v
  rw [Nat.cast_zero] at h0v

  have hsm : ∀ r : ℤ, W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) r =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) •
        W.levN T₂ i 1 ⟨x, hx⟩ (r - j) :=
    fun r => W.levN_smul T₂ i 1 _ _ r
  have hccb : PowerSeries.constantCoeff (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) = (PD.p : LL) ^ b i := by
    rw [map_pow, map_pow, lemGA0_cc_qp W i h0]
  have hxneg : ∀ r : ℤ, r < 0 → W.levN T₂ i 1 ⟨x, hx⟩ r = 0 :=
    lemGA0_conv_vanish (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) (W.levN T₂ i 1 ⟨x, hx⟩)
      (by rw [hccb]; exact pow_ne_zero _ hp0) (W.levN_supp T₂ i 1 _)
      (fun r hr => by rw [← hsm r]; exact hneg r hr)
  have he : ((letE i : LetA O n) • (⟨x, hx⟩ : ↥(W.N T₂))) = ⟨x, hx⟩ := Subtype.ext hxD.1
  have hL : W.levN T₂ i 1 ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (⟨x, hx⟩ : ↥(W.N T₂))) 0 =
      (PD.p : LL) ^ b i • ιV PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨x, hx⟩) := by
    rw [hsm, lemGA0_conv_zero _ _ hxneg, hccb, C.levN_eq, ← C.cmp_eq T₂ hcr i, he]
  have hcch : PowerSeries.coeff 0 (W.lev i 1 (Formalism.MainNotions.LiftingTheory.qp W ^ 0 * Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S))) =
      (PD.p : LL) ^ (b (i - 1) + S) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, pow_zero, one_mul, map_pow, map_pow,
      lemGA0_cc_pk W C i h0]
  have hmain : (PD.p : LL) ^ b i • W.cmp T₂ ⟨x, hx⟩ =
      (PD.p : LL) ^ (b (i - 1) + S) • ((PD.p : LL) ^ lemG_sig PD.p (hpar n b S + η) •
        (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) := by
    apply lemGA0_ιV_inj (PD := PD) T₂
    rw [map_smul, map_smul, map_smul, ← hL, h0v, hcch]
  rw [← inv_smul_smul₀ (pow_ne_zero (b i) hp0) (W.cmp T₂ ⟨x, hx⟩), hmain, smul_smul, smul_smul,
    zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
  congr 1
  ring

end LemGA0

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalShareBounds
section
noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

variable {D : D7}

theorem wtOf_off (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp


end Formalism.MainNotions.N.LocalShareBounds
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_letS (c : ZMod n) (x : W.DD T) : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_NcS (c : ZMod n) (x : W.DD T) :
    x ∈ NcS W T c ↔ x ∈ W.N T ∧ (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold NcS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS, mem_letS, and_assoc]

theorem mem_PiNS (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold PiNS
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS]
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN
  rw [Submodule.mem_map]
  rfl

theorem mem_LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ LamPS W T Eπ h' c ↔ Eπ ^ h' • x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) ∧
      (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    mem_DelS, mem_letS, and_assoc]
  rfl

theorem mem_InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ InvS W T π' Eπ h' k c ↔ x ∈ LamPS W T Eπ h' c ∧ W.γD T W.gamK x - x ∈ PiNS W T π' k := by
  unfold InvS
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem PiNS_le_N (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ W.N T := by
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := (mem_PiNS W T π' k x).1 hx
  exact (W.N T).smul_mem _ hy

theorem γD_letE (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem φD_letE (c : ZMod n) (x : W.DD T) :
    W.φD T ((letE (c - 1) : LetA O n) • x) = (letE c : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]

theorem map_letA_smul {T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x :=
  Formalism.MainNotions.LiftingTheory.wmap_map_smul W f a x

theorem map_comp_zero {T' T'' : LocLat G Qp LL O} (ι : LatHom T.L T'.L) (π : LatHom T'.L T''.L)
    (h0 : ∀ y, π.f (ι.f y) = 0) (x : W.DD T) : W.map π (W.map ι x) = 0 := by
  rw [← W.map_comp]
  have hext : ∀ g₁ g₂ : LatHom T.L T''.L, g₁.f = g₂.f → g₁ = g₂ := by
    rintro ⟨f1, _, _, _⟩ ⟨f2, _, _, _⟩ h
    cases h
    rfl
  have hg : latAdd (latComp π ι) (latComp π ι) = latComp π ι := by
    apply hext
    ext y
    simp [latAdd, latComp, h0]
  have := W.map_latAdd (latComp π ι) (latComp π ι) x
  rw [hg] at this
  exact left_eq_add.mp this

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TwGuard
section
noncomputable section

namespace Formalism.MainNotions

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem vAdd_pos_iff_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ≠ 0) : 0 < vAdd la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast ha
  have hle := la.valuation_le_one (K := K) a
  have hlt : la.valuation K (algebraMap (𝓞 K) K a) < 1 ↔ a ∈ la.asIdeal := la.valuation_lt_one_iff_mem a
  unfold vAdd
  constructor
  · intro h
    by_contra hm
    have h1 : la.valuation K (a : K) = 1 := le_antisymm hle (not_lt.1 fun h' => hm (hlt.1 h'))
    rw [h1] at h
    simp at h
  · intro hm
    have h2 : la.valuation K (a : K) < 1 := hlt.2 hm
    have h3 := (WithZero.log_lt_log h0 one_ne_zero).2 h2
    simp at h3
    omega

end Formalism.MainNotions

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add (f := _), map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
end
end

