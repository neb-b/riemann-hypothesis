module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroup
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem avg_eig : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V,
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  intro G V _ _ _ _ _ π hπ H θ hD w
  classical
  let Hs : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  have hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1 := fun a ha => by
    rw [← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]
  have hθ0 : ∀ a ∈ H, θ a ≠ 0 := fun a ha h0 => by
    have := hθinv a ha; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hπmul : ∀ a b : G, π (a * b) w = π a (π b w) := fun a b => by rw [map_mul]; rfl
  let T : Subgroup Hs :=
    { carrier := {j | π j w = θ j • w}
      one_mem' := by simp [hD.val_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rw [hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        have h1 : w = θ a • π (a : G)⁻¹ w := by
          rw [← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]; rfl
        have h2 : θ (a : G)⁻¹ = (θ a)⁻¹ := eq_inv_of_mul_eq_one_left (hθinv a a.2)
        rw [h2]
        conv_rhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }
  haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact
  have hopen : IsOpen (T : Set Hs) := by
    apply Subgroup.isOpen_of_mem_nhds T (g := 1)
    rw [nhds_subtype_eq_comap, Filter.mem_comap]
    obtain ⟨U, hU, hUθ⟩ := hD.near
    refine ⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩
    rintro j ⟨hjU, hjw⟩
    show π j w = θ j • w
    rw [hjw, hUθ _ hjU j.2, one_smul]
  haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen
  haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _
  let f : Hs → V := fun j => (θ j)⁻¹ • π j w
  have hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hb : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = s at hab hb
    subst hb
    have hs : π s w = θ s • w := hab
    simp only [f, Subgroup.coe_mul]
    rw [hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hθ0 s s.2), mul_one]
  have hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a) := by
    intro h a
    simp only [f, Subgroup.coe_mul]
    rw [map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (hθ0 h h.2), one_mul]
  let rep : Hs ⧸ T → Hs := fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out
  have hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q := by
    intro q
    simp only [rep]
    split_ifs with hq
    · exact hq.symm
    · exact QuotientGroup.out_eq' q
  have hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q) := by
    intro h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp_rw [hact]
    have : ∀ q, f (h * rep q) = f (rep (h • q)) := fun q => by
      apply hf
      rw [hrep (h • q)]
      conv_rhs => rw [← hrep q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp_rw [this]
    exact Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))
  refine ⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩
    simp [rep]
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (rep q).2
  · have hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T)) := by
      intro q₁ _ q₂ _ h
      rw [← hrep q₁, ← hrep q₂, Subtype.ext h]
    rw [Finset.sum_image hinj]
    intro h hh
    exact hsum ⟨h, hh⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem isIntegral_int_mem_every_valuationSubring {F : Type} [Field F] (V : ValuationSubring F)
    {y : F} (hy : IsIntegral ℤ y) : y ∈ V := by
  have hV : IsIntegral V y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hz]
  exact z.2

theorem valuationSubring_valuation_intCast_coprime_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    {q : ℕ} (hq : ((q : ℕ) : F) ∈ V.nonunits) {n : ℤ} (hn : IsCoprime n (q : ℤ)) :
    V.valuation (n : F) = 1 := by
  obtain ⟨a, b, hab⟩ := hn
  have hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1 := fun m =>
    (V.valuation_le_one_iff _).2 (by simp)
  have hq' : V.valuation ((q : ℕ) : F) < 1 := V.mem_nonunits_iff.1 hq
  refine le_antisymm (hint n) (not_lt.1 fun hlt => ?_)
  have hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1 := by
    have := congrArg (fun t : ℤ => (t : F)) hab
    simpa using this
  have h1 : V.valuation ((a : F) * n) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt
  have h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'
  have h3 := Valuation.map_add_lt _ h1 h2
  rw [hsum, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_finset_primes_forall_mem_valuationSubring :
    ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F),
      ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
        ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  intro F _ _ _ s
  have : Algebra.IsAlgebraic ℤ F :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩
  have hndvd : ¬ q ∣ d.natAbs := fun h =>
    hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)
  have hcop : IsCoprime d (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using this
  have hdx : (d : F) * x ∈ V := by
    have := isIntegral_int_mem_every_valuationSubring V (hd x hx)
    simpa [zsmul_eq_mul] using this
  have hv1 := valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop
  rw [← V.valuation_le_one_iff]
  have := (V.valuation_le_one_iff _).2 hdx
  rwa [map_mul, hv1, one_mul] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_int_exponent_cyclotomic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ) (hM : 0 < M) (hd : l ^ n ∣ M) :
    ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧
      (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := rootsOfUnity.integer_power_of_ringEquiv M s.toRingEquiv
  have hs : ∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e := by
    intro ζ hζ
    have h := he hζ.toRootsOfUnity
    simpa [Units.val_zpow_eq_zpow_val] using h
  refine ⟨e, hs, ?_⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hη : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have hsη : s (ζ ^ k) = (ζ ^ k) ^ e := by
    rw [map_pow, hs ζ hζ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  set c := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hc
  have hpow : (ζ ^ k) ^ (l ^ n) = 1 := hη.pow_eq_one
  have hspec := cyclotomicCharacter.spec (L := Ω) l s.toRingEquiv (ζ ^ k) hpow
  have heq : (ζ ^ k) ^ e = (ζ ^ k) ^ (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hsη, zpow_natCast]
    exact hspec
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ e - (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hη.zpow_eq_one_iff_dvd, zpow_sub₀ (hη.ne_zero (NeZero.ne _)), heq, div_self]
    exact zpow_ne_zero _ (pow_ne_zero _ (hζ.ne_zero (NeZero.ne _)))
  have hz : (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ((e : ℤ_[l]) - c) = 0 := by
    rw [map_sub, map_intCast, hc]
    rw [sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at this
    rw [this]
    simp
  have hmem : (e : ℤ_[l]) - c ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := hz
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow] at hmem
  exact hmem

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.FunctionFieldPrimitive

open Polynomial


open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
theorem _root_.GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive {F : Type} [Field F] [CharZero F]
    {L : Type} [Field L]
    [Algebra F L] (t : L) (ht : Transcendental F t)
    (hfin : FiniteDimensional (IntermediateField.adjoin F {t}) L) :
    ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧
      Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧
      ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F),
        Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  have htK : t ∈ IntermediateField.adjoin F {t} := IntermediateField.mem_adjoin_simple_self F t
  have hne : ∀ p : Polynomial F, p ≠ 0 → Polynomial.aeval t p ≠ 0 := fun p hp h =>
    ht ⟨p, hp, h⟩
  have hden : ∀ y ∈ IntermediateField.adjoin F {t}, ∃ s : Polynomial F, s ≠ 0 ∧
      ∃ r : Polynomial F, Polynomial.aeval t s * y = Polynomial.aeval t r := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff F y).1 hy
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, 0, by simp [hs]⟩
    · exact ⟨s, hs, r, by rw [mul_div_cancel₀ _ (hne s hs)]⟩
  have hcomm : ∀ p : Polynomial F,
      ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p :
        IntermediateField.adjoin F {t}) : L) = Polynomial.aeval t p := fun p =>
    (Polynomial.aeval_algHom_apply (IntermediateField.adjoin F {t}).val
      (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p).symm
  letI algK : Algebra (Polynomial F) (IntermediateField.adjoin F {t}) :=
    (Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t})).toRingHom.toAlgebra
  letI algL : Algebra (Polynomial F) L := (Polynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial F) (IntermediateField.adjoin F {t}) L :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomm p).symm
  haveI : Algebra.IsAlgebraic (Polynomial F) (IntermediateField.adjoin F {t}) := by
    constructor
    intro k
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C r, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P 1) h
      simp at h1
      exact hs h1
    · apply Subtype.val_injective
      rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
      show ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) s :
          IntermediateField.adjoin F {t}) : L) * k -
        ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) r :
          IntermediateField.adjoin F {t}) : L) = 0
      rw [hcomm, hcomm, hsr, sub_self]
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin F {t}) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (Polynomial F) L :=
    Algebra.IsAlgebraic.trans (Polynomial F) (IntermediateField.adjoin F {t}) L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (IntermediateField.adjoin F {t}) L
  obtain ⟨y, hy0, hyint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial F) θ).exists_integral_multiple
  have hωdef : y • θ = Polynomial.aeval t y * θ := Algebra.smul_def y θ
  have hyK : Polynomial.aeval t y ∈ IntermediateField.adjoin F {t} := by
    rw [← hcomm]; exact Subtype.property _
  have htop : IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} = ⊤ := by
    rw [eq_top_iff, ← hθ, IntermediateField.adjoin_simple_le_iff]
    have hθeq : θ = (Polynomial.aeval t y)⁻¹ * (y • θ) := by
      rw [hωdef, inv_mul_cancel_left₀ (hne y hy0)]
    have hmem : (Polynomial.aeval t y)⁻¹ * (y • θ) ∈
        IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} :=
      mul_mem (inv_mem (IntermediateField.algebraMap_mem _
        (⟨Polynomial.aeval t y, hyK⟩ : IntermediateField.adjoin F {t})))
        (IntermediateField.mem_adjoin_simple_self _ (y • θ))
    rwa [← hθeq] at hmem
  refine ⟨minpoly (Polynomial F) (y • θ), y • θ, minpoly.monic hyint,
    minpoly.irreducible hyint, minpoly.aeval _ _, ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin (IntermediateField.adjoin F {t}) {y • θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (y • θ)), htop]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨1, one_ne_zero, Polynomial.X, by simp⟩
  | algebraMap k =>
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    exact ⟨s, hs, Polynomial.C r, by rw [Polynomial.eval₂_C]; exact hsr⟩
  | add a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, Polynomial.C Q₂ * R₁ + Polynomial.C Q₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, ← h₁, ← h₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, R₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_mul, ← h₁, ← h₂, map_mul]
    ring

end GlobalTheory.FunctionFieldPrimitive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOne
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open Polynomial

theorem exists_root_of_unity_close_of_pow_close : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K]
    [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 →
    ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  intro Ω K _ _ _ _ _ W x N hN hv
  classical
  set p : Polynomial Ω := X ^ N - C 1 with hp
  have hm : p.Monic := monic_X_pow_sub_C 1 hN.ne'
  have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod := by
    have := congrArg (Polynomial.aeval x) hs
    simpa [p, map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  by_contra hcon
  push_neg at hcon
  refine (not_lt.mpr ?_) hv
  rw [hx, map_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod_of_one_le ?_
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
  have ha' : a ^ N = 1 := by
    have := (mem_roots hm.ne_zero).mp ha
    simpa [p, sub_eq_zero] using this
  exact hcon a ha'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMulStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det ≠ 0 → ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ, Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧ Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.exists_tendsto_evM_mul | exact GlobalTheory.OddFrame.exists_tendsto_evM_mul | (intros; apply GlobalTheory.OddFrame.exists_tendsto_evM_mul <;> assumption)
end

