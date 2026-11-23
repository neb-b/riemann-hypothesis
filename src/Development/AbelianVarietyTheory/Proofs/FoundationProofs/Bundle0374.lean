module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0371

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwist
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.PrimChar

variable {l : ℕ} [Fact l.Prime]

theorem norm_sub_lt_one_trans {x y z : Qbar l} (h1 : ‖x - y‖ < 1) (h2 : ‖y - z‖ < 1) : ‖x - z‖ < 1 := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)

theorem norm_eq_one_of_pow {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_pow_lt_one {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 :=
  _root_.GlobalTheory.PowerDifferenceNorm.norm_pow_sub_pow_lt_one hx hy h n

theorem norm_natCast_sub_lt_one {a b : ℕ} (h : (a : ZMod l) = (b : ZMod l)) : ‖(a : Qbar l) - b‖ < 1 := by
  obtain ⟨m, hm⟩ := ((ZMod.natCast_eq_natCast_iff a b l).1 h).symm.dvd
  have h2 : (a : Qbar l) - b = (l : Qbar l) * (m : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) hm
    push_cast at this
    exact this
  rw [h2, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)).trans_lt
    (GlobalTheory.KZ.norm_prime_lt_one_qbar l)

theorem exists_root_close {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : ‖x ^ n - 1‖ < 1) :
    ∃ w : Qbar l, w ^ n = 1 ∧ ‖w - x‖ < 1 := by
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : Qbar l) := ⟨Nat.cast_ne_zero.2 hn⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) n
  have h1 := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero hn) hμ)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at h1
  rw [h1, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 (Finset.one_le_prod₀ fun w hw => ?_))
  rw [norm_sub_rev]
  exact hc w ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) 1).1 hw)

theorem exists_teichmuller : ∃ ω : (ZMod l)ˣ →* (Qbar l)ˣ,
    ∀ x : (ZMod l)ˣ, ‖(ω x : Qbar l) - ((x : ZMod l).val : Qbar l)‖ < 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : ‖(((g : ZMod l).val : ℕ) : Qbar l) ^ (l - 1) - 1‖ < 1 := by
    have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ (l - 1)) (b := 1) (by
      push_cast
      rw [ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one])
    exact_mod_cast this
  obtain ⟨w, hw, hwg⟩ := exists_root_close hl1 h0
  let w' : (Qbar l)ˣ := Units.ofPowEqOne w (l - 1) hw hl1
  have hw' : (w' : Qbar l) = w := rfl
  have hdvd : orderOf w' ∣ orderOf g := by
    rw [hord]
    apply orderOf_dvd_of_pow_eq_one
    ext
    rw [Units.val_pow_eq_pow_val, hw', hw, Units.val_one]
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, fun x => ?_⟩
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg x))
  rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hw']
  refine norm_sub_lt_one_trans (norm_pow_sub_pow_lt_one (norm_eq_one_of_pow hl1 hw).le
    (IsUltrametricDist.norm_natCast_le_one _ _) hwg j) ?_
  have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ j) (b := ((g ^ j : (ZMod l)ˣ) : ZMod l).val) (by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  exact_mod_cast this

theorem exists_wild (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) :
    ∃ χ : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ, (χ u : Qbar l) = ζ ∧ ∀ b, b ^ (l - 1) = 1 → χ b = 1 := by
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ k) := ⟨hlk⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨g, hg⟩ := (ZMod.isCyclic_units_of_prime_pow l hl h2 (k + 1)).exists_generator
  have hord : orderOf g = l ^ k * (l - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hl]
  have hou : orderOf u = l ^ k := by
    rw [← orderOf_units, hu, ZMod.orderOf_one_add_prime hl h2]
  obtain ⟨a, ha⟩ := (mem_powers_iff_mem_zpowers.2 (hg u))
  simp only at ha
  have hcop : Nat.Coprime l (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hla : Nat.Coprime a (l ^ k) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    rintro ⟨c, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : u ^ (l ^ j * (l - 1)) = 1 := by
      rw [← ha, ← pow_mul, show l * c * (l ^ j * (l - 1)) = (l ^ (j + 1) * (l - 1)) * c by ring, ← hord, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hou, pow_succ] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 hcop (Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos j) h3)
  obtain ⟨i, -, hi⟩ := (hζ.pow_of_coprime a hla).eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hc : (ζ ^ i) ^ (l ^ k) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  let c : (Qbar l)ˣ := Units.ofPowEqOne (ζ ^ i) (l ^ k) hc hlk
  have hc' : (c : Qbar l) = ζ ^ i := rfl
  have hc1 : c ^ (l ^ k) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hc', hc, Units.val_one]
  have hdvd : orderOf c ∣ orderOf g := by
    rw [hord]
    exact (orderOf_dvd_of_pow_eq_one hc1).mul_right _
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, ?_, fun b hb => ?_⟩
  · rw [← ha, map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hc', ← pow_mul, mul_comm,
      pow_mul, hi]
  · have e1 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l - 1) = 1 := by rw [← map_pow, hb, map_one]
    have e2 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l ^ k) = 1 := by
      obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg b))
      simp only
      rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, ← pow_mul, mul_comm, pow_mul, hc1, one_pow]
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)

theorem isPrimitive_of_value (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (χ : DirichletCharacter (Qbar l) (l ^ (k + 1))) (hχ : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ)
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) : χ.IsPrimitive := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  have hd := χ.conductor_dvd_level
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow hl).1 hd
  have hi' : i ≤ j + 1 := by
    rcases Nat.lt_or_eq_of_le hi with h | h
    · omega
    · exact absurd (by rw [hc, h]) hne
  have hd2 : χ.conductor ∣ l ^ (j + 1) := by rw [hc]; exact pow_dvd_pow _ hi'
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).1 χ.factorsThrough_conductor
  have h1 : (1 + (l : ZMod (l ^ (j + 1)))) ^ (l ^ j) = 1 := by
    rw [← ZMod.orderOf_one_add_prime hl h2 j]; exact pow_orderOf_eq_one _
  have hmem : u ^ (l ^ j) ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker]
    ext
    have := congrArg (ZMod.castHom hd2 (ZMod χ.conductor)) h1
    rw [map_pow, map_add (f := _), map_one, map_natCast] at this
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_pow_eq_pow_val, hu, Units.val_one]
    show ZMod.castHom hd (ZMod χ.conductor) _ = 1
    rw [map_pow, map_add (f := _), map_one, map_natCast]
    exact this
  have h3 := hker hmem
  rw [MonoidHom.mem_ker] at h3
  have h4 := congrArg Units.val h3
  rw [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val, hu, map_pow, hχ, Units.val_one] at h4
  exact hζ.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
    (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self j)) h4

theorem exists_primitive_inComp : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l),
    l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)),
      ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  intro l _ φ e k ζ h2 hk hζ
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hcop : Nat.Coprime (1 + l) (l ^ (k + 1)) := Nat.Coprime.pow_right _ (by simp)
  let u : (ZMod (l ^ (k + 1)))ˣ := ZMod.unitOfCoprime (1 + l) hcop
  have hu : (u : ZMod (l ^ (k + 1))) = 1 + l := by
    rw [ZMod.coe_unitOfCoprime]; push_cast; rfl
  obtain ⟨ω, hω⟩ := exists_teichmuller (l := l)
  obtain ⟨χ₂, hχu, hχT⟩ := exists_wild k ζ h2 hk hζ u hu
  have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
  have hred : ∀ b : (ZMod (l ^ (k + 1)))ˣ, ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) =
      ZMod.castHom hd (ZMod l) (b : ZMod (l ^ (k + 1))) := fun b => rfl
  have hu1 : ZMod.unitsMap hd u = 1 := by
    ext
    rw [hred, hu, map_add (f := _), map_one, map_natCast, ZMod.natCast_self, add_zero, Units.val_one]
  let f : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ := ((ω ^ e * MulChar.toUnitHom φ).comp (ZMod.unitsMap hd)) * χ₂
  have hf : ∀ b, (f b : Qbar l) = (ω (ZMod.unitsMap hd b) : Qbar l) ^ e *
      φ ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) * χ₂ b := fun b => by
    simp only [f, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom]
  let χ : DirichletCharacter (Qbar l) (l ^ (k + 1)) := MulChar.ofUnitHom f
  have hχ : ∀ b : (ZMod (l ^ (k + 1)))ˣ, χ b = f b := fun b => MulChar.ofUnitHom_coe f b
  have hval : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
    rw [← hu, hχ, hf, hu1, hχu]; simp
  refine ⟨χ⁻¹, ?_, ?_, ?_⟩
  · have := isPrimitive_of_value k ζ h2 hk hζ χ hval u hu
    rw [DirichletCharacter.isPrimitive_def] at this ⊢
    rw [DirichletCharacter.conductor_inv, this]
  · intro b hb
    have hb' : (((b : ZMod (l ^ (k + 1))).val : ℕ) : ZMod l) = ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) := by
      rw [hred, ZMod.castHom_apply, ZMod.natCast_val]
    rw [inv_inv, hχ, hf, hχT b hb, Units.val_one, mul_one, hb', ← sub_mul, norm_mul]
    set x := ZMod.unitsMap hd b with hx
    have hx1 : x ^ (l - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one l x
    have n1 : ‖φ (x : ZMod l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx1, Units.val_one, map_one])
    have n2 : ‖(ω x : Qbar l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hx1, map_one, Units.val_one])
    rw [n1, mul_one]
    refine norm_pow_sub_pow_lt_one n2.le (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e
    refine norm_sub_lt_one_trans (hω x) (norm_natCast_sub_lt_one ?_)
    rw [hb', ZMod.natCast_zmod_val]
  · rw [inv_inv, hval]

end GlobalTheory.KZ.Cmp.PrimChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebra
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne.ZetaDer

open Polynomial

section Gen
variable {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]

theorem exists_der_one (z : S) (μ : M)
    (hwd : ∀ Q : R[X], aeval z Q = 0 → aeval z (derivative Q) • μ = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin R {z}) D ∧ D z = μ := by
  classical
  let e : R[X] → S := fun Q => aeval z Q
  let D : S → M := fun x => aeval z (derivative (Function.invFun e x)) • μ
  have key : ∀ f : R[X], D (aeval z f) = aeval z (derivative f) • μ := by
    intro f
    have h1 : e (Function.invFun e (e f)) = e f := Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun e (e f) - f) (by rw [map_sub]; exact sub_eq_zero.2 h1)
    rw [derivative_sub, map_sub, sub_smul, sub_eq_zero] at h2
    exact h2
  have hm : ∀ x ∈ Algebra.adjoin R {z}, ∃ f : R[X], aeval z f = x := by
    intro x hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact hx
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_add (f := _), key, key, key, derivative_add, map_add (f := _), add_smul]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_mul, key, key, key, derivative_mul, map_add (f := _), add_smul, map_mul, map_mul, smul_smul, smul_smul,
      add_comm, mul_comm (aeval z (derivative f))]
  · intro a
    have : algebraMap R S a = aeval z (C a) := by simp
    rw [this, key]
    simp
  · have : z = aeval z (X : R[X]) := by simp
    conv_lhs => rw [this]
    rw [key]
    simp

end Gen

variable {Ω : Type} [Field Ω]

theorem frac_smul_mk {A : ValuationSubring Ω} (s : A) (x : Ω) :
    s • (Submodule.Quotient.mk x : FracA A) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero {A : ValuationSubring Ω} (s : A) :
    (Submodule.Quotient.mk (s : Ω) : FracA A) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_rel [CharZero Ω] {p : ℕ} [hp : Fact p.Prime] {A : ValuationSubring Ω} {R : Type} [CommRing R] [Algebra R A]
    (m : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ (m + 1))) :
    (aeval z (derivative (cyclotomic (p ^ (m + 1)) R))) •
      (Submodule.Quotient.mk ((z : Ω) * p / (p : Ω) ^ (m + 1)) : FracA A) = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzA : IsPrimitiveRoot z (p ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := A.subtype) hz Subtype.val_injective
  have hξ : IsPrimitiveRoot ((z : Ω) ^ p ^ m) p := by
    have := hz.pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this
  set gS : A := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ((z : Ω) ^ p ^ m) ^ j := by
    simp [gS]
  have hg : (gS : Ω) * ((z : Ω) ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp
  have hroot : aeval z (cyclotomic (p ^ (m + 1)) R) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hzA.isRoot_cyclotomic hpos
  have hid := congrArg (fun f => aeval z (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one R p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add (f := _), map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  rw [frac_smul_mk]
  set F := aeval z (derivative (cyclotomic (p ^ (m + 1)) R))
  have hζ1 : (z : Ω) ^ p ^ (m + 1) = 1 := hz.pow_eq_one
  have hF : (F : Ω) * ((z : Ω) ^ p ^ m - 1) * z = (p : Ω) ^ (m + 1) := by
    have h2 : F * (z ^ p ^ m - 1) = (p : A) ^ (m + 1) * z ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    have h3 : (F : Ω) * ((z : Ω) ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * (z : Ω) ^ (p ^ (m + 1) - 1) := by
      have := congrArg (A.subtype) h2
      simpa using this
    rw [h3, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : (z : Ω) ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : (F : Ω) * ((z : Ω) * p / (p : Ω) ^ (m + 1)) = ((-gS : A) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

theorem exists_root_succ [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (n : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ n)) :
    ∃ w : A, IsPrimitiveRoot (w : Ω) (p ^ (n + 1)) ∧ w ^ p = z := by
  have hpos : 0 < p ^ (n + 1) := pow_pos hp.out.pos _
  haveI : NeZero (p ^ (n + 1)) := ⟨hpos.ne'⟩
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos _).ne'⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : Ω) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (n + 1))
  have h1 : IsPrimitiveRoot (ζ ^ p) (p ^ n) := hζ.pow hpos (by rw [pow_succ'])
  obtain ⟨i, -, hi, hiz⟩ := h1.isPrimitiveRoot_iff.1 hz

  obtain ⟨j, hj, hjz⟩ : ∃ j : ℕ, j.Coprime (p ^ (n + 1)) ∧ (ζ ^ p) ^ j = z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, Nat.coprime_one_left _, ?_⟩
      have a1 : ζ ^ p = 1 := by simpa using h1.pow_eq_one
      have a2 : (z : Ω) = 1 := by simpa using hz.pow_eq_one
      rw [a1, a2, one_pow]
    · refine ⟨i, ?_, hiz⟩
      rw [Nat.coprime_pow_right_iff hn] at hi
      exact hi.pow_right _
  have hw : IsPrimitiveRoot (ζ ^ j) (p ^ (n + 1)) := hζ.pow_of_coprime j hj
  have hmem : ζ ^ j ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hw.pow_eq_one]; exact A.one_mem)
  refine ⟨⟨ζ ^ j, hmem⟩, hw, Subtype.ext ?_⟩
  rw [← hjz]
  show (ζ ^ j) ^ p = _
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem exists_seq [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (N : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ N)) :
    ∃ zs : ℕ → A, zs 0 = z ∧ (∀ k, IsPrimitiveRoot (zs k : Ω) (p ^ (N + k))) ∧ ∀ k, zs (k + 1) ^ p = zs k := by
  choose f hf hf' using exists_root_succ (p := p) A
  let s : (k : ℕ) → {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))} := fun k =>
    Nat.rec (motive := fun k => {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}) ⟨z, hz⟩
      (fun k w => ⟨f (N + k) w.1 w.2, hf (N + k) w.1 w.2⟩) k
  exact ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => hf' (N + k) (s k).1 (s k).2⟩

end GlobalTheory.RecOne.ZetaDer

namespace GlobalTheory.RecOne

open ZetaDer Polynomial

theorem zeta_derivation_cyc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) →
    ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧
      D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  intro p hp Ω _ _ hc A hO N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨zs, hz0, hprim, hpow⟩ := exists_seq A N z hz
  let B : ℕ → Subalgebra (fixA A) A := fun m => Algebra.adjoin (fixA A) {zs (m + 1)}
  have hmem1 : ∀ m, zs (m + 1) ∈ B m := fun m => Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem0 : ∀ m, zs m ∈ B m := fun m => by rw [← hpow m]; exact pow_mem (hmem1 m) _
  have hle1 : ∀ m, B m ≤ B (m + 1) := fun m =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (hmem0 (m + 1)))
  have hlev : ∀ m : ℕ, ∃ D : A → FracA A, IsDerOn (B m) D ∧
      D (zs (m + 1)) = Submodule.Quotient.mk ((zs (m + 1) : Ω) * p / (p : Ω) ^ (N + m + 1)) := by
    intro m
    refine exists_der_one (zs (m + 1)) _ fun Q hQ => ?_
    obtain ⟨R, rfl⟩ := GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed p Ω A hO (N + m + 1) (zs (m + 1)) (hprim (m + 1)) Q hQ
    have hzA : IsPrimitiveRoot (zs (m + 1)) (p ^ (N + m + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim (m + 1)) Subtype.val_injective
    have hroot : aeval (zs (m + 1)) (cyclotomic (p ^ (N + m + 1)) (fixA A)) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      exact hzA.isRoot_cyclotomic (pow_pos hp.out.pos _)
    rw [derivative_mul, map_add (f := _), map_mul, map_mul, hroot, zero_mul, add_zero, mul_comm, mul_smul,
      cyc_rel (N + m) (zs (m + 1)) (hprim (m + 1)), smul_zero]
  choose D hD hDz using hlev
  have hval : ∀ m, D m (zs m) = Submodule.Quotient.mk ((zs m : Ω) * p / (p : Ω) ^ (N + m)) := by
    intro m
    have hc1 : ((zs m : A) : Ω) = (zs (m + 1) : Ω) ^ p := by rw [← hpow m]; rfl
    rw [hc1]
    conv_lhs => rw [← hpow m]
    rw [(hD m).pow_der (hmem1 m) hp.out.pos, hDz m, ZetaDer.frac_smul_mk]
    congr 1
    push_cast
    rw [← pow_sub_one_mul hp.out.ne_zero (zs (m + 1) : Ω)]
    field_simp
    ring
  have hcompat : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zs (m + 1)}) ((hD (m + 1)).mono' (hle1 m)) (hD m) ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, hval (m + 1), hDz m]
    rfl
  have hmono : Monotone B := monotone_nat_of_le_succ hle1
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (fixA A) A (FracA A) B hmono D hD hcompat
  have hle : cycAlg p A ≤ ⨆ m, B m := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨n, hx⟩
    haveI : NeZero (p ^ (N + n)) := ⟨(pow_pos hp.out.pos _).ne'⟩
    have hzA : IsPrimitiveRoot (zs n) (p ^ (N + n)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim n) Subtype.val_injective
    obtain ⟨i, -, rfl⟩ := hzA.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_add, mul_comm, pow_mul, hx, one_pow])
    exact (le_iSup B n) (pow_mem (hmem0 n) i)
  refine ⟨D', hD'.mono' hle, ?_⟩
  rw [← hz0, hD'eq 0 _ (hmem0 0), hval 0]
  rfl

end GlobalTheory.RecOne
end
end

