module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002
public import ReciprocityTheory.Chebotarev.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def coneOn (s : Finset V) : Set V :=
  {x | ∃ t : V → ℚ, (∀ i ∈ s, 0 < t i) ∧ x = ∑ i ∈ s, t i • i}

def SignConst (l : V →ₗ[ℚ] ℚ) (C : Set V) : Prop :=
  (∀ x ∈ C, l x = 0) ∨ (∀ x ∈ C, 0 < l x) ∨ (∀ x ∈ C, l x < 0)

inductive Tile (P : Set V) (Q : Set V → Prop) : Set V → Prop
  | empty : Tile P Q ∅
  | cone (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V)) (hP : (s : Set V) ⊆ P) (hQ : Q (coneOn s)) :
      Tile P Q (coneOn s)
  | union {A B : Set V} (hA : Tile P Q A) (hB : Tile P Q B) (hAB : Disjoint A B) : Tile P Q (A ∪ B)

def posCone (F : Type) [Field F] [NumberField F] : ConvexCone ℚ F where
  carrier := {x | TotPos F x}
  smul_mem' := by
    intro c hc x hx σ
    have h : σ (c • x) = (c : ℝ) * σ x := by
      rw [Rat.smul_def, map_mul, map_ratCast]
    rw [h]
    exact mul_pos (by exact_mod_cast hc) (hx σ)
  add_mem' := by
    intro x hx y hy σ
    rw [map_add (f := _)]
    exact add_pos (hx σ) (hy σ)

def congSubgroup {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := congUnits 𝔣
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a * b : (𝓞 F)ˣ) : 𝓞 F) - 1 = (a : 𝓞 F) * ((b : 𝓞 F) - 1) + ((a : 𝓞 F) - 1) := by
        rw [Units.val_mul]; ring
      rw [h]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hb.1) ha.1
    · have h : (((a * b : (𝓞 F)ˣ) : 𝓞 F) : F) = ((a : 𝓞 F) : F) * ((b : 𝓞 F) : F) := by
        rw [Units.val_mul]; simp
      rw [h, map_mul]
      exact mul_pos (ha.2 σ) (hb.2 σ)
  one_mem' := by
    refine ⟨by simp, fun σ => ?_⟩
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -(((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((a : 𝓞 F) - 1)) := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        linear_combination this
      rw [h]
      exact 𝔣.neg_mem (𝔣.mul_mem_left _ ha.1)
    · have h1 : (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((a : 𝓞 F) : F) = 1 := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) this
      have h2 := congrArg σ h1
      rw [map_mul, map_one] at h2
      have h3 := ha.2 σ
      by_contra hn
      have : σ (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * σ ((a : 𝓞 F) : F) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h3.le
      linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeDegreeOneAvoiding
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
open Polynomial

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_large_prime_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), p.Prime ∧ N < p ∧ (p : ℤ) ∣ f.eval m :=
  _root_.UpperTheory.Reformulated.B.P6.LargePrimeDivisors.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval f hf N

theorem exists_exponent_ne_zero (F : Type) [Field F] [NumberField F] :
    ∃ θ : 𝓞 F, RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic α))
  obtain ⟨θ, hθ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨θ, ?_⟩
  have hθ' : (θ : F) = y • α := hθ
  have hprim : IntermediateField.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have h : (θ : F) ∈ IntermediateField.adjoin ℚ {(θ : F)} :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have hyF : (y : F) ≠ 0 := by exact_mod_cast hy
    have e : α = ((y : ℚ)⁻¹) • (θ : F) := by
      rw [hθ', Algebra.smul_def, zsmul_eq_mul]
      simp [hyF]
    rw [e]
    exact (IntermediateField.adjoin ℚ {(θ : F)}).smul_mem h
  have hintZ : IsIntegral ℤ (θ : F) := RingOfIntegers.isIntegral_coe θ
  have hintQ : IsIntegral ℚ (θ : F) := Algebra.IsIntegral.isIntegral _
  have htop : Algebra.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, hprim,
      IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop hintQ htop
  have hgen : B.gen = θ := PowerBasis.ofAdjoinEqTop_gen hintQ htop
  have hintB : IsIntegral ℤ B.gen := hgen ▸ hintZ
  have hdi : IsIntegral ℤ (Algebra.discr ℚ B.basis) := Algebra.discr_isIntegral ℚ (fun i => by
    rw [PowerBasis.coe_basis]
    exact hintB.pow _)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hdi
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hn.symm)
  have hcond : (n : 𝓞 F) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have h1 := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hintB (RingOfIntegers.isIntegral_coe b)
    rw [hgen, ← hn] at h1
    have h2 : ((n : F) * (b : F)) ∈ Algebra.adjoin ℤ {(θ : F)} := by
      simpa [Algebra.smul_def] using h1
    have h3 : Algebra.adjoin ℤ {(θ : F)} =
        (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 F) F) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [h3] at h2
    obtain ⟨u, hu, hue⟩ := h2
    have hub : u = (n : 𝓞 F) * b := RingOfIntegers.coe_injective (by simpa using hue)
    exact hub ▸ hu
  intro h0
  change Ideal.absNorm (Ideal.under ℤ (conductor ℤ θ)) = 0 at h0
  rw [Ideal.absNorm_eq_zero_iff] at h0
  have hm : n ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using hcond
  rw [h0] at hm
  exact hn0 (by simpa using hm)

theorem exists_isPrime_absNorm_eq {F : Type} [Field F] [NumberField F] (θ : 𝓞 F) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (m : ℤ) (hm : (p : ℤ) ∣ (minpoly ℤ θ).eval m) :
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ Ideal.absNorm 𝔠 = p := by
  have h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hQ : (X - C ((m : ℤ) : ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff h₀]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.2 ?_⟩
    rw [IsRoot.def, eval_intCast_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hm
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩
  have hf := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
  have hPp : (P : Ideal (𝓞 F)).IsPrime := P.2.1
  have hPl : (P : Ideal (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
  refine ⟨P, hPp, ?_⟩
  rw [← Ideal.pow_inertiaDeg p (P : Ideal (𝓞 F)), hf, natDegree_X_sub_C, pow_one]

theorem exists_prime_absNorm_avoiding : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 h𝔣 W B hW
  obtain ⟨θ, hθ⟩ := exists_exponent_ne_zero F
  obtain ⟨p, m, hp, hN, hdvd⟩ := exists_large_prime_dvd_eval (minpoly ℤ θ)
    (minpoly.natDegree_pos θ.isIntegral)
    (B + RingOfIntegers.exponent θ + Ideal.absNorm 𝔣 + ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}))
  have := Fact.mk hp
  have hexp : ¬ p ∣ RingOfIntegers.exponent θ := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hθ) h
    omega
  obtain ⟨𝔠, hprime, hnorm⟩ := exists_isPrime_absNorm_eq θ p hexp m hdvd
  have small : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → Ideal.absNorm I < p → ¬ I ≤ 𝔠 := fun I hI hlt hle => by
    have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Ideal.absNorm_dvd_absNorm_of_le hle)
    omega
  have hbot : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hnorm
    exact hp.ne_zero hnorm.symm
  have hmax : 𝔠.IsMaximal := hprime.isMaximal hbot
  refine ⟨𝔠, hprime, hnorm ▸ hp, by omega, ?_, ?_⟩
  · by_contra h
    exact small 𝔣 h𝔣 (by omega) (sup_eq_left.1 (hmax.eq_of_le h le_sup_left).symm)
  · intro x hx hxc
    have hle : Ideal.absNorm (Ideal.span {x}) ≤ ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}) :=
      Finset.single_le_sum (f := fun x => Ideal.absNorm (Ideal.span {x})) (fun _ _ => Nat.zero_le _) hx
    exact small (Ideal.span {x}) (by simpa using hW x hx) (by omega)
      ((Ideal.span_singleton_le_iff_mem _).2 hxc)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ :=
  fun m => g (m + Pi.single i 1) - g m

def DL {r : ℕ} (cs : List (Fin r)) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ := cs.foldr fd g

def fdR {r : ℕ} (i : Fin r) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ :=
  fun x => G (x + Pi.single i 1) - G x

def DLR {r : ℕ} (cs : List (Fin r)) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ := cs.foldr fdR G

def GoodAt (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) : Prop :=
  (∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) ∧
    ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single i e : Fin r → ℕ)) = 0

def BddW {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop := ∃ C : ℝ, ∀ m, |(v m : ℝ)| ≤ C

def partialSum {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m i), v (Function.update m i k)

def meanP (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  (∑ k ∈ Finset.range l, partialSum i v (Function.update m i k)) / l

def Aop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  partialSum i v (m + Pi.single i 1) - meanP l i v m

def Bop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  if m i = 0 then meanP l i v m else 0

def linF {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) : ℝ :=
  b j + ∑ i, a j i * x i

def Fr {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (β : ι → ℕ) (x : Fin r → ℝ) : ℂ :=
  ∏ j, ((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))

def sizeE {r : ℕ} (x : Fin r → ℝ) : ℝ := 1 + ∑ i, x i

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaPrimeTwistSummable
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem classWeight_relation (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)) (hc : (Ideal.absNorm 𝔠).Prime)
    (e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}) (he : ∀ J, (e J).1 = 𝔠 * J.1)
    (s : ℂ) (t : ℂ) (_hs : 1 < s.re)
    (hA : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (hB : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (ht : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t) :
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  classical
  have hp0 : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne_zero
  have hf1 : (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s)) = fun J =>
      ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
    funext J
    rw [he J, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have h1 : HasSum (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s))
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    rw [hf1]
    exact hA.hasSum.mul_left _
  have h2 := (e.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).mp h1
  have hι : Function.Injective (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B})) := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have hf3 : ((fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) ∘
      (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}))) =
      fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    simp only [Function.comp_apply, if_pos I.2.2]
  have h3 : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0)
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    refine (hι.hasSum_iff ?_).mp ?_
    · intro x hx
      rw [if_neg]
      intro hle
      exact hx ⟨⟨x.1, x.2, hle⟩, rfl⟩
    · rw [hf3]
      exact h2
  have h4 := (h3.mul_left ((Ideal.absNorm 𝔠 : ℕ) : ℂ)).sub hB.hasSum
  have hf5 : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
      fun I => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * (if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) -
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    unfold classWeight
    split_ifs <;> push_cast <;> ring
  rw [hf5] at ht
  rw [ht.unique h4, sub_eq_add_neg (1 : ℂ) s, Complex.cpow_add _ _ hp0, Complex.cpow_one, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummable
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    (fun I : Ideal (𝓞 F) => CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞)
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassPrimeMultiplicationPermutation
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem rayRel_of_mul_left {F : Type} [Field F] [NumberField F] {𝔣 𝔠 I J : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥)
    (h : RayRel F 𝔣 (𝔠 * I) (𝔠 * J)) : RayRel F 𝔣 I J := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  refine ⟨a, b, ha, hb, ha', hb', hp, mul_left_cancel₀ h𝔠 ?_⟩
  rw [mul_left_comm, e, mul_left_comm]

theorem shift_perm (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))) (_h𝔣 : 𝔣 ≠ ⊥)
    (_hp : 𝔠.IsPrime) (h0 : 𝔠 ≠ ⊥) (hs : 𝔠 ⊔ 𝔣 = ⊤)
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hu : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hr : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) :
    ∃ τ : Equiv.Perm S, ∀ c : S,
      ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
          {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
        ∀ J, (e J).1 = 𝔠 * J.1 := by
  have hc : CoprimeTo F 𝔣 𝔠 := ⟨h0, hs⟩
  have hex : ∀ d : S, ∃ a : S, RayRel F 𝔣 (𝔠 * d.1) a.1 := fun d => by
    obtain ⟨a, ha, h⟩ := hr _ (coprimeTo_mul hc (hS d.1 d.2))
    exact ⟨⟨a, ha⟩, h⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := fun d d' h => by
    have h1 : RayRel F 𝔣 (𝔠 * d.1) (𝔠 * d'.1) := rayRel_trans (hφ d) (h ▸ rayRel_symm (hφ d'))
    exact Subtype.ext (hu _ d.2 _ d'.2 (rayRel_of_mul_left h0 h1))
  let τ : Equiv.Perm S := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).symm
  have hτ : ∀ c : S, RayRel F 𝔣 (𝔠 * (τ c).1) c.1 := fun c => by
    have h1 : φ (τ c) = c := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).apply_symm_apply c
    have h2 := hφ (τ c)
    rwa [h1] at h2
  refine ⟨τ, fun c => ?_⟩
  let f : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} →
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} := fun J =>
    ⟨𝔠 * J.1, ⟨coprimeTo_mul hc J.2.1, rayRel_trans (rayRel_mul_left 𝔠 J.2.2) (hτ c)⟩, Ideal.mul_le_left⟩
  have hf : Function.Bijective f := by
    constructor
    · intro J J' h
      have h1 : 𝔠 * J.1 = 𝔠 * J'.1 := congrArg (fun x : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} => x.1) h
      exact Subtype.ext (mul_left_cancel₀ h0 h1)
    · rintro ⟨I, ⟨hI, hIc⟩, hle⟩
      obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
      have hJ0 : J ≠ ⊥ := fun h => hI.1 (by rw [h, Ideal.mul_bot])
      have hJ : CoprimeTo F 𝔣 J :=
        ⟨hJ0, top_le_iff.1 (hI.2 ▸ sup_le_sup_right Ideal.mul_le_right 𝔣)⟩
      exact ⟨⟨J, hJ, rayRel_of_mul_left h0 (rayRel_trans hIc (rayRel_symm (hτ c)))⟩, rfl⟩
  exact ⟨Equiv.ofBijective f hf, fun J => rfl⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

