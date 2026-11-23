module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemInertiaInvariantsCyclotomicAlgebraIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem mem_cycAlg_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  intro l _ Ω _ _ _ A hA x
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  constructor
  · intro hx s hs
    obtain ⟨hsI, hsZ⟩ := mem_ineCyc.1 hs
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨n, hn⟩ := hz
      refine GlobalTheory.Col.fix_of_cycMod (l := l) (le_refl n) ?_ ?_
      · simp [cycMod, hsZ]
      · exact_mod_cast congrArg (fun a : A => (a : Ω)) hn
    | algebraMap r => exact r.2 s hsI
    | add a b _ _ ha hb =>
      show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
      rw [map_add (f := _), ha, hb]
    | mul a b _ _ ha hb =>
      show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
      rw [map_mul, ha, hb]
  · intro hx
    have hv : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hl⟩ := hA
      have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
      simpa using h1
    obtain ⟨m, hm⟩ := GlobalTheory.fixed_cycMod_of_fixed_cycZ l Ω A hv ∅ (x : Ω)
      (fun s hs _ hz => hx s (mem_ineCyc.2 ⟨hs, hz⟩))
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hpos : 0 < l ^ m := pow_pos hl.pos m
    haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
    have hfix : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s (x : Ω) = x := by
      intro s hs hsζ
      refine hm s ⟨hs, by simp, ?_⟩
      have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
      have h2 : ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val = ζ ^ 1 := by
        rw [pow_one]
        exact h1.symm.trans hsζ
      have h3 := (pow_eq_pow_iff_modEq (G := Ωˣ) (x := (hζ.isUnit hpos.ne').unit)
        (n := (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val) (m := 1)).1 (by
          apply Units.ext
          simpa using h2)
      have h4 : orderOf (hζ.isUnit hpos.ne').unit = l ^ m := by
        rw [← orderOf_units, IsUnit.unit_spec]
        exact hζ.eq_orderOf.symm
      rw [h4, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_one] at h3
      exact Units.ext h3
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA m ζ hζ (x : Ω) x.2 hfix
    have hζA : ζ ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
    have hζc : (⟨ζ, hζA⟩ : A) ∈ cycAlg l A :=
      mem_cycAlg_of_pow (n := m) (Subtype.ext (by simpa using hζ.pow_eq_one))
    have e : x = ∑ d ∈ Finset.range (Q.natDegree + 1), (⟨Q.coeff d, (hQ d).1⟩ : A) * (⟨ζ, hζA⟩ : A) ^ d := by
      apply Subtype.ext
      rw [← hQe, Polynomial.eval_eq_sum_range]
      refine Eq.trans ?_ (map_sum A.subtype _ _).symm
      refine Finset.sum_congr rfl fun d _ => ?_
      simp
    rw [e]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hζc d)
    exact (cycAlg l A).algebraMap_mem (⟨⟨Q.coeff d, (hQ d).1⟩, (hQ d).2⟩ : fixA A)

end GlobalTheory.RecOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocWsumProps
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem shCoc_wsum_props : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (ρ : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin 2) (Fin 2) (Qbar l)) (cf : Coef l) (ι : Type) [Fintype ι] (cw : ι → Qbar l)
  (Yx : ι → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ i r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Yx i r)) →
  (∀ i r, Yx i r = push (redL l r) (Yx i (r + 1))) →
  (∀ i r y j, Continuous fun s => Yx i r s y j) →
  (∀ i r s u j, Yx i r s u j ∈ cf.O) → (∀ i, cw i ∈ cf.O) →
  (∀ r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (fun s y => ∑ i, cw i • Yx i r s y)) ∧
  (∀ r, (fun s y => ∑ i, cw i • Yx i r s y) = push (redL l r) (fun s y => ∑ i, cw i • Yx i (r + 1) s y)) ∧
  (∀ r y j, Continuous fun s => (∑ i, cw i • Yx i r s y) j) ∧
  (∀ r s u j, (∑ i, cw i • Yx i r s u) j ∈ cf.O) := by
  intro l _ Ω _ _ ρ cf ι _ cw Yx hC hP hCont hO hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s t x
    have := fun i => hC i r s t x
    simp only [this, Finset.sum_add_distrib, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · intro r
    funext s y
    simp only [push]
    conv_lhs => rw [show (∑ i, cw i • Yx i r s y) = ∑ i, cw i • push (redL l r) (Yx i (r + 1)) s y from by
      simp only [← hP]]
    simp only [push, Finset.smul_sum]
    exact Finset.sum_comm
  · intro r y j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hCont i r y j)
  · intro r s u j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hw i) (hO i r s u j)

end GlobalTheory.K4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDiscreteInertiaKummerCoboundaryBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.HTTrace

theorem apply_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G ℚ Ω)
    {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod ℚ Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ

theorem cycMod_eq_one (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (hm : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hsζ : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have h1 := apply_pow Ω l m s hζ.pow_eq_one
  rw [hsζ] at h1
  have hv1 : ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val = 1 := by
    have := hζ.pow_inj (i := 1) (j := ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val) hlm (ZMod.val_lt _)
      (by rw [pow_one]; exact h1)
    exact this.symm
  ext
  rw [Units.val_one]
  apply ZMod.val_injective
  rw [hv1, ZMod.val_one]

theorem exists_gen (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m))
    (hζ' : ζ' ^ (l ^ m) = ζ) :
    ∃ s ∈ Ine (F := ℚ) A, s ζ' = ζ * ζ' := by
  obtain ⟨v, hv, hlv⟩ := hA
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hlv
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) hl1
  have hlt : 1 + l ^ m < l ^ (2 * m) := by
    rw [two_mul, pow_add]; nlinarith
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h
    have h2 : l ∣ l ^ m := dvd_pow_self l (by omega)
    have h3 : l ∣ 1 := (Nat.dvd_add_left h2).mp h
    have := Nat.le_of_dvd one_pos h3
    omega
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hAl (2 * m) hu.unit
  have hsu' : ((cycMod ℚ Ω l (2 * m) s : (ZMod (l ^ (2 * m)))ˣ) : ZMod (l ^ (2 * m)))
      = ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    have := congrArg Units.val hsu
    simpa using this
  have hpow2 : ζ' ^ (l ^ (2 * m)) = 1 := by
    rw [two_mul, pow_add, pow_mul, hζ', hζ.pow_eq_one]
  refine ⟨s, hs, ?_⟩
  rw [apply_pow Ω l (2 * m) s hpow2, hsu', ZMod.val_natCast, Nat.mod_eq_of_lt hlt, pow_add, pow_one, hζ', mul_comm]

theorem isPrimitiveRoot_root {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hζ' : ζ' ^ (l ^ m) = ζ) : IsPrimitiveRoot ζ' (l ^ (2 * m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [IsPrimitiveRoot.iff_orderOf, show 2 * (n + 1) = (n + 1 + n) + 1 by ring]
  apply orderOf_eq_prime_pow
  · rw [pow_add, pow_mul, hζ']
    exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
      (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (by omega))
  · rw [show (n + 1 + n) + 1 = (n + 1) + (n + 1) by ring, pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]

theorem geom_sum_root {Ω : Type} [Field Ω] (N : ℕ) (u : Ω) (hu : u ^ N = 1) :
    ∃ e : ℕ, ∑ j ∈ Finset.range N, u ^ j = (N : Ω) * e := by
  by_cases h : u = 1
  · exact ⟨1, by simp [h]⟩
  · refine ⟨0, ?_⟩
    have h1 := geom_sum_mul u N
    rw [hu, sub_self] at h1
    simpa using (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)

theorem trace_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (N : ℕ) (ζ ζ' : Ω) (hζ : ζ ^ N = 1)
    (hζ'A : ζ' ∈ A) (γ : G ℚ Ω) (h1 : γ ζ = ζ) (h2 : γ ζ' = ζ * ζ') (Q : Polynomial Ω)
    (hQ : ∀ d, Q.coeff d ∈ A ∧ γ (Q.coeff d) = Q.coeff d) :
    ∃ v ∈ A, ∑ j ∈ Finset.range N, (γ ^ j) (Q.eval ζ') = (N : Ω) * v := by
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h2, map_mul, hfix ζ h1, ih]; ring
  choose e he using fun d : ℕ => geom_sum_root N (ζ ^ d) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])
  refine ⟨∑ d ∈ Finset.range (Q.natDegree + 1), Q.coeff d * ζ' ^ d * e d,
    sum_mem fun d _ => mul_mem (mul_mem (hQ d).1 (pow_mem hζ'A d)) (natCast_mem A _), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.eval_eq_sum_range, map_sum, map_mul, map_pow, hj, hfix _ (hQ _).2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have : ∀ j : ℕ, Q.coeff d * (ζ ^ j * ζ') ^ d = Q.coeff d * ζ' ^ d * (ζ ^ d) ^ j := fun j => by ring
  simp only [this]
  rw [← Finset.mul_sum, he d]; ring

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  intro l _ hl2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ A hA m k hkm ζ ζ' hζ hζ' o x ho hx hofix hyp
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rcases k with _ | k
  · exact ⟨(l : Ω) ^ 1 * o, mul_mem (pow_mem hlA 1) ho, by simp⟩
  have hm : 1 ≤ m := by omega
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have hprim := isPrimitiveRoot_root l m hm ζ ζ' hζ hζ'
  have hζ'A : ζ' ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 := congrArg A.valuation hprim.pow_eq_one
    rw [map_pow, map_one] at h1
    exact (pow_le_one_iff (pow_pos (Fact.out : l.Prime).pos _).ne').1 h1.le
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ MulAction.stabilizer (G ℚ Ω) ζ'
  have hHmem : ∀ s : G ℚ Ω, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ s ζ' = ζ' := fun s => Iff.rfl
  have hHζ : ∀ s : G ℚ Ω, s ζ' = ζ' → s ζ = ζ := fun s hs => by rw [← hζ', map_pow, hs]
  have hHc : ∀ s : G ℚ Ω, s ζ' = ζ' → cycMod ℚ Ω l m s = 1 := fun s hs =>
    cycMod_eq_one l Ω m hm ζ hζ s (hHζ s hs)
  obtain ⟨y, hyA, hyfix, e, heA, he⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A hA H (inf_le_left.trans (Ine_le_Dec A)) k x hx (by
    intro h hh
    obtain ⟨hh1, hh2⟩ := (hHmem h).1 hh
    obtain ⟨z, hz, hze⟩ := hyp h hh1 (hHc h hh2) 0 (by simpa using hh2)
    refine ⟨-z, neg_mem hz, ?_⟩
    simp only [ZMod.val_zero, Nat.cast_zero, zero_mul] at hze
    linear_combination -hze)
  obtain ⟨γ, hγI, hγ⟩ := exists_gen l Ω A hA m hm ζ ζ' hζ hζ'
  have hγζ : γ ζ = ζ := by
    conv_lhs => rw [← hζ']
    rw [map_pow, hγ, mul_pow, hζ.pow_eq_one, one_mul, hζ']
  have hγc := cycMod_eq_one l Ω m hm ζ hζ γ hγζ
  obtain ⟨z, hzA, hz⟩ := hyp γ hγI hγc 1 (by rw [ZMod.val_one, pow_one]; exact hγ)
  rw [ZMod.val_one, Nat.cast_one, one_mul] at hz
  have hγD := Ine_le_Dec A hγI
  set w : Ω := γ e - e + l * z with hw
  have hwA : w ∈ A :=
    add_mem (sub_mem ((apply_mem_iff_of_mem_Dec hγD e).2 heA) heA) (mul_mem hlA hzA)
  have hweq : (l : Ω) ^ k * w = o - (γ y - y) := by
    have h1 := congrArg γ he
    rw [map_sub, map_mul, map_pow, map_natCast] at h1
    rw [hw]
    linear_combination -hz - h1 + he
  have hwfix : ∀ s ∈ Ine (F := ℚ) A, s ζ' = ζ' → s w = w := by
    intro s hs hsζ
    have h1 : γ⁻¹ * s * γ⁻¹⁻¹ ∈ H := by
      refine (hHmem _).2 ⟨conj_mem_Ine ((Dec (F := ℚ) A).inv_mem hγD) hs, ?_⟩
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγ, map_mul, hHζ s hsζ, hsζ, ← hγ]
      exact γ.symm_apply_apply ζ'
    have h2 : s (γ y) = γ y := by
      have h3 := congrArg γ (hyfix _ h1)
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply] at h3
      exact h3
    have h4 := congrArg s hweq
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, h2, hyfix s ((hHmem s).2 ⟨hs, hsζ⟩),
      hofix s hs (hHc s hsζ), ← hweq] at h4
    exact mul_left_cancel₀ (pow_ne_zero k hl0) h4
  obtain ⟨Q, hQ, hQw⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA (2 * m) ζ' hprim w hwA hwfix
  obtain ⟨v, hvA, hv⟩ := trace_mem A (l ^ m) ζ ζ' hζ.pow_eq_one hζ'A γ hγζ hγ Q fun d => ⟨(hQ d).1, (hQ d).2 γ hγI⟩
  rw [hQw] at hv
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hγ, map_mul, hfix ζ hγζ, ih]; ring
  have htop : (γ ^ (l ^ m)) y = y :=
    hyfix _ ((hHmem _).2 ⟨pow_mem hγI _, by rw [hj, hζ.pow_eq_one, one_mul]⟩)
  have hsum : ∑ j ∈ Finset.range (l ^ m), (γ ^ j) ((l : Ω) ^ k * w) = ((l ^ m : ℕ) : Ω) * o := by
    have h5 : ∀ j : ℕ, (γ ^ j) ((l : Ω) ^ k * w) = o - ((γ ^ (j + 1)) y - (γ ^ j) y) := fun j => by
      rw [hweq, map_sub, map_sub, hfix o (hofix γ hγI hγc), pow_succ, AlgEquiv.mul_apply]
    simp only [h5]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => (γ ^ j) y), htop]
    simp
  simp only [map_mul, map_pow, map_natCast] at hsum
  rw [← Finset.mul_sum, hv] at hsum
  have hN : ((l ^ m : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ho' : o = (l : Ω) ^ k * v := mul_left_cancel₀ hN (by linear_combination -hsum)
  exact ⟨v, hvA, by rw [ho']; ring⟩

end GlobalTheory.HTTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShapeStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.CyclotomicQExpansion
open scoped Matrix MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_representation_ordinary_triangular_shape : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (ψ : ZMod l → Qbar l),
  Nf e S A W → SrcUr ι e A W g →
  (∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
    (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
    ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)) →
  ∃ ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l),
    (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) ∧ Continuous ρ ∧
    (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) ∧
    (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) ∧
    ∃ F : Finset Ω, ∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e) := by
  first | (exact @GlobalTheory.RhoAdm.rho_ordinary_shape) | (exact GlobalTheory.RhoAdm.rho_ordinary_shape) | (intros; apply GlobalTheory.RhoAdm.rho_ordinary_shape  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSystemExponentRaiseOfPrimePowSmul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem zetaSystem_exponent_raise_of_prime_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N)
  (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ m : ℕ)
  (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ b b', pr (b + b') = pr b + pr b') →
  (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ Y →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  intro l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n
  obtain ⟨bB, hB, b, hb, hY⟩ := hZ r n
  have hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl
  have hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v := by
    intro v
    rw [hsmul]
    congr 1
    simp
  refine ⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2⟩ := hB σ hσ
    refine ⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩
    have : (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u
        = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u) := by
      rw [smul_sub, smul_smul, ← pow_add, add_comm m c₀]
      rfl
    rw [this, LinearMap.map_smul, h2 u, smul_zero]
  · intro y i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)
  · intro s y
    have hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y
        = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hpr, Matrix.mulVec_smul]
    rw [hYf]
    intro i
    have h := hY s y i
    unfold Cg at h ⊢
    have hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i -
        (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) -
            ((l : ℕ) : Qbar l) ^ m • b y)) i
        = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by
      simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ‖_‖ ≤ _
    simp only [Pi.smul_apply, smul_eq_mul] at hrw ⊢
    rw [hrw, norm_mul]
    calc _ ≤ 1 * ‖Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i‖ :=
          mul_le_mul_of_nonneg_right hlm (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h

end GlobalTheory.K4
end

