module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
section
namespace KStar.Tree

variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

private theorem isUnit_of_not_dvd {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one c)
    (not_lt.1 fun h => hc ((PadicInt.norm_lt_one_iff_dvd c).1 h))

private theorem nuOf_mem (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ g, ¬ (l : ℤ_[l]) ^ (nuOf l ε n + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  obtain ⟨g, hg⟩ := h
  have hx : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    apply hg
    ext
    exact congrArg (fun x : ℤ_[l] => (x : Padic l)) h1
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨u, v, hxv⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = u * (l : ℤ_[l]) ^ v :=
    ⟨_, _, PadicInt.unitCoeff_spec hx⟩
  have hne : {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}.Nonempty := by
    refine ⟨v, g, ?_⟩
    intro hd
    rw [hxv, pow_succ, mul_comm (u : ℤ_[l])] at hd
    have hlu : (l : ℤ_[l]) ∣ u := (mul_dvd_mul_iff_left (pow_ne_zero v hl0)).1 hd
    have hlunit : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_unit hlu u.isUnit
    have h1 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    rw [PadicInt.isUnit_iff] at hlunit
    linarith
  exact Nat.sInf_mem hne

theorem pow_nuOf_dvd (g : Γ) : (l : ℤ_[l]) ^ nuOf l ε n ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos (nuOf l ε n) with h0 | hpos
  · rw [h0, pow_zero]
    exact one_dvd _
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hlt : k < nuOf l ε n := by omega
    have hnm : k ∉ {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1} :=
      Nat.notMem_of_lt_sInf hlt
    rw [hk]
    by_contra hd
    exact hnm ⟨g, hd⟩

theorem exists_eq_pow_nuOf_mul_unit (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ (g : Γ) (u : ℤ_[l]ˣ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = (l : ℤ_[l]) ^ nuOf l ε n * u := by
  obtain ⟨g, hg⟩ := nuOf_mem l ε n h
  obtain ⟨c, hc⟩ := pow_nuOf_dvd l ε n g
  refine ⟨g, (isUnit_of_not_dvd l (c := c) ?_).unit, ?_⟩
  · rintro ⟨d, rfl⟩
    exact hg ⟨d, by rw [hc]; ring⟩
  · rw [IsUnit.unit_spec]
    exact hc

theorem le_nuOf_iff (h : ∃ g, ε g ^ n ≠ 1) (k : ℕ) :
    k ≤ nuOf l ε n ↔ ∀ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  constructor
  · intro hk g
    exact (pow_dvd_pow _ hk).trans (pow_nuOf_dvd l ε n g)
  · intro hk
    by_contra hlt
    push_neg at hlt
    obtain ⟨g, hg⟩ := nuOf_mem l ε n h
    exact hg ((pow_dvd_pow _ hlt).trans (hk g))

theorem nuOf_pos_of_res (h : ∃ g, ε g ^ n ≠ 1) {K : Type} [CommRing K] [Nontrivial K] (θ : ℤ_[l] →+* K)
    (h1 : ∀ g, θ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1) : 0 < nuOf l ε n := by
  have key := (le_nuOf_iff l ε n h 1).2 ?_
  · omega
  intro g
  rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p]
  apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top θ)
  rw [RingHom.mem_ker, map_sub, map_pow, map_one, h1 g, sub_self]

end KStar.Tree
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
section
namespace KStar.Tree

variable (l : ℕ) [Fact l.Prime]

private theorem nsa_isUnit {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  by_contra hu
  have : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact hc this

private theorem nsa_dvd_iff (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

private theorem nsa_nat (k : ℕ) (m : ℕ) (h : (l : ℤ_[l]) ^ k ∣ (m : ℤ_[l])) : l ^ k ∣ m := by
  have := (PadicInt.pow_p_dvd_int_iff (p := l) k (m : ℤ)).1 (by simpa using h)
  exact_mod_cast this

private theorem nsa_lte (s n : ℕ) (hs : s ≠ 0) (hn : Odd n) :
    ¬ (l : ℤ) ^ (s + n.factorization l + 1) ∣ (1 + (l : ℤ) ^ s) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hxy : (l : ℤ) ∣ (1 + (l : ℤ) ^ s) - 1 := by
    simpa using dvd_pow_self (l : ℤ) hs
  have hx : ¬ (l : ℤ) ∣ 1 + (l : ℤ) ^ s := by
    intro h
    exact hpz.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ) hs)).1 h)
  have hs' : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) - 1) = s := by
    rw [add_sub_cancel_left]
    exact emultiplicity_pow_self_of_prime hpz s
  have key : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) ^ n - 1 ^ n) =
      ((s + n.factorization l : ℕ) : ℕ∞) := by
    by_cases hl : l = 2
    · have hnd : ¬ l ∣ n := by
        subst hl
        exact hn.not_two_dvd_nat
      rw [emultiplicity_pow_sub_pow_of_prime hpz hxy hx (by exact_mod_cast hnd), hs',
        Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
    · rw [Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hl) hxy hx n, hs',
        Nat.factorization_def n hp, Nat.cast_add, padicValNat_eq_emultiplicity hn0]
  rw [one_pow] at key
  intro h
  have := le_emultiplicity_of_pow_dvd h
  rw [key] at this
  have := Nat.cast_le.1 this
  omega

theorem nuOf_le_of_approx {Γ : Type} [Group Γ] (ε : Γ →* ℤ_[l]ˣ) (n m : ℕ) (u : ℤ_[l]ˣ)
    (h : ∀ k : ℕ, ∃ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - u)
    (hu : ¬ (l : ℤ_[l]) ^ (m + 1) ∣ (u : ℤ_[l]) ^ n - 1) : nuOf l ε n ≤ m := by
  obtain ⟨g, hg⟩ := h (m + 1)
  refine Nat.sInf_le ⟨g, fun hc => hu ?_⟩
  have h2 := hg.trans (sub_dvd_pow_sub_pow ((ε g : ℤ_[l]ˣ) : ℤ_[l]) (u : ℤ_[l]) n)
  have h3 := dvd_sub hc h2
  convert h3 using 1
  ring

theorem exists_unit_not_dvd (C n : ℕ) (hC : C ≠ 0) (h2 : 2 ∣ C) (hn : Odd n) :
    ∃ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ C.factorization l ∣ (u : ℤ_[l]) - 1 ∧
      ¬ (l : ℤ_[l]) ^ (C.factorization l + (if l ∣ C then n.factorization l else 0) + 1) ∣ (u : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  by_cases hlC : l ∣ C
  · rw [if_pos hlC]
    have hs : C.factorization l ≠ 0 := (hp.factorization_pos_of_dvd hC hlC).ne'
    generalize C.factorization l = s at hs ⊢
    have hU : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
      apply nsa_isUnit
      intro h
      exact PadicInt.prime_p.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ_[l]) hs)).1 h)
    refine ⟨hU.unit, by simp, fun h => nsa_lte l s n hs hn ?_⟩
    rw [← PadicInt.pow_p_dvd_int_iff]
    simpa using h
  · rw [if_neg hlC, Nat.factorization_eq_zero_of_not_dvd hlC]
    refine ⟨-1, by simp, fun h => hlC ?_⟩
    have e : ((-1 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = -((2 : ℕ) : ℤ_[l]) := by
      simp only [Units.val_neg, Units.val_one, hn.neg_one_pow]
      push_cast
      ring
    rw [e, dvd_neg] at h
    have := nsa_nat l _ _ h
    simp only [add_zero, zero_add, pow_one] at this
    exact this.trans h2

theorem exists_sq_unit_not_dvd (n : ℕ) (hn : ¬ (l - 1) / 2 ∣ n) (hl : l ≠ 2) :
    ∃ u : ℤ_[l]ˣ, ¬ (l : ℤ_[l]) ^ (0 + 1) ∣ ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hx : PadicInt.toZMod ((((g : ZMod l).val : ℕ)) : ℤ_[l]) = (g : ZMod l) := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hU : IsUnit ((((g : ZMod l).val : ℕ)) : ℤ_[l]) := by
    apply nsa_isUnit
    rw [nsa_dvd_iff, hx]
    exact g.ne_zero
  refine ⟨hU.unit, fun h => hn ?_⟩
  rw [zero_add, pow_one, nsa_dvd_iff, map_sub, map_one, map_pow, Units.val_pow_eq_pow_val, map_pow,
    IsUnit.unit_spec, hx, sub_eq_zero, ← pow_mul] at h
  have h1 : g ^ (2 * n) = 1 := by
    apply Units.ext
    simpa using h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hl
  have e1 : l - 1 = 2 * k := by omega
  rw [e1] at h2 ⊢
  rw [Nat.mul_div_cancel_left k two_pos]
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h2

end KStar.Tree
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
section
namespace KStar.Tree

open Polynomial IntermediateField in
private theorem totient_le_of_cyc_pow_eq_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) (h : ∀ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n = 1) (k : ℕ) :
    Nat.totient (l ^ k) ≤ Module.finrank ℚ E * n := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hl := (Fact.out : l.Prime)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hint : IsIntegral E ζ := (hζ.isIntegral (pow_pos hl.pos k)).tower_top
  set S : Finset ℤ_[l] := (Polynomial.nthRoots n (1 : ℤ_[l])).toFinset with hSdef
  have hS : S.card ≤ n := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  have hsub : ∀ r ∈ (minpoly E ζ).rootSet Ω, r ∈ S.image fun x => ζ ^ (PadicInt.toZModPow k x).val := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have hmin : minpoly E r = minpoly E ζ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr.2 (minpoly.monic hint)).symm
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hmin
    have hspec := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut Gal(Ω/E) Ω g) ζ hζ.pow_eq_one
    rw [Finset.mem_image]
    refine ⟨((cyc l E Ω g : ℤ_[l]ˣ) : ℤ_[l]), ?_, ?_⟩
    · rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn),
        ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · rw [← hg]
      exact hspec.symm
  have hdeg : (minpoly E ζ).natDegree ≤ n := by
    rw [← Polynomial.card_rootSet_eq_natDegree (K := Ω) (minpoly.irreducible hint).separable
      (IsAlgClosed.splits ((minpoly E ζ).map (algebraMap E Ω)))]
    calc Fintype.card ((minpoly E ζ).rootSet Ω) = ((minpoly E ζ).rootSet Ω).toFinset.card :=
          (Set.toFinset_card _).symm
      _ ≤ (S.image fun x => ζ ^ (PadicInt.toZModPow k x).val).card :=
          Finset.card_le_card fun x hx => hsub x (Set.mem_toFinset.1 hx)
      _ ≤ S.card := Finset.card_image_le
      _ ≤ n := hS
  haveI : FiniteDimensional E E⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ E⟮ζ⟯ := Module.Finite.trans E E⟮ζ⟯
  have hζF : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩ : E⟮ζ⟯) (l ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := (E⟮ζ⟯).val) hζ Subtype.val_injective
  have hq : (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ k) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζF (pow_pos hl.pos k)]
    exact minpoly.natDegree_le _
  calc (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := hq
    _ = Module.finrank ℚ E * Module.finrank E E⟮ζ⟯ := (Module.finrank_mul_finrank ℚ E E⟮ζ⟯).symm
    _ ≤ Module.finrank ℚ E * n := by
        apply Nat.mul_le_mul_left
        rw [IntermediateField.adjoin.finrank hint]
        exact hdeg

theorem exists_cyc_pow_ne_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) : ∃ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n ≠ 1 := by
  have hl := (Fact.out : l.Prime)
  by_contra hne
  push_neg at hne
  have key := totient_le_of_cyc_pow_eq_one l E Ω n hn hne (Module.finrank ℚ E * n + 1)
  rw [Nat.totient_prime_pow_succ hl] at key
  have h1 : Module.finrank ℚ E * n < l ^ (Module.finrank ℚ E * n) := Nat.lt_pow_self hl.one_lt
  have h2 : l ^ (Module.finrank ℚ E * n) ≤ l ^ (Module.finrank ℚ E * n) * (l - 1) :=
    Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hl.one_lt)
  omega

end KStar.Tree
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TwistTrace
section
namespace KStar.Tree

private theorem squareTopTwistPlaces_coprime_splitPlaces {S A : Type} [CommRing A] [IsLocalRing A] [Ring S] [Algebra A S] {r : ℕ}
    (f f' : S →ₐ[A] Matrix (Fin r) (Fin r) A) (hf : Function.Surjective f)
    (hf' : Function.Surjective f') (U U' : Matrix (Fin r) (Fin r) A)
    (h : ∀ z, (f z * U).trace = (f' z * U').trace) (z₀ : S) (u : A) (hz : f' z₀ = u • f z₀)
    (hu : IsUnit (f z₀).det) : (u ^ r - 1) • U = 0 := by
  classical
  let c : Ideal A := (Submodule.span A {U}).annihilator
  have hc : ∀ a, a ∈ c ↔ a • U = 0 := fun a => Submodule.mem_annihilator_span_singleton U a
  have key : ∀ z, f' z = 0 → ∀ i j, f z i j ∈ c := by
    intro z hz i j
    rw [hc]
    ext b a
    obtain ⟨p, hp⟩ := hf (Matrix.single a i 1)
    obtain ⟨q, hq⟩ := hf (Matrix.single j b 1)
    have h1 := h (p * z * q)
    rw [map_mul, map_mul, map_mul, map_mul, hz, hp, hq, Matrix.single_mul_mul_single,
      Matrix.trace_single_mul] at h1
    simpa using h1
  rw [← hc]
  by_cases htop : c = ⊤
  · rw [htop]; trivial
  have : Nontrivial (A ⧸ c) := Ideal.Quotient.nontrivial_iff.mpr htop
  have : IsLocalRing (A ⧸ c) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective
  let π : Matrix (Fin r) (Fin r) A →+* Matrix (Fin r) (Fin r) (A ⧸ c) :=
    (Ideal.Quotient.mk c).mapMatrix
  have hπ : Function.Surjective π := by
    intro y
    choose w hw using fun i j => Ideal.Quotient.mk_surjective (I := c) (y i j)
    exact ⟨Matrix.of w, by ext i j; simp [π, hw]⟩
  have hπs : ∀ (a : A) x, π (a • x) = Ideal.Quotient.mk c a • π x := by
    intro a x
    ext i j
    simp [π]
  choose s hs using fun i j : Fin r => hf' (Matrix.single i j 1)
  let L : Matrix (Fin r) (Fin r) (A ⧸ c) →ₗ[A ⧸ c] Matrix (Fin r) (Fin r) (A ⧸ c) :=
    { toFun := fun y => ∑ i, ∑ j, y i j • π (f (s i j))
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp [Finset.smul_sum, mul_smul] }
  have hL : ∀ z, L (π (f' z)) = π (f z) := by
    intro z
    have h0 : f' (z - ∑ i, ∑ j, f' z i j • s i j) = 0 := by
      rw [map_sub, sub_eq_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hs, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single _
    have h1 : π (f (z - ∑ i, ∑ j, f' z i j • s i j)) = 0 := by
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (key _ h0 i j)
    rw [map_sub, map_sub, sub_eq_zero] at h1
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hπs]
    rfl
  let θ : Matrix (Fin r) (Fin r) (A ⧸ c) →ₐ[A ⧸ c] Matrix (Fin r) (Fin r) (A ⧸ c) :=
    AlgHom.ofLinearMap L (by simpa using hL 1) (by
      intro x y
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, rfl⟩ := hπ y
      obtain ⟨x, rfl⟩ := hf' x
      obtain ⟨y, rfl⟩ := hf' y
      rw [← map_mul, ← map_mul, hL, hL, hL, map_mul, map_mul])
  have hd := det_algHom θ (π (f' z₀))
  have hθ : θ (π (f' z₀)) = π (f z₀) := hL z₀
  rw [hθ, hz, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_smul, map_mul] at hd
  have hu' : IsUnit (Ideal.Quotient.mk c (f z₀).det) := hu.map _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  rw [Fintype.card_fin] at hd
  exact hu'.mul_right_cancel (by rw [one_mul]; exact hd.symm)

theorem twist_smul_eq_zero (Γ A : Type) [Group Γ] [CommRing A] [IsLocalRing A] (r : ℕ)
    (T : Γ →* Matrix (Fin r) (Fin r) A) (χ : Γ →* A) (hspan : Submodule.span A (Set.range T) = ⊤)
    (U U' : Matrix (Fin r) (Fin r) A) (hU : ∀ g, (T g * U).trace = χ g * (T g * U').trace) (g₀ : Γ) :
    (χ g₀ ^ r - 1) • U = 0 := by
  classical
  let T' : Γ →* Matrix (Fin r) (Fin r) A :=
    { toFun := fun g => χ g • T g
      map_one' := by simp
      map_mul' := by
        intro g h
        simp [mul_smul, smul_comm (χ h) (χ g)] }
  let f : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A := MonoidAlgebra.lift A _ Γ T
  let f' : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A := MonoidAlgebra.lift A _ Γ T'
  have e : ∀ g, f (MonoidAlgebra.of A Γ g) = T g := fun g => MonoidAlgebra.lift_of _ _
  have e' : ∀ g, f' (MonoidAlgebra.of A Γ g) = χ g • T g := fun g => MonoidAlgebra.lift_of _ _
  have surj : ∀ F : MonoidAlgebra A Γ →ₐ[A] Matrix (Fin r) (Fin r) A,
      (∀ g, ∃ z, F z = T g) → Function.Surjective F := by
    intro F hF
    have : LinearMap.range F.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hF g
    exact LinearMap.range_eq_top.mp this
  refine squareTopTwistPlaces_coprime_splitPlaces f f' (surj f fun g => ⟨_, e g⟩) (surj f' fun g => ?_) U U' ?_
    (MonoidAlgebra.of A Γ g₀) (χ g₀) (by rw [e, e']) ?_
  · refine ⟨χ g⁻¹ • MonoidAlgebra.of A Γ g, ?_⟩
    rw [map_smul, e', smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · intro z
    induction z using MonoidAlgebra.induction_on with
    | of g => rw [e, e', hU, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    | add x y hx hy => simp only [map_add (f := _), Matrix.add_mul, Matrix.trace_add, hx, hy]
    | smul a x hx => simp only [map_smul, Matrix.smul_mul, Matrix.trace_smul, hx]
  · rw [e]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ((Group.isUnit g₀).map T)

end KStar.Tree
end

