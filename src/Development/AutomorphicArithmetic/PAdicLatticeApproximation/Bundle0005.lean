module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.DenCoprimeIffOfMulPrimeToPRatio
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma den_coprime_of_mul_eq (p : ℕ) (u v : ℚ) (a b : ℕ) (hb : 0 < b) (hbp : b.Coprime p)
    (h : u * a = v * b) (hu : u.den.Coprime p) : v.den.Coprime p := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hv : v = u * Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    field_simp
    linarith [h]
  have h1 : (Rat.divInt (a : ℤ) (b : ℤ)).den ∣ b := by exact_mod_cast Rat.den_dvd a b
  have h2 := Rat.mul_den_dvd u (Rat.divInt (a : ℤ) (b : ℤ))
  rw [← hv] at h2
  exact Nat.Coprime.coprime_dvd_left (h2.trans (Nat.mul_dvd_mul_left _ h1)) (Nat.Coprime.mul_left hu hbp)

theorem UpperTheory.den_coprime_iff_of_mul_prime_to_p_ratio :
    ∀ (p : ℕ) [Fact p.Prime] (s s₁ : ℚ) (a b : ℕ), 0 < a → 0 < b → a.Coprime p → b.Coprime p → s₁ * a = s * b → ∀ y : ℚ, (s₁ * y).den.Coprime p ↔ (s * y).den.Coprime p := by
  intro p _ s s₁ a b ha hb hap hbp h y
  constructor
  · intro hu
    exact den_coprime_of_mul_eq p (s₁ * y) (s * y) a b hb hbp (by rw [mul_right_comm, h, mul_right_comm]) hu
  · intro hu
    exact den_coprime_of_mul_eq p (s * y) (s₁ * y) b a ha hap (by rw [mul_right_comm, ← h, mul_right_comm]) hu
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowMulIntOfIsIntAfAlgebraMap
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap :
    ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), IsIntAf (algebraMap ℚ (AfP p) q) → ∃ (r : ℕ) (z : ℤ), (p : ℚ) ^ r * q = z := by
  intro p hp q hq
  have hp' : p.Prime := hp.out
  obtain ⟨r, m, hmp, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp'.one_lt.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hden
      exact absurd hden q.den_nz
    · exact h
  have hmc : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp').mpr hmp).symm
  have hint : IsIntAf (algebraMap ℚ (AfP p) q * (p : AfP p) ^ r) := by
    intro v
    rw [map_mul, map_pow, map_natCast]
    exact mul_mem (hq v) (pow_mem (natCast_mem _ p) r)
  have hnum : ((q.num : ℤ) : ℚ) = (m : ℚ) * (q * (p : ℚ) ^ r) := by
    rw [← Rat.mul_den_eq_num]
    have : (q.den : ℚ) = (p : ℚ) ^ r * m := by exact_mod_cast hden
    rw [this]
    ring
  have hdvd : (m : ℤ) ∣ q.num := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p m hm0 hmc q.num _ hint
    rw [hnum, map_mul, map_mul, map_pow, map_natCast, map_natCast]
  have h1 : m ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
  have h2 : m ∣ q.den := ⟨p ^ r, by rw [hden, mul_comm]⟩
  have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 q.reduced) h2
  refine ⟨r, q.num, ?_⟩
  rw [← Rat.mul_den_eq_num]
  have : (q.den : ℚ) = (p : ℚ) ^ r := by
    rw [hden, hm1, mul_one]
    push_cast
    rfl
  rw [this, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.FiniteFreeOfBoundedDenominatorsLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private theorem UpperTheory.tensor_rat_injective_of_free {L : Type} [AddCommGroup L] [Module.Free ℤ L] :
    Function.Injective (TensorProduct.mk ℤ ℚ L (1 : ℚ)) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) :=
    fun a b h => by simpa using h
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L) (Algebra.linearMap ℤ ℚ) hf
  intro x y hxy
  apply (TensorProduct.lid ℤ L).symm.injective
  apply h
  simpa [LinearMap.rTensor_tmul] using hxy

theorem UpperTheory.finite_free_of_bounded_denominators_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a) → Module.Finite ℤ X.lat ∧ Module.Free ℤ X.lat := by
  intro p _ D X ⟨d, hd, h⟩
  haveI := D.freeLa
  haveI := D.finLa
  let ι : D.La →ₗ[ℤ] VQ D := TensorProduct.mk ℤ ℚ D.La (1 : ℚ)
  have hι : Function.Injective ι := UpperTheory.tensor_rat_injective_of_free
  let g : X.lat →ₗ[ℤ] VQ D := (d : ℤ) • (X.lat.toIntSubmodule.subtype)
  have hg : Function.Injective g := by
    intro u v huv
    have h1 : (d : ℤ) • (u : VQ D) = (d : ℤ) • (v : VQ D) := huv
    have hq : ((d : ℚ)) • (u : VQ D) = (d : ℚ) • (v : VQ D) := by
      simpa [Nat.cast_smul_eq_nsmul] using h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact Subtype.ext (smul_right_injective _ hd0 hq)
  have hr : ∀ w, g w ∈ LinearMap.range ι := by
    intro w
    obtain ⟨a, ha⟩ := h w w.2
    refine ⟨a, ?_⟩
    change (1 : ℚ) ⊗ₜ[ℤ] a = (d : ℤ) • (w : VQ D)
    rw [← ha]
    exact (natCast_zsmul (w : VQ D) d).symm
  let f : X.lat →ₗ[ℤ] D.La :=
    (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hr
  have hf : Function.Injective f := by
    intro u v huv
    apply hg
    have := (LinearEquiv.ofInjective ι hι).symm.injective huv
    exact congrArg Subtype.val this
  refine ⟨Module.Finite.of_injective f hf, ?_⟩
  exact Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.IntegralUnitCongrCoprimeIntMod
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.integral_unit_congr_coprime_int_mod :
    ∀ (p : ℕ) [Fact p.Prime] (ε : (AfP p)ˣ), IsIntAf (ε : AfP p) → IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p) → ∀ n : ℕ, 0 < n → n.Coprime p → ∃ (ν : ℤ) (b : AfP p), IsIntAf b ∧ (ε : AfP p) = (ν : AfP p) + (n : AfP p) * b ∧ IsCoprime ν (n : ℤ) := by
  intro p _ ε hε hε' n hn hnp
  obtain ⟨ν, b, hb, hνb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε
  obtain ⟨μ, b', hb', hμb⟩ := LaHatMod.exists_int_add_mul n hn hnp _ hε'
  refine ⟨ν, b, hb, hνb, ?_⟩
  have hint : IsIntAf ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    intro v
    simp only [map_add (f := _), map_mul, map_intCast, map_natCast]
    exact add_mem (add_mem (mul_mem (intCast_mem _ ν) (hb' v)) (mul_mem (intCast_mem _ μ) (hb v)))
      (mul_mem (mul_mem (natCast_mem _ n) (hb v)) (hb' v))
  have hprod : (1 : AfP p) = (ν : AfP p) * μ +
      n * ((ν : AfP p) * b' + (μ : AfP p) * b + (n : AfP p) * b * b') := by
    have : (ε : AfP p) * ((ε⁻¹ : (AfP p)ˣ) : AfP p) = 1 := Units.mul_inv ε
    rw [← this, hνb, hμb]
    ring
  have hdvd : (n : ℤ) ∣ 1 - ν * μ := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hnp _ _ hint
    rw [map_intCast, Int.cast_sub, Int.cast_one, Int.cast_mul]
    linear_combination hprod
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨μ, k, by linear_combination -hk⟩
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

private lemma exists_nsmul_mem_closure {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Set V) (w : V)
    (hw : w ∈ Submodule.span ℚ s) : ∃ k : ℕ, 0 < k ∧ k • w ∈ AddSubgroup.closure s :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure s w hw

theorem UpperTheory.p_lattice_saturated_and_cofinite :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)), UpperTheory.Gal.W2.IsPLat D M → (∀ (m : ℕ) (w : VQ D), m.Coprime p → m • w ∈ M → w ∈ M) ∧ ∀ w : VQ D, ∃ r : ℕ, p ^ r • w ∈ M := by
  intro p hp D M hM
  obtain ⟨-, s, hs, hmem⟩ := hM
  have hprime : p.Prime := hp.out
  refine ⟨?_, ?_⟩
  · intro m w hm hw
    obtain ⟨m', hm', hc⟩ := (hmem _).1 hw
    refine (hmem _).2 ⟨m' * m, Nat.Coprime.mul_left hm' hm, ?_⟩
    rwa [mul_smul]
  · intro w
    obtain ⟨k, hk, hkw⟩ := exists_nsmul_mem_closure (s : Set (VQ D)) w (by rw [hs]; trivial)
    obtain ⟨r, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hprime.ne_one
    refine ⟨r, (hmem _).2 ⟨k', ((Nat.Prime.coprime_iff_not_dvd hprime).2 hk').symm, ?_⟩⟩
    rw [smul_smul, mul_comm]
    exact hkw
end

