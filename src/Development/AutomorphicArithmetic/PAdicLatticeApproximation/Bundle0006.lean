module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDivOfREqSmulCompletedLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_div_of_r_eq_smul_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (w : VQ D) (n : ℕ) (e : AfP p ⊗[ℚ] VQ D), w ∈ X.lat → 0 < n → n.Coprime p → e ∈ LaHat D → X.r w = n • e → ∃ u ∈ X.lat, w = n • u := by
  intro p _ D X w n e hw hn hc he hr
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hwu : w = n • ((n : ℚ)⁻¹ • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hru : X.r ((n : ℚ)⁻¹ • w) = e := by
    rw [map_smul, hr, ← Nat.cast_smul_eq_nsmul ℚ n, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨(n : ℚ)⁻¹ • w, ⟨(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).1 n _ hc ?_, ?_⟩, hwu⟩
  · rw [← hwu]; exact hw.1
  · rw [hru]; exact he
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDualVectorOfIntegralFunctional
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_dual_vector_of_integral_functional :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (g : VQ D →ₗ[ℚ] ℚ), (∀ u ∈ X.lat, ∃ z : ℤ, g u = z) → ∃ w ∈ X.M, ∀ u, X.s * X.B w u = g u := by
  intro p _ D X g hg
  have := D.finLa
  have hnd : X.B.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (LinearMap.IsAlt.isRefl X.alt)).mpr X.nondeg
  let w0 := (X.B.toDual hnd).symm g
  have hB : ∀ u, X.B w0 u = g u := by
    intro u
    exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) g u
  have hw : ∀ u, X.s * X.B (X.s⁻¹ • w0) u = g u := by
    intro u
    rw [map_smul, LinearMap.smul_apply, hB, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ X.s_pos.ne', one_mul]
  refine ⟨X.s⁻¹ • w0, ?_, hw⟩
  rw [X.perf]
  intro u hu
  rw [hw]
  obtain ⟨t, ht0, htp, htm⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r u)
  have hlat : t • u ∈ X.lat :=
    X.mem_lat.mpr ⟨X.M.nsmul_mem hu t, by simpa only [map_nsmul] using htm⟩
  obtain ⟨z, hz⟩ := hg _ hlat
  rw [map_nsmul, nsmul_eq_mul] at hz
  have ht : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hq : g u = (z : ℚ) / (t : ℚ) := by
    rw [eq_div_iff ht, mul_comm, hz]
  have hd := Rat.den_dvd z t
  rw [Rat.divInt_eq_div] at hd
  push_cast at hd
  rw [hq]
  exact Nat.Coprime.coprime_dvd_left (Int.natCast_dvd_natCast.mp hd) htp
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsLatticeApproxModNCompletedLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_lattice_approx_mod_n_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ), 0 < n → n.Coprime p → ∀ a : D.La, ∃ u ∈ X.lat, ∃ e ∈ LaHat D, X.r u = inAf D a + n • e := by
  intro p hp D X n hn hnp a
  obtain ⟨w, e₀, he₀, h⟩ := X.dense n hn (inAf D a)
  rw [← X.r_apply] at h
  have hrw : X.r w ∈ LaHat D := by
    have h2 : X.r w = inAf D a - n • e₀ := eq_sub_of_add_eq h.symm
    rw [h2]
    exact sub_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a) (AddSubgroup.nsmul_mem _ he₀ n)
  obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
  have hphi : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : (p ^ Nat.totient n) ^ k ≡ 1 [MOD n] := by
    simpa using (Nat.ModEq.pow_totient hnp.symm).pow k
  have hle : k ≤ Nat.totient n * k := Nat.le_mul_of_pos_left k hphi
  have ht1 : 1 ≤ p ^ (Nat.totient n * k) := Nat.one_le_pow _ _ hp0
  obtain ⟨q, hq⟩ : n ∣ p ^ (Nat.totient n * k) - 1 :=
    (Nat.modEq_iff_dvd' ht1).1 (by rw [pow_mul]; exact hmod.symm)
  have ht : p ^ (Nat.totient n * k) = 1 + n * q := by omega
  have hM : p ^ (Nat.totient n * k) • w ∈ X.M := by
    have h3 : p ^ (Nat.totient n * k) = p ^ (Nat.totient n * k - k) * p ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h3, mul_smul]
    exact AddSubgroup.nsmul_mem _ hk _
  have hr : X.r (p ^ (Nat.totient n * k) • w) = inAf D a + n • (q • X.r w - e₀) := by
    rw [map_nsmul, ht, add_smul, one_smul, mul_smul, smul_sub, h]
    generalize n • q • X.r w = y
    generalize n • e₀ = z
    abel
  refine ⟨p ^ (Nat.totient n * k) • w, ?_, q • X.r w - e₀, ?_, hr⟩
  · refine X.mem_lat.2 ⟨hM, ?_⟩
    rw [hr]
    exact add_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a)
      (AddSubgroup.nsmul_mem _ (sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀) n)
  · exact sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowSmulEqOfMemCompletedLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_smul_eq_of_mem_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w : VQ D), (1 : AfP p) ⊗ₜ[ℚ] w ∈ LaHat D → ∃ (r : ℕ) (a : D.La), p ^ r • w = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D w hw
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := b.baseChange ℚ
  have hint : ∀ i, IsIntAf (algebraMap ℚ (AfP p) (B.repr w i)) := by
    intro i
    have h := GlobalTheory.LKGeo.LatDvd.isIntAf_adBasis_repr b i hw
    have e : (GlobalTheory.LKGeo.LatDvd.adBasis b).repr ((1 : AfP p) ⊗ₜ[ℚ] w) i
        = algebraMap ℚ (AfP p) (B.repr w i) := by
      simp only [GlobalTheory.LKGeo.LatDvd.adBasis, Module.Basis.baseChange_repr_tmul]
      rw [Algebra.algebraMap_eq_smul_one]
    rwa [e] at h
  choose r z hz using fun i => UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p (B.repr w i) (hint i)
  let R : ℕ := Finset.univ.sup r
  have hR : ∀ i, r i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  let a : D.La := ∑ i, ((p : ℤ) ^ (R - r i) * z i) • b i
  refine ⟨R, a, B.ext_elem fun i => ?_⟩
  have ha : b.repr a i = (p : ℤ) ^ (R - r i) * z i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [a, map_sum, Finsupp.single_apply]
  have e2 : B.repr ((1 : ℚ) ⊗ₜ[ℤ] a) i = ((b.repr a i : ℤ) : ℚ) := by
    simp [B, Module.Basis.baseChange_repr_tmul]
  rw [e2, ha, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  rw [← hz i]
  have : (p : ℚ) ^ R = (p : ℚ) ^ (R - r i) * (p : ℚ) ^ r i := by
    rw [← pow_add, Nat.sub_add_cancel (hR i)]
  rw [this]
  ring
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.LatticeSaturatedAtPAndPrimeToP
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.lattice_saturated_at_p_and_prime_to_p :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∀ w : VQ D, X.r w ∈ LaHat D → ∃ k : ℕ, p ^ k • w ∈ X.lat) ∧ (∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat) ∧ ∀ w : VQ D, ∃ m : ℕ, m ≠ 0 ∧ m • w ∈ X.lat := by
  intro p hp D X
  have hpp : p.Prime := hp.out
  have h2 : ∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat := by
    intro w hw
    obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r w)
    refine ⟨t, ht0, htc, nsmul_mem hw t, ?_⟩
    rw [map_nsmul]
    exact ht
  refine ⟨?_, h2, ?_⟩
  · intro w hw
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    refine ⟨k, hk, ?_⟩
    rw [map_nsmul]
    exact nsmul_mem hw _
  · intro w
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    obtain ⟨t, ht0, -, ht⟩ := h2 _ hk
    refine ⟨t * p ^ k, Nat.mul_ne_zero ht0.ne' (pow_ne_zero _ hpp.ne_zero), ?_⟩
    rw [mul_smul]
    exact ht
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ScaledFormDenEqOneOnLattice
section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.scaled_form_den_eq_one_on_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (u w : VQ D), u ∈ X.lat → w ∈ X.lat → (X.s * X.B u w).den = 1 := by
  intro p _ D X u w hu hw
  have hu' : u ∈ X.M ∧ X.r u ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hu
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hu
  have hw' : w ∈ X.M ∧ X.r w ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hw
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hw
  have hint : IsIntAf (algebraMap ℚ (AfP p) (X.s * X.B u w)) := by
    rw [X.form u w]
    exact AdelicSim.isInt_mul X.ε_int (AdelicSim.formInt D hu'.2 hw'.2)
  have hcop : (X.s * X.B u w).den.Coprime p := (X.perf u).mp hu'.1 w hw'.1
  obtain ⟨r, z, hz⟩ := UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p _ hint
  set q : ℚ := X.s * X.B u w with hq
  have e : ((p : ℤ) ^ r * q.num : ℤ) = z * q.den := by
    have h : ((p : ℚ) ^ r * q.num : ℚ) = z * q.den := by
      rw [← hz, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast h
  have hdvd : (q.den : ℤ) ∣ (p : ℤ) ^ r * q.num := ⟨z, by rw [e]; ring⟩
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  have h2 : q.den ∣ p ^ r := (Nat.Coprime.symm q.reduced).dvd_of_dvd_mul_right hdvd
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right r hcop) h2
end

