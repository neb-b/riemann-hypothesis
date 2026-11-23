module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem powerSeries_expansion_image_dense_with_denominator {p : ℕ} [Fact p.Prime] (D : Datum p) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p)
    (z : AfP p ⊗[ℚ] VQ D) : ∃ (w : VQ D) (e : AfP p ⊗[ℚ] VQ D), e ∈ LaHat D ∧
      z = (1 : AfP p) ⊗ₜ[ℚ] w + N • e := by
  obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D z
  obtain ⟨x, e, he, hx⟩ := exists_inAf_add_nsmul_of_mem_laHat p D (t * N) (Nat.mul_pos ht0 hN)
    (Nat.Coprime.mul_left htc hNp) (t • z) ht
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ⟨(t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x), e, he, ?_⟩
  have h1 : t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x))) = inAf D x := by
    rw [inAf, ← Nat.cast_smul_eq_nsmul ℚ, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ ht', one_smul]
  have h2 : t • z = t • ((1 : AfP p) ⊗ₜ[ℚ] ((t : ℚ)⁻¹ • ((1 : ℚ) ⊗ₜ[ℤ] x)) + N • e) := by
    rw [hx, smul_add, h1, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ t, ← Nat.cast_smul_eq_nsmul ℚ t] at h2
  exact smul_right_injective _ ht' h2

theorem UpperTheory.Gal.W2.rdDense_of :
    UpperTheory.Gal.W2.RdDense := by
  intro p _ D G L x h₁ n hn z
  let T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)
  let S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
    actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁
  have hTS : T * S = 1 := by
    have e1 : actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C) *
        actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : L.actG h₁⁻¹ * L.actG h₁ = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    change (L.actG h₁⁻¹ * actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)) *
      (actOn L.rep (AfP p) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * L.actG h₁) = 1
    rw [_root_.mul_assoc, ← _root_.mul_assoc (actOn L.rep (AfP p) (x : AfP p ⊗[ℚ] G.C)), e1, _root_.one_mul, e2]
  obtain ⟨m, hm0, hmc, hm⟩ := DenEnd.exists_coprime_nsmul_map_mem p D T
  obtain ⟨k, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hn0 : 0 < n' := Nat.pos_of_ne_zero fun h => hn' (h ▸ dvd_zero p)
  have hnc : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn').symm
  obtain ⟨w, e, he, hz⟩ := powerSeries_expansion_image_dense_with_denominator D (n' * m) (Nat.mul_pos hn0 hm0) (Nat.Coprime.mul_left hnc hmc) (S z)
  have hint : IsIntAf (algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k)) := fun u => by
    rw [map_pow, map_pow]; exact pow_mem (DenEnd.isIntAf_inv u) k
  have hz2 : z = T (S z) := by
    rw [← Module.End.mul_apply, hTS]; rfl
  have hr : rd L x h₁ w = T ((1 : AfP p) ⊗ₜ[ℚ] w) := rfl
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨w, algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ k) • (m • T e), DenEnd.smul_mem D hint (hm e he), ?_⟩
  rw [hr, hz2, hz, map_add (f := _), map_nsmul]
  congr 1
  rw [algebraMap_smul, hnn]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hpk : (p : ℚ) ^ k * ((p : ℚ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
  push_cast
  linear_combination (-((n' : ℚ) * m)) * hpk
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mul_unit_eq_algebraMap_mul {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (xs : S) (x : Sˣ) (b bi : S)
    (t : A) (hb : bi * b = 1) (hx : (x : S) * b * xs = algebraMap A S t) :
    xs * (x : S) = algebraMap A S t * bi := by
  have hc : ∀ y : S, algebraMap A S t * y = y * algebraMap A S t := fun y => Algebra.commutes t y
  have h1 : xs = bi * ((↑x⁻¹ : S) * algebraMap A S t) := by
    rw [← hx, ← _root_.mul_assoc (↑x⁻¹ : S), ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
      _root_.one_mul, ← _root_.mul_assoc, hb, _root_.one_mul]
  rw [h1, _root_.mul_assoc, _root_.mul_assoc, hc, ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
    _root_.one_mul]
  exact (hc bi).symm

theorem UpperTheory.Gal.W2.rdForm_of :
    UpperTheory.Gal.W2.RdForm := by
  intro p _ D G L B h₁
  obtain ⟨t, ht⟩ := B.trivAf.choose_spec
  have hx : (↑(trivX B) : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ↑B.β *
      MulOpposite.unop ((starT G.star (AfP p)) ↑(trivX B)) = algebraMap (AfP p) _ ↑t := ht
  have key := mul_unit_eq_algebraMap_mul (A := AfP p) _ (trivX B) _ (inC G (AfP p) ↑B.β⁻¹) _
    (by rw [← map_mul, Units.inv_mul, map_one]) hx
  have hsh : sh G (↑B.β⁻¹ : G.C) = ↑B.β⁻¹ := by
    have h : sh G (↑B.β⁻¹ : G.C) * ↑B.β = 1 := by
      rw [← B.sym]
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    exact Units.mul_eq_one_iff_eq_inv.mp h
  refine ⟨(h₁⁻¹).1.2 * t, fun u w => ?_⟩
  unfold rd
  rw [actG_form_eq_sim, adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, key, map_mul,
    AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [inC, AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  rw [actOn_tmul_tmul', TensorProduct.smul_tmul', LinearMap.BilinForm.baseChange_tmul, formB,
    L.adj, hsh, Units.val_mul]
  simp only [smul_eq_mul]
  rw [Algebra.smul_def]
  ring
end

