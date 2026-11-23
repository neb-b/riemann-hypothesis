module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany
section
open Finset UpperTheory.V.Bern

private theorem nz_iff {R S : Type} [Field R] [Algebra ℚ R] [Field S] [Algebra ℚ S] {N : ℕ} [NeZero N]
    (f : R →+* S) (χ : DirichletCharacter R N) (k : ℕ) :
    ((χ.ringHomComp f : DirichletCharacter S N) (-1) = (-1) ^ k ↔ χ (-1) = (-1) ^ k) ∧
    (Bprim k (χ.ringHomComp f : DirichletCharacter S N) ≠ 0 ↔ Bprim k χ ≠ 0) ∧
    (genB k (χ.ringHomComp f : ZMod N → S) ≠ 0 ↔ genB k χ ≠ 0) := by
  have hinj : Function.Injective f := f.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [MulChar.ringHomComp_apply]
    have e : ((-1 : S)) ^ k = f ((-1 : R) ^ k) := by simp
    rw [e]
    exact hinj.eq_iff
  · rw [← b_primmap f hinj k χ]
    exact map_ne_zero_iff f hinj
  · rw [← map_genB_char f k χ]
    exact map_ne_zero_iff f hinj

theorem UpperTheory.V.Bern.b_nzany :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (χ : DirichletCharacter Ω N) (k : ℕ), 1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro Ω _ _ N _ χ k hk hχ
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let i : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let f : AlgebraicClosure ℚ →+* AlgebraicClosure Ω :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure Ω).toRingHom
  let g : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨ψ, -, hψ⟩ := (UpperTheory.V.Bern.b_charbij (N := N) f Set.univ).surjOn
    (show (χ.ringHomComp i : DirichletCharacter _ N) ∈ charSet (AlgebraicClosure Ω) Set.univ from Set.mem_univ _)
  obtain ⟨a1, a2, a3⟩ := nz_iff i χ k
  obtain ⟨b1, b2, b3⟩ := nz_iff f ψ k
  obtain ⟨c1, c2, c3⟩ := nz_iff g ψ k
  simp only at hψ
  rw [hψ] at b1 b2 b3
  obtain ⟨h1, h2⟩ := UpperTheory.V.Bern.b_nzC (ψ.ringHomComp g) k hk (c1.2 (b1.1 (a1.2 hχ)))
  exact ⟨a2.1 (b2.2 (c2.1 h1)), fun h => a3.1 (b3.2 (c3.1 (h2 h)))⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Prodint
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_prodint :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ M : ℤ, M ≠ 0 ∧ Real.log |(M : ℝ)| ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, (den N k : Ω) * Bprim k χ = (M : Ω) := by
  intro N _ k P hk hP
  obtain ⟨q, hq⟩ := b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by
    intro K Ω _ _ _ _ f χ
    simp only [map_mul, map_natCast]
    rw [b_primmap f f.injective])
  have hfin : (charSet ℂ P).Finite := Set.toFinite _
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]
    exact IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1
  have hint' : IsIntegral ℤ q := by
    have : (q : ℂ) = algebraMap ℚ ℂ q := rfl
    rw [this] at hint
    exact (isIntegral_algebraMap_iff ).mp hint
  obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hM' : (M : ℚ) = q := by simpa using hM
  subst hM'
  have hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ) := by
    rw [hC]; simp
  have hM0 : M ≠ 0 := by
    have : (M : ℂ) ≠ 0 := by
      rw [← hC']
      refine Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero ?_ ?_
      · exact Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne'
      · have hχ' : χ.toUnitHom.ker ∈ P := hfin.mem_toFinset.mp hχ
        exact (b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1
    exact_mod_cast this
  refine ⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩
  · have hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard := by
      have h1 : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
      rw [h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle
  · rw [hq Ω]; simp
end

