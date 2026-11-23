module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitant
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Move

section General

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fv_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    fv F (γ *ᵥ v) = fm F γ *ᵥ fv F v := by
  funext i
  simp only [fv, fm, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, TensorProduct.tmul_sum]

theorem fv_smul (s : E) (v : Fin n → E) :
    fv F (s • v) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] s : RA F E) • fv F v := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_sub]

theorem nsmul_cancel {M : ℕ} (hM : 0 < M) {x y : Fin n → RA F E} (h : M • x = M • y) : x = y := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun z => (M : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hM'] using this

end General

section Ideals

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem span_smul_le (s : 𝓞 E) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {s} • A ≤ B ↔ ∀ v ∈ A, s • v ∈ B := by
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact h v hv

theorem exists_nat_coprime (s : 𝓞 E) (N : ℕ)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → (N : 𝓞 E) ∉ P) :
    ∃ k : ℕ, k.Coprime N ∧ s ∣ (k : 𝓞 E) := by
  set I : Ideal ℤ := (Ideal.span {s}).comap (algebraMap ℤ (𝓞 E)) with hI
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  refine ⟨a.natAbs, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun p hp hpa hpN => ?_
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).2 hp'
    have hle : I ≤ Ideal.span {(p : ℤ)} := by
      rw [ha]
      exact Ideal.span_singleton_le_span_singleton.2 (Int.natCast_dvd.2 hpa)
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
      (Ideal.span {s}) hle
    refine h Q hQp (hQ (Ideal.mem_span_singleton_self s)) ?_
    have : ((N : ℕ) : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change ((N : ℕ) : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc, Ideal.mem_span_singleton]; exact_mod_cast hpN
    simpa using this
  · have h1 : s ∣ ((a : ℤ) : 𝓞 E) := by
      have := haI
      rw [hI, Ideal.mem_comap, Ideal.mem_span_singleton] at this
      simpa using this
    have h2 : ((a : ℤ) : 𝓞 E) ∣ ((a.natAbs : ℤ) : 𝓞 E) :=
      map_dvd (Int.castRingHom (𝓞 E)) (Int.dvd_natAbs.2 dvd_rfl)
    rw [Int.cast_natCast] at h2
    exact h1.trans h2

theorem smul_mem_of_dvd {s t : 𝓞 E} (h : s ∣ t) {B : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E}
    (hv : s • v ∈ B) : t • v ∈ B := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_smul]
  exact B.smul_mem c hv

end Ideals

section Unimod

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hermE_one (x y : Fin n → E) :
    hermE (IsCMField.complexConj E) 1 x y = ∑ j, IsCMField.complexConj E (y j) * x j := by
  simp [hermE, Matrix.one_apply, mul_comm]

theorem unimod_move (γ : GL (Fin n) E) (hγ : IsUnE (IsCMField.complexConj E) 1 γ.1) (Λ Λ' : GenLat E n)
    (h : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) (hU : Λ.Unimod) : Λ'.Unimod := by
  have hs : ∀ v : Fin n → E, ∃ u, v = γ.1 *ᵥ u := fun v =>
    ⟨(γ⁻¹).1 *ᵥ v, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  intro v
  obtain ⟨u, rfl⟩ := hs v
  rw [← h, hU u]
  constructor
  · intro H w hw
    obtain ⟨x, rfl⟩ := hs w
    rw [← hermE_one, hγ, hermE_one]
    exact H x ((h x).2 hw)
  · intro H x hx
    have := H _ ((h x).1 hx)
    rwa [← hermE_one, hγ, hermE_one] at this

end Unimod

end GlobalTheory.UnRep.Move
