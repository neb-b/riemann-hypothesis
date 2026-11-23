module

public import Mathlib
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0001
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0002
public import PositivityTheory.PublishedTheorems.WeilRepresentations.ZariskiDensity.QiCoreDefs

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCharP
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem pw_charP (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by
  induction r generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, pow_one, RingHom.mem_ker]
    have h := AlgHom.congr_fun (counit_pw Δ ε hL hR 1) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact RingHom.mem_ker.1 hx
  | succ r ih =>
    have hp : (p : H) = 0 := by
      rw [← map_natCast (algebraMap K H), CharP.cast_eq_zero K p, map_zero]
    have h2 : pw Δ ε p x ∈ RingHom.ker ε ^ 2 := by
      have := pw_sub_mem Δ ε hL hR p hx
      rwa [hp, zero_mul, sub_zero] at this
    have hcomp : pw Δ ε (p ^ (r + 1)) = (pw Δ ε (p ^ r)).comp (pw Δ ε p) := by
      rw [pow_succ]
      exact hmul _ _
    rw [hcomp, AlgHom.comp_apply]
    have hmap : Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε) ≤ RingHom.ker ε ^ (2 ^ r) :=
      Ideal.map_le_iff_le_comap.2 fun z hz => ih hz
    have hy : pw Δ ε (p ^ r) (pw Δ ε p x) ∈ Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ h2
    rw [Ideal.map_pow] at hy
    have h3 := Ideal.pow_right_mono hmap 2 hy
    rwa [← pow_mul, ← pow_succ] at h3

end PositivityTheory.PrwZar.Qi
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIdem
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx

end PositivityTheory.PrwZar.Qi
end
end

