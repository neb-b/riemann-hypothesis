module

public import Mathlib
public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
public import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.LengthQuotientLeOfLatticeSandwich

@[expose] public section

namespace Formalism.HermitianLattices.RamifiedHeckeModels

open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate

theorem prime_order_element : RationalMatrixPrimeOrderBound := by
  intro n p hp A hA h1
  classical
  haveI := Fact.mk hp
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hm0 : minpoly ℚ A ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ A ∣ Polynomial.cyclotomic p ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one ℚ p]
    apply minpoly.dvd
    simp [hA]
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) := Polynomial.cyclotomic.irreducible_rat hp.pos

  have hcd : Polynomial.cyclotomic p ℚ ∣ minpoly ℚ A := by
    by_contra hnd
    have hcop : IsCoprime (Polynomial.cyclotomic p ℚ) (minpoly ℚ A) := hirr.coprime_iff_not_dvd.2 hnd
    have hX : minpoly ℚ A ∣ Polynomial.X - 1 := hcop.symm.dvd_of_dvd_mul_left hdvd
    apply h1
    have h0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hX (minpoly.aeval ℚ A)
    simpa [sub_eq_zero] using h0
  have hle1 := Polynomial.natDegree_le_of_dvd hcd hm0
  have hle2 : (minpoly ℚ A).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hle1
  omega

section LemmaC

open Formalism.LogVandermondeBounds.product_first_zeroth_parts Module

section
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type} [AddCommGroup M] [Module R M]


set_option maxHeartbeats 800000 in
theorem length_quotient_bound_general (ϖ : R) (hϖ : Irreducible ϖ) (S S0 B : Submodule R M) (U D : M →ₗ[R] M)
    (e : ℕ) (hSB : S0 ≤ B) (hU : B.map U ≤ S) (hD : S.map D ≤ B)
    (hUD : ∀ s ∈ S, U (D s) = ϖ ^ e • s) [Module.Free R S] [Module.Finite R S] :
    Module.length R (S ⧸ (S0.map U).comap S.subtype) ≤
      Module.length R (B ⧸ S0.comap B.subtype) + (e * Module.finrank R S : ℕ) := by
  classical
  set T1 : Submodule R S := (S0.map U).comap S.subtype with hT1
  set T2 : Submodule R S := (B.map U).comap S.subtype with hT2
  have h12 : T1 ≤ T2 := Submodule.comap_mono (Submodule.map_mono hSB)
  set Q : Submodule R (S ⧸ T1) := T2.map T1.mkQ with hQ

  have hsplit : Module.length R (S ⧸ T1) = Module.length R Q + Module.length R ((S ⧸ T1) ⧸ Q) :=
    Module.length_eq_add_of_exact Q.subtype Q.mkQ Q.injective_subtype Q.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Q)
  rw [(Submodule.quotientQuotientEquivQuotient T1 T2 h12).length_eq] at hsplit

  have hlen2 : Module.length R (S ⧸ T2) ≤ (e * Module.finrank R S : ℕ) := by
    apply length_quot_le_of_pow_smul ϖ hϖ S T2 e
    intro x
    rw [hT2, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
    exact ⟨D x, hD (Submodule.mem_map_of_mem x.2), hUD x x.2⟩

  have hlen1 : Module.length R Q ≤ Module.length R (B ⧸ S0.comap B.subtype) := by
    let uB : B →ₗ[R] S := (U.domRestrict B).codRestrict S (fun b => hU (Submodule.mem_map_of_mem b.2))
    have huB : ∀ b : B, uB b ∈ T2 := fun b => by
      rw [hT2, Submodule.mem_comap]
      exact ⟨b, b.2, rfl⟩
    let ψ : B →ₗ[R] Q := (T1.mkQ ∘ₗ uB).codRestrict Q (fun b => Submodule.mem_map_of_mem (huB b))
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [hT2, Submodule.mem_comap] at hx
      obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 hx
      refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
      show T1.mkQ (uB ⟨b, hb⟩) = T1.mkQ x
      congr 1
      exact Subtype.ext hbx
    have hker : S0.comap B.subtype ≤ LinearMap.ker ψ := by
      intro b hb
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show T1.mkQ (uB b) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT1, Submodule.mem_comap]
      exact Submodule.mem_map_of_mem hb
    let φ := (S0.comap B.subtype).liftQ ψ hker
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨b, rfl⟩ := hψ y
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    exact Module.length_le_of_surjective φ hφ
  rw [hsplit]
  exact add_le_add hlen1 hlen2

end

theorem lemma_c_under_twist : LemmaC_twist := by
  intro R _ _ _ ϖ hϖ M _ _ S B U D e b hSB hU hD hUD _ _
  have hmap : (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).map U = S.map ((ϖ ^ b) • U) := by
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [← hmap]
  exact length_quotient_bound_general ϖ hϖ S _ B U D e hSB hU hD hUD

end LemmaC

end Formalism.HermitianLattices.RamifiedHeckeModels
