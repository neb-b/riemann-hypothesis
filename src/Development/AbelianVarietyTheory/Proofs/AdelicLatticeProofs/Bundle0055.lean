module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleBaseChange

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV Formalism.UG Formalism.UG.P

theorem exists_tensor_finiteAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E, (∀ x : E, ι (1 ⊗ₜ[F] x) = algebraMap E _ x) ∧ (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (α : FiniteAdeleRing (𝓞 F) F), α v = 1 → (∀ v', v' ≠ v → α v' = 0) → ∀ P : HeightOneSpectrum (𝓞 E), ι (α ⊗ₜ[F] 1) P = if P.under (𝓞 F) = v then 1 else 0 := by
  intro F E _ _ _ _ _
  obtain ⟨ι, hι⟩ := exists_toAd F E
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* AfE F E :=
    (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun v α h1 h0 P => ?_⟩
  · rw [hj, hc, map_tmul_one hι]
  · have : j y ∈ intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        rw [hj, hc]
        exact map_mem_int hι (levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ RInt F E := mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, hr i, g i, ?_⟩
    rw [hc']
  · rw [hj, hc, hι, map_one, one_mul, adMap_apply]
    split_ifs with h
    · subst h
      rw [h1, map_one]
    · rw [h0 _ h, map_zero]

end GlobalTheory.AdeleBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupportStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_adelic_decomposition_split_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)), IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧ (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_rep_suppSplit | exact GlobalTheory.UnRep.exists_rep_suppSplit | (intros; apply GlobalTheory.UnRep.exists_rep_suppSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfIsCyclic
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem np_of_finrank_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : NP F E := by
  intro x _ _
  refine ⟨algebraMap F E x, ?_⟩
  rw [Algebra.norm_algebraMap, h, pow_one]

theorem np_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (hp : p.Prime) (h : Module.finrank F E = p) :
    NP F E := by
  by_cases h2 : p = 2
  · exact _root_.GlobalTheory.CNorm.np_of_finrank_two F E (h2 ▸ h)
  · exact _root_.GlobalTheory.CNorm.np_of_odd_prime_degree p F E hp h2 h

theorem hasseNormPrinciple_cyclic_of_finrank (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = n → IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ hn hG hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_cases h1 : n = 1
  · exact np_of_finrank_one F E (hn.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = n := (IsGalois.card_aut_eq_finrank F E).trans hn
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p (hcard ▸ hpn)
  set H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g with hH
  have hHc : Nat.card H = p := by rw [hH, Nat.card_zpowers, hg]
  have : H.Normal := by
    constructor
    intro a ha b
    have hc : b * a = a * b := by
      obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
      obtain ⟨i, rfl⟩ := hs a
      obtain ⟨j, rfl⟩ := hs b
      exact (Commute.zpow_zpow_self s j i).eq
    rw [hc, mul_inv_cancel_right]
    exact ha
  let M : IntermediateField F E := IntermediateField.fixedField H
  have : NumberField M := NumberField.of_module_finite F M
  have hME : Module.finrank M E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hHc
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hFM : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
  have hCM : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) M)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hmul : Module.finrank F M * Module.finrank M E = n :=
    (Module.finrank_mul_finrank F M E).trans hn
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hlt : Module.finrank F M < n := by
    rw [← hmul, hME]
    exact lt_mul_of_one_lt_right hpos hp.one_lt
  exact _root_.GlobalTheory.CNorm.np_of_cyclic_tower F M E hC (np_of_finrank_prime p M E hp hME) (ih _ hlt F M rfl hFM hCM)

theorem np_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E :=
  fun F E _ _ _ _ _ hG hC => hasseNormPrinciple_cyclic_of_finrank _ F E rfl hG hC

end GlobalTheory.CNorm
end

