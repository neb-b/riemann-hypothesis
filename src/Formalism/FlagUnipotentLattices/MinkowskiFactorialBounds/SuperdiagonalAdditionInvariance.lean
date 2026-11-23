module

public import Formalism.FlagUnipotentLattices.Bundle0001
public import Mathlib
public import Formalism.SobolevGaussianKernels.StatementEI
public import Formalism.CorankShare.StatementFR

@[expose] public section

namespace Formalism.HermitianLatticeCounting.P.S4aux

open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset

theorem orbit_count_formula : OmCount := by
  intro P Om H hH
  calc (2:ℝ)^Om.card = ∏ p ∈ Om, (2:ℝ) := by simp
    _ ≤ ∏ p ∈ Om, H p := Finset.prod_le_prod₀ (fun _ _ => by norm_num) hH

theorem weighted_cauchy_schwarz : WeightedCS := by
  intro ι _ V _ v W hW
  calc ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (inv_pos.2 (hW i)).le)
        (fun i _ => mul_nonneg (hW i).le (sq_nonneg _)) (fun i _ => ?_)
      have := (hW i).ne'
      apply le_of_eq
      field_simp

theorem fourth_reduction_identity : Step4 := by
  intro P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen
  set 𝒜 := Om.powerset.filter (fun A => A.Nonempty) with h𝒜
  have hcard : (𝒜.card : ℝ) ≤ (2 : ℝ) ^ Om.card := by
    have : 𝒜.card ≤ 2 ^ Om.card := by
      rw [← Finset.card_powerset]; exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hHc : ∀ p, 0 < H p ^ c := fun p => pow_pos (lt_of_lt_of_le one_pos (hH p)) _

  have one : ∀ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
      ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    intro A hA
    obtain ⟨hAO, p0, hp0⟩ : A ⊆ Om ∧ A.Nonempty := by
      simpa [h𝒜, Finset.mem_filter, Finset.mem_powerset] using hA
    set g : P → ℝ := fun p => if p ∈ A then ((q p : ℝ) ^ κ)⁻¹ else 1 with hg
    have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
    have hq2 : ∀ p, ((q p : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ κ)⁻¹ := fun p => by
      apply inv_anti₀ (by positivity)
      gcongr
      exact_mod_cast hq p
    have h21 : ((2 : ℝ) ^ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hg1 : ∀ p, g p ≤ 1 := fun p => by
      simp only [hg]; split_ifs
      · exact (hq2 p).trans h21
      · exact le_rfl
    have hgp : ∏ p, g p ≤ ((2 : ℝ) ^ κ)⁻¹ := by
      rw [← Finset.mul_prod_erase univ g (Finset.mem_univ p0)]
      calc g p0 * ∏ p ∈ univ.erase p0, g p ≤ ((2 : ℝ) ^ κ)⁻¹ * 1 := by
            apply mul_le_mul
            · simp only [hg, if_pos hp0]; exact hq2 p0
            · exact Finset.prod_le_one₀ (fun p _ => hg0 p) (fun p _ => hg1 p)
            · exact Finset.prod_nonneg fun p _ => hg0 p
            · positivity
        _ = _ := mul_one _
    calc ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
        ≤ ∏ p, (H p ^ c * (H p ^ c * ngen p)) * g p := by
          refine Finset.prod_le_prod₀ (fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _))
            fun p _ => ?_
          have hb : H p ^ c * nn p ≤ H p ^ c * (H p ^ c * ngen p) :=
            mul_le_mul_of_nonneg_left (hgen p) (hHc p).le
          by_cases hp : p ∈ A
          · simp only [hg, if_pos hp]
            calc _ ≤ _ := hN p (hAO hp)
              _ = (H p ^ c * nn p) * ((q p : ℝ) ^ κ)⁻¹ := by ring
              _ ≤ _ := by gcongr
          · simp only [hg, if_neg hp, mul_one]
            exact (hZ p).trans hb
      _ = ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ∏ p, g p := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow, two_mul, pow_add]; ring
      _ ≤ ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ((2 : ℝ) ^ κ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hgp ?_
          refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _)
            (Finset.prod_nonneg fun p _ => ?_)
          have := (hnn p).trans (hgen p)
          exact nonneg_of_mul_nonneg_right this (hHc p)
      _ = _ := by ring
  have hR0 : 0 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (by positivity))
      (Finset.prod_nonneg fun p _ => ?_)
    have := (hnn p).trans (hgen p)
    exact nonneg_of_mul_nonneg_right this (hHc p)
  calc ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
          ((𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ‖(if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2) := by
        refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => hw p _)
        calc ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
            ≤ (∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖) ^ 2 := by
              gcongr; exact norm_sum_le _ _
          _ ≤ (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = _ := by
              congr 1
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [norm_prod, Finset.prod_pow]
    _ = (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 := by
        simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ (2 : ℝ) ^ Om.card * ∑ A ∈ 𝒜, (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
        apply mul_le_mul hcard (Finset.sum_le_sum one) _ (by positivity)
        exact Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw p x) (sq_nonneg _)
    _ = (2 : ℝ) ^ Om.card * ((𝒜.card : ℝ) * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Om.card * ((2 : ℝ) ^ Om.card * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        gcongr
    _ = _ := by
        have : (4 : ℝ) ^ Om.card = (2 : ℝ) ^ Om.card * (2 : ℝ) ^ Om.card := by
          rw [← mul_pow]; norm_num
        rw [this]; ring

section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction

end unfold

section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end dualcap

section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)

end sametrace

namespace Part2

end Part2

section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]

end dvrcard

section count
variable {F : Type} [Field F] [Fintype F]

end count

section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

end inert

section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

end inert2

section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)




end inert3

section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)



end inert4

section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end unram2

section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

end orth

section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

end unimod

section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)



end unimod2

section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]

end annih

section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)

end stdform

section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]






end hermjac

section hermjacA
variable {E : Type} [CommRing E]

end hermjacA

section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]

end hermjacA2

section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]


end hermjacB

end Formalism.HermitianLatticeCounting.P.S4aux

namespace Formalism.HermitianLatticeCounting.P

theorem orbit_count_formula : Formalism.HermitianLatticeCounting.S4.OmCount := S4aux.orbit_count_formula
theorem weighted_cauchy_schwarz : Formalism.HermitianLatticeCounting.S4.WeightedCS := S4aux.weighted_cauchy_schwarz
theorem fourth_reduction_identity : Formalism.HermitianLatticeCounting.S4.Step4 := S4aux.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.P
