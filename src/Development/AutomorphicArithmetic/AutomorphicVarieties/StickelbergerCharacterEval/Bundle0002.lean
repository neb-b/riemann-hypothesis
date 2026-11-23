module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detprod
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.det_mul_quotientByOrderTwo_eq_prod_charEval :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A Ω (detR c ε z) = ∏ χ : Ch Ω c ε, ev A χ.1 z := by
  intro A _ Ω _ _ Γ _ _ _ c ε hc hc1 hε z
  classical
  have hcard := card_signedInvolutionChar_eq_card_involutionQuotient (Ω := Ω) c ε hc hc1 hε
  let e : Ch Ω c ε ≃ Qc c := Fintype.equivOfCardEq hcard
  let P : Matrix (Qc c) (Qc c) Ω := Matrix.of fun k i => ((e.symm k).1 (rep i) : Ω)
  let M : Matrix (Qc c) (Qc c) Ω := (algebraMap A Ω).mapMatrix (mat c ε z)
  let d : Qc c → Ω := fun k => ev A (e.symm k).1 z
  have hPM : P * M = Matrix.diagonal d * P := by
    ext k j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [P, M, d, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact sum_char_mul_quotientMatrix_eq_charEval_mul c ε hc hc1 (e.symm k) z j
  have hind : LinearIndependent Ω (fun k => P k) :=
    (linearIndependent_characters_on_quotientReps (Ω := Ω) c ε hc).comp e.symm e.symm.injective
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp hind
  have hdet : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P |>.mp hP).ne_zero
  have h2 : P.det * M.det = (∏ k, d k) * P.det := by
    rw [← Matrix.det_mul, hPM, Matrix.det_mul, Matrix.det_diagonal]
  have h3 : M.det = ∏ k, d k := by
    have := h2
    rw [mul_comm ((∏ k, d k))] at this
    exact mul_left_cancel₀ hdet this
  have h4 : algebraMap A Ω (detR c ε z) = M.det := by
    unfold detR
    rw [RingHom.map_det]
  rw [h4, h3]
  exact Equiv.prod_comp e.symm (fun χ => ev A χ.1 z)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsLinearEquivQuotientByOrderTwoCoords
section
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∃ e : Rq A c ε ≃ₗ[A] (Qc c → A), ∀ w : MonoidAlgebra A Γ, e (cls A c ε w) = coord c ε w := by
  intro A _ Γ _ _ c ε hc hc1 hε
  classical
  haveI : Fintype (Qc c) := Fintype.ofFinite (Qc c)
  let f : MonoidAlgebra A Γ →ₗ[A] (Qc c → A) :=
    { toFun := coord c ε
      map_add' := by
        intro x y
        funext i
        simp only [coord, MonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [coord, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
          RingHom.id_apply, Pi.smul_apply]
        ring }
  have hf : ∀ w, f w = coord c ε w := fun w => rfl
  have hker : LinearMap.ker f = (Ideal.span {rel A c ε}).restrictScalars A := by
    ext w
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_span_orderTwoRelation_iff_coords_eq_zero c ε hc hc1 hε, hf]
  have hrepinj : ∀ i i' : Qc c, rep i = rep i' → i = i' := by
    intro i i' h
    rw [← mk_rep i, ← mk_rep i', h]
  have hcrep : ∀ i i' : Qc c, rep i' ≠ c * rep i := by
    intro i i' h
    have e1 : i' = i := by
      rw [← mk_rep i', ← mk_rep i, h]
      exact ((mk_eq_mk hc (rep i) (c * rep i)).mpr (Or.inr rfl)).symm
    subst e1
    have e2 : c * rep i' = 1 * rep i' := by rw [← h, one_mul]
    exact hc1 (mul_right_cancel e2)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, MonoidAlgebra.single (rep i) (v i), ?_⟩
    funext i0
    rw [hf, coord]
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg (hcrep i0 i)]
    · intro i _ hi
      rw [if_neg (fun h => hi (hrepinj i i0 h))]
    · intro h
      exact absurd (Finset.mem_univ i0) h
  let e : Rq A c ε ≃ₗ[A] (Qc c → A) :=
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {rel A c ε})).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ f.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun w => rfl⟩
end

