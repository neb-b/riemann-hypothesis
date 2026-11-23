module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_pos_nat_clearing_rat_denominators {κ : Type} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ k, ∃ z : ℤ, (M : ℚ) * q k = z := by
  refine ⟨∏ k, (q k).den, Finset.prod_pos fun k _ => (q k).pos, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun k => (q k).den) (Finset.mem_univ k)
  refine ⟨m * (q k).num, ?_⟩
  rw [hm]
  push_cast
  calc ((q k).den : ℚ) * m * q k = m * (q k * (q k).den) := by ring
    _ = m * (q k).num := by rw [Rat.mul_den_eq_num]


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.adelicPair_elementary : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), _root_.GlobalTheory.ClassFin.AdelicPair R R₀ → (∀ M : ℕ, 0 < M → ∀ r ∈ R₀, ∃ z : ℤ, ∃ a ∈ R₀, r = (z : R) + (M : R) * a) ∧ (∀ (κ : Type) [Fintype κ] (r : κ → R), ∃ M : ℕ, 0 < M ∧ ∀ k, (M : R) * r k ∈ R₀) ∧ Function.Injective (algebraMap ℚ R) := by
  intro R _ _ R₀ hR
  refine ⟨fun M hM r hr => ?_, fun κ _ r => ?_, ?_⟩
  · obtain ⟨q, a, ha, hra⟩ := hR.approx M hM r
    have hq : algebraMap ℚ R q ∈ R₀ := by
      have h : algebraMap ℚ R q = r - (M : R) * a := by rw [hra]; ring
      rw [h]
      exact R₀.sub_mem hr (R₀.mul_mem (natCast_mem R₀ M) ha)
    obtain ⟨z, rfl⟩ := hR.int_of_mem q hq
    exact ⟨z, a, ha, by rw [hra, map_intCast]⟩
  · choose q a ha hra using fun k => hR.approx 1 one_pos (r k)
    obtain ⟨M, hM, hMq⟩ := exists_pos_nat_clearing_rat_denominators q
    refine ⟨M, hM, fun k => ?_⟩
    obtain ⟨z, hz⟩ := hMq k
    have h : (M : R) * r k = (z : R) + (M : R) * a k := by
      rw [hra k, Nat.cast_one, one_mul, mul_add, ← map_natCast (algebraMap ℚ R) M, ← map_mul, hz,
        map_intCast]
    rw [h]
    exact R₀.add_mem (intCast_mem R₀ z) (R₀.mul_mem (natCast_mem R₀ M) (ha k))
  · have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := hR.int_of_mem (1 / 2)
        (by rw [Subsingleton.elim (algebraMap ℚ R (1 / 2)) 0]; exact R₀.zero_mem)
      have h2 : (1 : ℚ) = 2 * z := by rw [← hz]; norm_num
      have h3 : (1 : ℤ) = 2 * z := by exact_mod_cast h2
      omega
    exact (algebraMap ℚ R).injective

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsLogKronecker
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  obtain ⟨U', d', hU', rfl, rfl⟩ := h'
  refine ⟨U ⊗ₖ U', fun p => d p.1 + d' p.2, ?_, ?_, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hU', one_kronecker_one]
  · have e : (diagonal (fun p : ι × κ => ((d p.1 + d' p.2 : ℝ) : ℂ))) =
        diagonal (fun i => (d i : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
          (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun i => (d' i : ℂ)) := by
      rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
        diagonal_add]
      congr 1
      funext p
      rw [Complex.ofReal_add, mul_one, one_mul]
    rw [e, conjTranspose_kronecker, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      hU, hU']
  · have e : (diagonal (fun p : ι × κ => ((Real.exp (d p.1 + d' p.2) : ℝ) : ℂ))) =
        diagonal (fun i => (Real.exp (d i) : ℂ)) ⊗ₖ diagonal (fun i => (Real.exp (d' i) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext p
      rw [Real.exp_add, Complex.ofReal_mul]
    rw [e, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem harm_kronecker : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ) (g' : σ → Matrix κ κ ℂ), Harm g → Harm g' → Harm (fun s => g s ⊗ₖ g' s) := by
  intro ι _ _ κ _ _ σ _ g g' ⟨H, hH, hs⟩ ⟨H', hH', hs'⟩
  refine ⟨fun s => H s ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H' s, fun s => ?_, ?_⟩
  · have := isLog_kronecker (hH s) (hH' s)
    simpa only [conjTranspose_kronecker, ← mul_kronecker_mul] using this
  · ext ⟨i, k⟩ ⟨j, l⟩
    have h1 : ∑ s, H s i j = 0 := by
      have := congrFun (congrFun hs i) j
      simpa [Matrix.sum_apply] using this
    have h2 : ∑ s, H' s k l = 0 := by
      have := congrFun (congrFun hs' k) l
      simpa [Matrix.sum_apply] using this
    simp only [Matrix.sum_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, h1, h2, Matrix.zero_apply]
    simp

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNilpotentTmulSubTmulOfConstOnFibres
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem isNilpotent_of_forall_algHom_eq_zero (T : Type) [CommRing T] [Algebra ℂ T]
    [Algebra.FiniteType ℂ T] (x : T) (h : ∀ ω : T →ₐ[ℂ] ℂ, ω x = 0) : IsNilpotent x := by
  have hJ : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := ℂ)
  have h1 : x ∈ Ideal.jacobson (⊥ : Ideal T) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    let := Ideal.Quotient.field m
    have hfin : Module.Finite ℂ (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ m)
    have hb : Function.Bijective (algebraMap ℂ (T ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : ℂ ≃ₐ[ℂ] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ m)) hb
    have := h ((e.symm : (T ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
    have h0 : e.symm (Ideal.Quotient.mk m x) = 0 := this
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ e.symm.injective).mp h0)
  have h2 : x ∈ Ideal.radical (⊥ : Ideal T) := by
    have := IsJacobsonRing.out hJ (Ideal.radical_isRadical (⊥ : Ideal T))
    rw [← this]
    exact Ideal.jacobson_mono Ideal.le_radical h1
  exact h2

theorem isNilpotent_tmul_sub_tmul_of_const_on_fibres :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  intro B A _ _ _ _ _ _ _ f h
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  have : Algebra.FiniteType A (A ⊗[B] A) := inferInstance
  have : Algebra.FiniteType ℂ (A ⊗[B] A) := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  apply isNilpotent_of_forall_algHom_eq_zero
  intro ω
  let l : A →ₐ[ℂ] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[ℂ] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars ℂ
  have := h (ω.comp l) (ω.comp r) (fun b => by
    simp only [AlgHom.comp_apply, l, r, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
  rw [map_sub, sub_eq_zero]
  exact this

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.coord_indep
    (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (a b : F)
    (hab : algebraMap F E a + algebraMap F E b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq
    refine ⟨-a / b, (algebraMap F E).injective ?_⟩
    have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
    have hθ : θ = -algebraMap F E a / algebraMap F E b := by
      field_simp
      linear_combination hab
    rw [← h.sq, hθ]
    simp [map_div₀, map_neg]
    ring
  subst hb
  refine ⟨(algebraMap F E).injective ?_, rfl⟩
  simpa using hab

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
theorem _root_.GlobalTheory.QNorm.IsQuad.root_ne_zero (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp

end


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by
  intro F E _ _ _ _ δ θ σ h
  have t1 := h.coord_indep
  have hθ := h.root_ne_zero
  have hc := h.conj
  have hs := h.sq
  refine ⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    simp [AlgEquiv.commutes, hc]
  · intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc] at hx
    have := t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)
    have hb : b = 0 := by simpa using this.2
    exact ⟨a, by simp [hb]⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    refine ⟨a, b, ?_⟩
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hs
  · intro x hx
    by_cases h1 : x = -1
    · refine ⟨θ, hθ, ?_⟩
      rw [hc, h1, div_neg, div_self hθ]
    · have hy : (1 + x) ≠ 0 := fun h0 => h1 (by linear_combination h0)
      have hσy : σ (1 + x) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ σ.injective]
      refine ⟨1 + x, hy, ?_⟩
      rw [eq_div_iff hσy, map_add (f := _), map_one]
      linear_combination hx
  · rintro u ⟨y, hy⟩
    obtain ⟨a, b, rfl⟩ := h.span y
    have := t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
      linear_combination hy + (algebraMap F E b) ^ 2 * hs)
    have h2 : a * b = 0 := by
      have h3 := this.2
      have h4 : (2 : F) * (a * b) = 0 := by linear_combination -h3
      simpa using h4
    have hu : u = a ^ 2 + b ^ 2 * δ := by linear_combination this.1
    rcases mul_eq_zero.1 h2 with ha | hb
    · right; exact ⟨b * δ, by rw [hu, ha]; ring⟩
    · left; exact ⟨a, by rw [hu, hb]; ring⟩
  · have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply t1
      simpa [Algebra.smul_def] using hst
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Matrix.range_cons_cons_empty]
      refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
      simp [Algebra.smul_def]
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionIsGaloisAndEmbedding
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem quad_unique {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) {a b c d : F}
    (e : algebraMap F E a + algebraMap F E b * θ = algebraMap F E c + algebraMap F E d * θ) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    by_contra hne
    have h0 : b - d ≠ 0 := sub_ne_zero.mpr hne
    have h0' : algebraMap F E (b - d) ≠ 0 := by
      exact (map_ne_zero _).2 h0
    have hθ : θ = algebraMap F E ((c - a) / (b - d)) := by
      rw [map_div₀, eq_div_iff h0', map_sub, map_sub]
      linear_combination e
    apply h.nonsq
    refine ⟨(c - a) / (b - d), (algebraMap F E).injective ?_⟩
    rw [map_mul, ← hθ, ← h.sq, sq]
  refine ⟨(algebraMap F E).injective ?_, hbd⟩
  rw [hbd] at e
  exact add_right_cancel e

theorem isQuad_galois_and_embedding : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → IsGalois F E ∧ (∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) ∧ ∀ (L : Type) [Field L] (φ : F →+* L) (r : L), r ^ 2 = φ δ → ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  intro F E _ _ _ _ δ θ σ h
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F E := by
      classical
      refine ⟨⟨{1, θ}, ?_⟩⟩
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Finset.coe_pair, Submodule.mem_span_pair]
      exact ⟨a, b, by simp [Algebra.smul_def]⟩
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    have h1 : σ (algebraMap F E a + algebraMap F E b * θ)
        = algebraMap F E a + algebraMap F E b * θ :=
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_top _)
    rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj] at h1
    have h2 : algebraMap F E a + algebraMap F E (-b) * θ
        = algebraMap F E a + algebraMap F E b * θ := by
      rw [← h1, map_neg]; ring
    have h3 := (quad_unique h h2).2
    have hb : b = 0 := by linear_combination (-1/2 : F) * h3
    rw [hb, map_zero, zero_mul, add_zero]
    exact IntermediateField.algebraMap_mem _ a
  · intro τ
    have h1 : τ θ ^ 2 = θ ^ 2 := by
      rw [← map_pow, h.sq, AlgEquiv.commutes]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · left
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e]
    · right
      ext x
      obtain ⟨a, b, rfl⟩ := h.span x
      simp [e, h.conj]
  · intro L _ φ r hr
    choose A B hAB using h.span
    have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
        A x = a ∧ B x = b := fun x a b e => quad_unique h ((hAB x).symm.trans e)
    have hal : ∀ a : F, φ (A (algebraMap F E a)) + φ (B (algebraMap F E a)) * r = φ a := by
      intro a
      obtain ⟨h1, h2⟩ := key (algebraMap F E a) a 0 (by simp)
      simp [h1, h2]
    refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
              map_one' := by simpa using hal 1
              map_zero' := by simpa using hal 0
              map_add' := ?_
              map_mul' := ?_ }, hal, ?_⟩
    · intro x y
      obtain ⟨h1, h2⟩ := key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
        have hx := hAB x
        have hy := hAB y
        have hs := h.sq
        simp only [map_add (f := _), map_mul]
        linear_combination y * hx + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hy
          + algebraMap F E (B x) * algebraMap F E (B y) * hs)
      simp only [h1, h2, map_add (f := _), map_mul]
      linear_combination (-(φ (B x) * φ (B y))) * hr
    · intro x y
      obtain ⟨h1, h2⟩ := key (x + y) (A x + A y) (B x + B y) (by
        have hx := hAB x
        have hy := hAB y
        simp only [map_add (f := _)]
        linear_combination hx + hy)
      simp only [h1, h2, map_add (f := _)]
      ring
    · obtain ⟨h1, h2⟩ := key θ 0 1 (by simp)
      simp [h1, h2]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IwasawaDecompositionRealMatrix
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_orthogonal_mul_upper (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (k r : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i j, j < i → r i j = 0) ∧ g = k * r := by
  classical
  let f : Fin N → EuclideanSpace ℝ (Fin N) := fun j => WithLp.toLp 2 (fun i => g i j)
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨Matrix.of fun i j => b j i, Matrix.of fun i j => inner ℝ (b i) (f j), ?_, ?_, ?_⟩
  · ext i j
    have := orthonormal_iff_ite.mp b.orthonormal i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← this, PiLp.inner_apply]
    simp [mul_comm]
  · intro i j hij
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hij
  · ext i j
    have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    calc g i j = f j i := rfl
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem iwasawa_real : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  intro N g hg
  obtain ⟨k, r, hk, hr, rfl⟩ := exists_orthogonal_mul_upper N g
  have hbt : r.BlockTriangular id := fun i j hij => hr i j hij
  have hdet : r.det ≠ 0 := by
    intro h0
    apply hg
    rw [Matrix.det_mul, h0, mul_zero]
  rw [Matrix.det_of_isUpperTriangular hbt, Finset.prod_ne_zero_iff] at hdet
  have hne : ∀ i, r i i ≠ 0 := fun i => hdet i (Finset.mem_univ i)
  have habs : ∀ i, |r i i| ≠ 0 := fun i => abs_ne_zero.mpr (hne i)
  refine ⟨k * diagonal (fun i => r i i / |r i i|), fun i => |r i i|,
    Matrix.of fun i j => r i j / r i i, ?_, fun i => abs_pos.mpr (hne i), ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk,
      Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [div_mul_div_comm, abs_mul_abs_self, div_self (mul_ne_zero (hne i) (hne i))]
  · intro i
    exact div_self (hne i)
  · intro i j hij
    simp [hr i j hij]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.of_apply]
    have h1 := hne i
    have h2 := habs i
    field_simp

end GlobalTheory.ClassFin
end

