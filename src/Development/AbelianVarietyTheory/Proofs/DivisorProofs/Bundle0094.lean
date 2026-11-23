module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFields
section
open MvPolynomial

namespace GlobalTheory.PointTransfer

theorem exists_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    [Algebra.FiniteType F A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_common_zero {Ω τ : Type} [Field Ω] [IsAlgClosed Ω] [Finite τ]
    (I : Ideal (MvPolynomial τ Ω)) (hI : I ≠ ⊤) : ∃ y : τ → Ω, ∀ f ∈ I, aeval y f = 0 := by
  by_contra h
  have he : zeroLocus Ω I = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h ⟨y, fun f hf => hy f hf⟩
  have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I
  rw [he, MvPolynomial.vanishingIdeal_empty] at h2
  exact hI (Ideal.radical_eq_top.1 h2.symm)

noncomputable def partialEval {F A σ τ : Type} [CommRing F] [CommRing A] [Algebra F A] (u : σ → A) :
    MvPolynomial (σ ⊕ τ) F →ₐ[F] MvPolynomial τ A :=
  aeval (Sum.elim (fun s => C (u s)) X)

theorem eval₂Hom_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (y : τ → B) (g : MvPolynomial (σ ⊕ τ) F) :
    eval₂Hom (ψ : A →+* B) y (partialEval u g) = aeval (Sum.elim (fun s => ψ (u s)) y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem map_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (g : MvPolynomial (σ ⊕ τ) F) :
    MvPolynomial.map (ψ : A →+* B) (partialEval u g) = partialEval (fun s => ψ (u s)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem solvable_transfer (F σ τ : Type) [Field F] [Finite σ] [Finite τ]
    (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F))
    (H : ∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) →
      ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω)
    (hu : ∀ g ∈ P, aeval u g = 0) :
    ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  have hI : J.map (partialEval (F := F) (τ := τ) u) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω)
        ((partialEval (F := F) (τ := τ) u) '' (J : Set _)) := by
      have : (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F := F) (τ := τ) u) := by
        rw [htop]; trivial
      exact this
    obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
    choose g' hg'J hg' using fun i => (g i).2
    let S : Set Ω := Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)
    have hS : S.Finite :=
      (Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)
    let A : Subalgebra F Ω := Algebra.adjoin F S
    haveI : Algebra.FiniteType F A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
    obtain ⟨ψ⟩ := exists_algHom_algebraicClosure F A
    let uA : σ → A := fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩
    have hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ := τ) (A.val : A →+* Ω)) := by
      intro i
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩
    choose c' hc' using hc
    have hid : ∑ i, c' i * partialEval uA (g' i) = 1 := by
      apply MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_one, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]
      rfl
    obtain ⟨y, hy⟩ := H (fun s => ψ (uA s)) (by
      intro p hp
      have h0 : aeval uA p = 0 := by
        apply Subtype.val_injective
        have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p
        exact this.trans (hu p hp)
      have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p
      rw [← this, AlgHom.comp_apply, h0, map_zero])
    have := congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_sum, Finset.sum_eq_zero] at this
    · exact zero_ne_one this
    · intro i _
      rw [map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]
  obtain ⟨y, hy⟩ := exists_common_zero _ hI
  refine ⟨y, fun g hg => ?_⟩
  have h := hy _ (Ideal.mem_map_of_mem _ hg)
  have h2 := eval₂Hom_partialEval (AlgHom.id F Ω) u y g
  exact h2.symm.trans h

end GlobalTheory.PointTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOne
section
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianForms
section
open Matrix

namespace GlobalTheory.HermGram

noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])

theorem reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl

theorem reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by
  simp only [reForm_apply]
  have : star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]; ring
  rw [← this]; simp

theorem gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext k l
    simp only [conjTranspose_apply, of_apply, star_trivial]
    exact reForm_symm hH (e l) (e k)
  · intro x hx
    set v : Fin g → ℂ := ∑ k, x k • e k with hvdef
    have hv : v ≠ 0 := by
      intro h0
      apply hx
      apply e.equivFun.symm.injective
      rw [map_zero, Module.Basis.equivFun_symm_apply]
      exact h0
    have key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x
        = reForm H v v := by
      rw [hvdef]
      change star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [reForm_symm hH (e l) (e k)]; ring
    rw [key, reForm_apply]
    exact hpos v hv

theorem gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, Matrix.mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
      LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂

end GlobalTheory.HermGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectors
section
namespace GlobalTheory

open Module.End

theorem pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional {E H I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsSymmetric) (hc : ∀ i j, Commute (T i) (T j))
    (j u : E →ₗ[ℂ] H)
    (hu : ∀ (m : I → ℝ) (y : E), (∀ i, T i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, inner ℂ (j x) (u y) = (c : ℂ) * inner ℂ x y)
    (x : E) (hx : x ≠ 0) : (inner ℂ (j x) (u x)).im = 0 ∧ 0 < (inner ℂ (j x) (u x)).re := by
  classical
  have htop : (⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i)) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT (fun a b _ => hc a b)
  have hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have key : ∀ (χ : I → ℂ) (y : ↥(⨅ i, eigenspace (T i) (χ i))), ∃ c : ℝ, 0 < c ∧
      ∀ z, inner ℂ (j z) (u y) = (c : ℂ) * inner ℂ z (y : E) := by
    intro χ y
    apply hu (fun i => (χ i).re) (y : E)
    intro i
    have hmem : (y : E) ∈ eigenspace (T i) (χ i) := (Submodule.mem_iInf _).mp y.2 i
    have hy : T i y = χ i • (y : E) := mem_eigenspace_iff.mp hmem
    by_cases h0 : (y : E) = 0
    · simp [h0]
    · have hr := (hT i).conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hmem, h0⟩)
      have hre : ((χ i).re : ℂ) = χ i := Complex.conj_eq_iff_re.mp hr
      rw [hy, hre]
  have hx' : x ∈ ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hs
  choose c hc0 hcx using key
  have hself : ∀ χ ∈ s, inner ℂ x (μ χ : E) = ((‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    rw [← hμ, sum_inner, Finset.sum_eq_single χ]
    · rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · intro ψ _ hψ
      simpa using hO hψ (μ ψ) (μ χ)
    · intro h; exact absurd hχ h
  have hux : u x = ∑ χ ∈ s, u (μ χ : E) := by rw [← hμ, map_sum]
  have hval : inner ℂ (j x) (u x) = ((∑ χ ∈ s, c χ (μ χ) * ‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hux, inner_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hcx, hself χ hχ, Complex.ofReal_mul]
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  obtain ⟨χ, hχ, hne⟩ : ∃ χ ∈ s, (μ χ : E) ≠ 0 := by
    by_contra hcon
    apply hx
    rw [← hμ]
    exact Finset.sum_eq_zero fun χ hχ => by_contra fun h => hcon ⟨χ, hχ, h⟩
  exact Finset.sum_pos' (fun ψ _ => mul_nonneg (hc0 _ _).le (sq_nonneg _))
    ⟨χ, hχ, mul_pos (hc0 _ _) (pow_pos (norm_pos_iff.mpr hne) 2)⟩

theorem pos_of_pos_mul_inner_on_joint_eigenvectors :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  intro V _ _ H _ _ ι hι W hW I T hTW hsym hcomm u hu x hxW hx0
  let e : W ≃ₗ[ℂ] W.map ι := Submodule.equivMapOfInjective ι hι W
  have : FiniteDimensional ℂ (W.map ι) := e.finiteDimensional
  let T' : I → (W.map ι) →ₗ[ℂ] (W.map ι) := fun i =>
    e.toLinearMap ∘ₗ (T i).restrict (hTW i) ∘ₗ e.symm.toLinearMap
  have hesymm : ∀ z : W.map ι, ι (e.symm z : V) = (z : H) := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have hTe : ∀ i (z : W.map ι), (e.symm (T' i z) : V) = T i (e.symm z) := by
    intro i z
    simp [T']
  have hT'coe : ∀ i (z : W.map ι), (T' i z : H) = ι (T i (e.symm z)) := by
    intro i z
    rw [← hesymm (T' i z), hTe]
  have hsym' : ∀ i, (T' i).IsSymmetric := by
    intro i a b
    change inner ℂ (T' i a : H) (b : H) = inner ℂ (a : H) (T' i b : H)
    rw [hT'coe, hT'coe, ← hesymm a, ← hesymm b]
    exact hsym i _ _
  have hc' : ∀ i k, Commute (T' i) (T' k) := by
    intro i k
    refine LinearMap.ext fun z => e.symm.injective (Subtype.ext ?_)
    rw [Module.End.mul_apply, Module.End.mul_apply]
    simp only [hTe]
    exact LinearMap.congr_fun (hcomm i k) _
  let u' : (W.map ι) →ₗ[ℂ] H := u ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hu' : ∀ (m : I → ℝ) (y : W.map ι), (∀ i, T' i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ z, inner ℂ ((W.map ι).subtype z) (u' y) = (c : ℂ) * inner ℂ z y := by
    intro m y hy
    have hy' : ∀ i, T i (e.symm y) = (m i : ℂ) • (e.symm y : V) := by
      intro i
      rw [← hTe, hy i, map_smul, Submodule.coe_smul]
    obtain ⟨c, hc, hcx⟩ := hu m (e.symm y) (e.symm y).2 hy'
    refine ⟨c, hc, fun z => ?_⟩
    have h := hcx (e.symm z) (e.symm z).2
    rw [hesymm z, hesymm y] at h
    exact h
  have hne : e ⟨x, hxW⟩ ≠ 0 := by
    intro h
    apply hx0
    have h2 : ((e ⟨x, hxW⟩ : W.map ι) : H) = 0 := by rw [h]; rfl
    exact hι ((show ι x = 0 from h2).trans (map_zero ι).symm)
  have hmain := pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional T' hsym' hc' (W.map ι).subtype u' hu'
    (e ⟨x, hxW⟩) hne
  have h1 : (W.map ι).subtype (e ⟨x, hxW⟩) = ι x := rfl
  have h2 : u' (e ⟨x, hxW⟩) = u x := by simp [u']
  rw [h1, h2] at hmain
  exact hmain

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCardLeNormProd
section
namespace GlobalTheory.RootNormLowerBound

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 < ε) (s : Multiset ℂ)
    (h : ∀ t ∈ s, ε ≤ ‖t‖) : ε ^ Multiset.card s ≤ ‖(s.map (fun a => -a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ,
      mul_comm (ε ^ Multiset.card s)]
    exact mul_le_mul ha ih' (by positivity) (norm_nonneg _)

theorem exists_root_norm_lt {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖F.coeff (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by
  by_contra hcon
  have hall : ∀ t ∈ F.roots, ε ≤ ‖t‖ := fun t ht =>
    le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩
  have h1 := pow_card_le_norm_prod hε F.roots hall
  have hc : F.coeff 0 = (F.roots.map fun a => -a).prod := by
    rw [(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [IsAlgClosed.card_roots_eq_natDegree, ← hc] at h1
  linarith

end GlobalTheory.RootNormLowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDivMemOfEsymmPowDivMem
section
open Polynomial

namespace GlobalTheory

theorem pow_div_mem_of_esymm_pow_div_mem (K : Type) [Field K] (V : ValuationSubring K)
    (A : Type) [Fintype A] (x : A → K) (D : ℕ) (c : K) (hc : c ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card A →
      k ∣ D ∧ (Finset.univ.val.map x).esymm k ^ (D / k) / c ∈ V) (a : A) :
    x a ^ D / c ∈ V := by
  classical
  set v := V.valuation with hv
  set s : Multiset K := Finset.univ.val.map x with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have hn : 1 ≤ Multiset.card s := hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c := by
    intro y
    rw [← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]
  rw [mem_iff]
  by_contra hlt
  push_neg at hlt
  rw [Valuation.map_pow] at hlt
  have key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k := by
    intro k hk1 hkn
    obtain ⟨hkD, hmem⟩ := h k hk1 (hcard ▸ hkn)
    rw [mem_iff, Valuation.map_pow] at hmem
    by_contra hge
    push_neg at hge
    have hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k) := pow_le_pow_left₀ zero_le' hge _
    rw [← pow_mul, Nat.mul_div_cancel' hkD] at hp
    exact absurd (hp.trans hmem) (not_le.mpr hlt)
  have hpos : 0 < v (x a) := by
    have := key 1 le_rfl hn
    rw [pow_one] at this
    exact lt_of_le_of_lt zero_le' this
  have h0 : (s.map fun t => X - C t).prod.eval (x a) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]
    simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
    exact Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at h0
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul,
    Nat.sub_zero] at h0
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0, one_mul, ← eq_neg_iff_add_eq_zero] at h0
  have hlt2 : v (∑ j ∈ Finset.range (Multiset.card s),
      (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')
    intro j hj
    have hj' : j + 1 ≤ Multiset.card s := Finset.mem_range.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v (s.esymm (j + 1)) * v (x a) ^ (Multiset.card s - (j + 1))
        < v (x a) ^ (j + 1) * v (x a) ^ (Multiset.card s - (j + 1)) :=
          mul_lt_mul_of_pos_right (key (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hj') (pow_pos hpos _)
      _ = v (x a) ^ Multiset.card s := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [h0, Valuation.map_neg, map_pow] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory
end

