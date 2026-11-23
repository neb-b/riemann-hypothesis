module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsFracOfAdjoinEqTop
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.Model

open GlobalTheory.PD

variable (k : Type) [Field k] (d : ℕ)

section Bundle

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

end Bundle

section Cover

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

def yc (i : Fin (d + 1)) : Fin d → F := fun j => x (i.succAbove j) / x i

theorem isFrac_of_adjoin_eq_top (S : Set F) (h : IntermediateField.adjoin k S = ⊤) :
    IsFractionRing (Algebra.adjoin k S) F := by
  refine IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_
  have hz : z ∈ IntermediateField.adjoin k S := h ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩

theorem ratio_mem_field (hx : ∀ i, x i ≠ 0) (i a : Fin (d + 1)) :
    x a / x i ∈ IntermediateField.adjoin k (Set.range (yc x i)) := by
  rcases eq_or_ne a i with rfl | h
  · rw [div_self (hx a)]
    exact IntermediateField.one_mem _
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩

theorem adjoin_yc_eq_top (hP : IsPd k x) (i : Fin (d + 1)) :
    IntermediateField.adjoin k (Set.range (yc x i)) = ⊤ := by
  rw [eq_top_iff, ← hP.gen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  show x j.succ / x 0 ∈ IntermediateField.adjoin k (Set.range (yc x i))

  have e : x j.succ / x 0 = (x j.succ / x i) / (x 0 / x i) := by
    rw [div_div_div_cancel_right₀ (hP.ne i)]
  rw [e]
  exact div_mem (ratio_mem_field k x hP.ne i _) (ratio_mem_field k x hP.ne i _)

theorem trdeg_eq (hP : IsPd k x) : Cardinal.mk (Fin d) ≤ Algebra.trdeg k F := by
  exact hP.indep.cardinalMk_le_trdeg

theorem indep_yc (hP : IsPd k x) (i : Fin (d + 1)) : AlgebraicIndependent k (yc x i) := by

  have : IsFractionRing (Algebra.adjoin k (Set.range (yc x i))) F :=
    isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (yc x i))) F :=
    IsLocalization.isAlgebraic F (nonZeroDivisors (Algebra.adjoin k (Set.range (yc x i))))
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k (yc x i) (trdeg_eq k x hP)).1

theorem rA_single_eq (hx : ∀ i, x i ≠ 0) (i : Fin (d + 1)) :
    rA k x {i} = Algebra.adjoin k (Set.range (yc x i)) := by
  unfold rA
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i', hi', j, rfl⟩
    rw [Finset.mem_singleton] at hi'
    subst hi'
    rcases eq_or_ne j i' with rfl | h
    · rw [div_self (hx j)]
      exact Subalgebra.one_mem _
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq h
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩

def chartEquiv (hP : IsPd k x) (i : Fin (d + 1)) : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i} :=
  (indep_yc k x hP i).aevalEquiv.trans (Subalgebra.equivOfEq _ _ (rA_single_eq k x hP.ne i).symm)

end Cover

section Extra

end Extra

end GlobalTheory.PD.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open ReciprocityTheory.GeometryOfNumbersTheory Matrix NumberField
open scoped ComplexOrder ComplexConjugate

variable {K E : Type*} [Field K] [Field E] {V V' : Type*} [AddCommGroup V] [Module K V]

section Complex

variable (h : HermFam K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]

def csq (c : ι → ℂ) (v : ι → V) : ℝ := (∑ i, ∑ k, conj (c i) * c k * h.form σ (v i) (v k)).re

def cnrm (c : ι → ℂ) (v : ι → V) : ℝ := Real.sqrt (csq h σ c v)

theorem csq_map (a : ι → K) (v : ι → V) :
    csq h σ (fun i => σ (a i)) v = (h.form σ (∑ i, a i • v i) (∑ i, a i • v i)).re := by
  rw [csq, h.form_sum_left]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [h.form_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [h.form_smul_left, h.smul_right, mul_assoc]

theorem cnrm_map (a : ι → K) (v : ι → V) : cnrm h σ (fun i => σ (a i)) v = h.nrm σ (∑ i, a i • v i) :=
  congrArg Real.sqrt (csq_map h σ a v)

theorem csq_comb {κ : Type*} [Fintype κ] (c : ι → ℂ) (a : ι → κ → K) (b : κ → V) :
    csq h σ c (fun i => ∑ k, a i k • b k) = csq h σ (fun k => ∑ i, c i * σ (a i k)) b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [csq, h.form_sum_left, h.form_sum_right, h.form_smul_left, h.smul_right, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2.1, t.2.2.2, t.2.1, t.1), fun t => (t.2.2.2, t.2.2.1, t.1, t.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring

theorem csq_nonneg (c : ι → ℂ) (v : ι → V) : 0 ≤ csq h σ c v := by
  let S := Submodule.span K (Set.range v)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K S
  have e : v = fun i => ∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • (b k : V) := funext fun i => by
    exact (congrArg S.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm).trans (map_sum _ _ _)
  rw [e, csq_comb]
  generalize (fun k => ∑ i, c i * σ _) = x
  have := (h.posDef σ _ _ (b.linearIndependent.map' S.subtype S.ker_subtype)).posSemidef.dotProduct_mulVec_nonneg x
  refine (Complex.nonneg_iff.1 this).1.trans_eq (congrArg _ ?_)
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

end Complex

def ofCoords {P : (K →+* ℂ) → Type*} [∀ σ, Fintype (P σ)] (φ : ∀ σ, V →ₛₗ[σ] (P σ → ℂ))
    (G : ∀ σ, Matrix (P σ) (P σ) ℂ) (hG : ∀ σ, (G σ).PosDef)
    (hφ : ∀ σ n (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun i => φ σ (v i)) :
    HermFam K V where
  form σ x y := star (φ σ x) ⬝ᵥ G σ *ᵥ φ σ y
  add_right σ x y z := by rw [map_add (f := _), mulVec_add, dotProduct_add]
  smul_right σ a x y := by rw [map_smulₛₗ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  conj_symm σ x y := by
    rw [starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec, (hG σ).1.eq, ← dotProduct_mulVec]
  posDef σ n v hv := by
    classical
    have := (hG σ).conjTranspose_mul_mul_same (B := Matrix.of fun p i => φ σ (v i) p)
      (Matrix.mulVec_injective_iff.2 (hφ σ n v hv))
    convert this using 1
    ext i j
    simp [dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V) (hf : Function.Injective f) :
    HermFam K V' where
  form σ x y := h.form σ (f x) (f y)
  add_right σ x y z := by rw [map_add (f := _), h.add_right]
  smul_right σ a x y := by rw [map_smul, h.smul_right]
  conj_symm σ x y := h.conj_symm σ _ _
  posDef σ n v hv := h.posDef σ n _ (hv.map' f (LinearMap.ker_eq_bot.2 hf))

theorem isConjInv_comap [AddCommGroup V'] [Module K V'] {h : HermFam K V} (hh : h.IsConjInv) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) : (comap h f hf).IsConjInv := fun σ _ _ => hh σ _ _

def basisCoords {n : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) : V →ₛₗ[σ] (n → ℂ) where
  toFun x i := σ (b.repr x i)
  map_add' x y := funext fun i => by simp
  map_smul' a x := funext fun i => by simp

theorem linearIndependent_basisCoords {n ι : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) {v : ι → V}
    (hv : LinearIndependent K v) : LinearIndependent ℂ fun i => basisCoords b σ (v i) :=
  letI := σ.toAlgebra
  linearIndependent_algebraMap_comp_iff.2 (hv.map' b.equivFun.toLinearMap b.equivFun.ker)

def ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) : HermFam K V :=
  ofCoords (P := fun _ => n) (basisCoords b) G hG fun σ _ _ => linearIndependent_basisCoords b σ

theorem form_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (i j : n) : (ofGram b G hG).form σ (b i) (b j) = G σ i j := by
  classical
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, Finsupp.single_apply, apply_ite]

theorem isConjInv_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) {G : (K →+* ℂ) → Matrix n n ℂ}
    (hG : ∀ σ, (G σ).PosDef) (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).IsConjInv := fun σ x y => by
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, hc]

def ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) : HermFam K V :=
  ofGram b (fun _ => 1) fun _ => PosDef.one

theorem nrm_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (σ : K →+* ℂ) (i : n) :
    (ofBasis b).nrm σ (b i) = 1 := by
  simp [HermFam.nrm, ofBasis, form_ofGram]

theorem isConjInv_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) :
    (ofBasis b).IsConjInv := isConjInv_ofGram b _ fun _ i j => by simp [Matrix.one_apply, apply_ite]

section Extend

variable [AddCommGroup V'] [Module E V'] {j : K →+* E}

structure IsExtension (ι : V →ₛₗ[j] V') : Prop where

  indep : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent E fun i => ι (v i)

  span : Submodule.span E (Set.range ι) = ⊤

variable {ι : V →ₛₗ[j] V'} (hι : IsExtension ι)

def IsExtension.basis {n : ℕ} (b : Module.Basis (Fin n) K V) : Module.Basis (Fin n) E V' :=
  Module.Basis.mk (hι.indep n b b.linearIndependent) (hι.span.ge.trans (Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))

variable [FiniteDimensional K V]


def extend (h : HermFam K V) : HermFam E V' :=
  ofGram (hι.basis (Module.finBasis K V)) (fun τ => h.gram (τ.comp j) (Module.finBasis K V))
    fun _ => h.posDef _ _ _ (Module.finBasis K V).linearIndependent

theorem isConjInv_extend {h : HermFam K V} (hh : h.IsConjInv) : (extend hι h).IsConjInv :=
  isConjInv_ofGram _ _ fun τ _ _ => hh (τ.comp j) _ _

end Extend

end GlobalTheory.HermTools
end
end

