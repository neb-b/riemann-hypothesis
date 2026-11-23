module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.Bundle0003
public import GroundTheory.GlobalFields.TateThesis.TateMain
public import GroundTheory.GlobalFields.TateThesis.Bundle0009

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem vecMul_vecMul_inv (x : Fin 2 → 𝔸[K]) (h : GL (Fin 2) 𝔸[K]) :
    (x ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) ᵥ*
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = x := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

theorem continuous_inv_entry (i j : Fin 2) :
    Continuous fun h : GL (Fin 2) 𝔸[K] ↦
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j := by
  exact Units.continuous_coe_inv.matrix_elem i j

private theorem mul_mem_idealFiniteAdeles_of_mem_integral {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x a : 𝔸ᶠ[K]}
    (hx : x ∈ idealFiniteAdeles I) (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a * x ∈ idealFiniteAdeles I := by
  change ∀ v, Valued.v ((a * x) v) ≤ _
  intro v
  have h1 : Valued.v (x v) ≤ WithZero.exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
    hx v
  have h2 : Valued.v (a v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (ha v)
  have h3 : (a * x) v = a v * x v := rfl
  rw [h3, Valuation.map_mul]
  calc Valued.v (a v) * Valued.v (x v) ≤ 1 * Valued.v (x v) := mul_le_mul' h2 le_rfl
    _ ≤ _ := by rw [one_mul]; exact h1

private theorem mem_idealFiniteAdeles_one_of_mem_integral {a : 𝔸ᶠ[K]} (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  change ∀ v, Valued.v (a v) ≤ _
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  exact (mem_adicCompletionIntegers _ _ _).mp (ha v)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K])
    {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      (∀ i, finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set S : Set 𝔸ᶠ[K] := ((⋃ i : Fin 2, ⋃ j : Fin 2,
      (fun h : GL (Fin 2) 𝔸[K] =>
        finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j)) '' C) ∪
      Set.range b) ∪ {1} with hS
  have hSc : IsCompact S :=
    ((isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hC.image (continuous_finRingHom.comp (continuous_inv_entry i j))).union
      (isCompact_range continuous_of_discreteTopology)).union isCompact_singleton
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hSc
  have hL0 : ((I : FractionalIdeal (𝓞 K)⁰ K) ⊔ 1) ≠ 0 := by
    intro h0
    have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 0 := h0 ▸ le_sup_right
    exact one_ne_zero (le_antisymm h1 (FractionalIdeal.zero_le _))
  set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 _ hL0 with hLdef
  have hIL : (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0]; exact le_sup_left)
  have h1L : (idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0, Units.val_one]; exact le_sup_right)
  set e : K := algebraMap (𝓞 K) K d with he_def
  have he : e ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hE0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (e⁻¹ * e⁻¹) * (L : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr
      (mul_ne_zero (inv_ne_zero he) (inv_ne_zero he))) (Units.ne_zero L)
  refine ⟨Units.mk0 _ hE0, fun h hh ξ hξ i => ?_⟩
  set y := finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) with hy
  have hrec : (fun i => algebraMap K 𝔸ᶠ[K] (ξ i)) =
      y ᵥ* ((((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])).map finRingHom) := by
    rw [hy, ← finPart_vecMul, vecMul_vecMul_inv, finPart_algebraMap]
  have hξi : algebraMap K 𝔸ᶠ[K] (ξ i) = ∑ j, y j *
      finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) := by
    rw [congrFun hrec i]
    rfl
  set E : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] e with hEdef
  have hE1 : E ∈ integralFiniteAdeles (𝓞 K) K := by
    have := hd 1 (Or.inr rfl)
    rwa [mul_one] at this
  have hEs : ∀ j, E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) ∈
      integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ⟨h, hh, rfl⟩⟩⟩)))
  have hEb : ∀ j, E * b j ∈ integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inr ⟨j, rfl⟩))
  have hmemL : algebraMap K 𝔸ᶠ[K] (e * e * ξ i) ∈ idealFiniteAdeles L := by
    rw [map_mul, map_mul, hξi, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have hsplit : E * E * (y j * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) :
        Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) =
        (E * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i))) *
          (y j - b j) +
        (E * b j) * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) := by
      ring
    rw [hsplit]
    refine add_mem (hIL (mul_mem_idealFiniteAdeles_of_mem_integral (hξ j) (mul_mem hE1 (hEs j)))) ?_
    exact h1L (mem_idealFiniteAdeles_one_of_mem_integral (mul_mem (hEb j) (hEs j)))
  have hmem : e * e * ξ i ∈ (L : FractionalIdeal (𝓞 K)⁰ K) :=
    (algebraMap_mem_idealFiniteAdeles_iff L _).mp hmemL
  rw [Units.val_mk0]
  have hξeq : ξ i = (e⁻¹ * e⁻¹) * (e * e * ξ i) := by field_simp
  rw [hξeq]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmem

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

end

end GlobalTheory.CompanionTheory.EisRk1Bound
