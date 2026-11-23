module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapNeZeroOfMemHcompl
section
open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem algebraMap_conjO (r : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl

theorem conjO_conjO (r : 𝓞 K) : conjO K (conjO K r) = r :=
  _root_.Formalism.HermitianLattices.Ext.L3.conjO_conjO r

theorem mem_conjIdeal_iff (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]

theorem conjIdeal_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).IsPrime := by
  rw [conjIdeal_eq_comap]
  exact Ideal.comap_isPrime (conjO K) p

theorem hcompl_eq_closure (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) p = Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  congr 1
  ext s
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 _ (algebraMap_conjO s)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have : t = conjO K s := RingOfIntegers.ext ht
    rwa [this]

theorem mem_hcompl_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      have h1 : (1 : 𝓞 K) ∉ p := (Ideal.ne_top_iff_one p).mp hp.ne_top
      exact ⟨h1, by rwa [map_one]⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (hp.mem_or_mem h).elim ihx.1 ihy.1
      · rw [map_mul] at h
        exact (hp.mem_or_mem h).elim ihx.2 ihy.2
  · intro hs
    exact Submonoid.subset_closure hs

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    apply Submonoid.subset_closure
    exact ⟨hx.2, by rw [conjO_conjO]; exact hx.1⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

theorem algebraMap_ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  have hs0 : s = 0 := RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm)
  exact ((mem_hcompl_iff hp s).mp hs).1 (hs0 ▸ p.zero_mem)

theorem mem_locR_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) :
    a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ↔
      ∃ r : 𝓞 K, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
        a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  constructor
  · rintro ⟨s, hs, h1⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
    refine ⟨r, s, hs, ?_⟩
    rw [eq_div_iff (algebraMap_ne_zero_of_mem_hcompl hp hs), hr, mul_comm]
  · rintro ⟨r, s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_div_cancel₀ _ (algebraMap_ne_zero_of_mem_hcompl hp hs)]
    exact Formalism.HermitianLatticesTheory.locDual_alg_mem r

def locRing (p : Ideal (𝓞 K)) : Subring K where
  carrier := {a | a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p}
  mul_mem' := by
    intro a b ha hb
    change a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at ha
    change b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at hb
    change a * b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha hb ⊢
    obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have e : algebraMap (𝓞 K) K (s * t) * (a * b) =
        (algebraMap (𝓞 K) K s * a) * (algebraMap (𝓞 K) K t * b) := by
      rw [map_mul]; ring
    rw [e]
    exact Formalism.HermitianLatticesTheory.locDual_one_mul h1 h2
  one_mem' := by
    change (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, mul_one]; exact Submodule.one_le.mp le_rfl⟩
  add_mem' := fun ha hb => (Formalism.HermitianLatticesTheory.locR (K := K) p).add_mem ha hb
  zero_mem' := (Formalism.HermitianLatticesTheory.locR (K := K) p).zero_mem
  neg_mem' := fun ha => (Formalism.HermitianLatticesTheory.locR (K := K) p).neg_mem ha

theorem mem_locRing (p : Ideal (𝓞 K)) (a : K) :
    a ∈ locRing p ↔ a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := Iff.rfl

theorem algebraMap_mem_locRing (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Formalism.HermitianLatticesTheory.locDual_alg_mem r⟩

theorem frac_locRing (p : Ideal (𝓞 K)) (a : K) : ∃ t ∈ locRing p, t ≠ 0 ∧ t * a ∈ locRing p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
  refine ⟨algebraMap (𝓞 K) K s, algebraMap_mem_locRing p _, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    change a * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r at hrs
    rw [hrs]
    exact algebraMap_mem_locRing p r

theorem star_mem_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) :
    star a ∈ locRing p := by
  rw [mem_locRing, mem_locR_iff hp] at ha ⊢
  obtain ⟨r, s, hs, rfl⟩ := ha
  refine ⟨conjO K r, conjO K s, conjO_mem_hcompl hs, ?_⟩
  rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

theorem isUnitIn_div_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := fun h => h0 (by rw [h, zero_div])
    rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv
    obtain ⟨u, hu, h1⟩ := hinv
    obtain ⟨v, hv⟩ := Submodule.mem_one.mp h1
    have e : u * s = v * r := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u * s) = algebraMap (𝓞 K) K (v * r)
      rw [map_mul, map_mul, hv, inv_div]
      field_simp
    have hus := (mem_hcompl_iff hp _).mp (mul_mem hu hs)
    rw [e] at hus
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hus.1 (p.mul_mem_left v h), fun h => hus.2 (Ideal.mul_mem_left _ v h)⟩
  · intro hr
    have hr0 := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hr0 hs0, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, inv_div _ _⟩

theorem unram_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hmem : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp.isPrime, mem_conjIdeal_iff]
    refine ⟨hθ, fun h => hθ ?_⟩
    rw [map_sub, conjO_conjO] at h
    have := p.neg_mem h
    rwa [neg_sub] at this
  have h := (isUnitIn_div_iff hp.isPrime (θ - conjO K θ)
    (one_mem (Formalism.HermitianLatticesTheory.hcompl (K := K) p))).mpr hmem
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at h

end Formalism.HermitianLattices.Ext.L3.WA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardMapEquiv
section
namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts

open Matrix

variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem card_conj (C : Matrix m m A) (hC : IsUnit C.det) :
    Nat.card {X : Matrix m m A // Xᴴ * (Cᴴ * C) * X = Cᴴ * C} =
      Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} := by
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  have h2 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have h3 : C⁻¹ᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  refine Nat.card_congr
    { toFun := fun X => ⟨C * X.1 * C⁻¹, ?_⟩
      invFun := fun Y => ⟨C⁻¹ * Y.1 * C, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hX := X.2
    calc (C * X.1 * C⁻¹)ᴴ * (C * X.1 * C⁻¹) = C⁻¹ᴴ * (X.1ᴴ * (Cᴴ * C) * X.1) * C⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (C⁻¹ᴴ * Cᴴ) * (C * C⁻¹) := by rw [hX]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, h3, Matrix.mul_one]
  · have hY := Y.2
    calc (C⁻¹ * Y.1 * C)ᴴ * (Cᴴ * C) * (C⁻¹ * Y.1 * C)
        = Cᴴ * (Y.1ᴴ * ((C⁻¹ᴴ * Cᴴ) * ((C * C⁻¹) * Y.1))) * C := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Cᴴ * C := by rw [h1, h3, Matrix.one_mul, Matrix.one_mul, hY, Matrix.mul_one]
  · intro X
    apply Subtype.ext
    show C⁻¹ * (C * X.1 * C⁻¹) * C = X.1
    calc C⁻¹ * (C * X.1 * C⁻¹) * C = (C⁻¹ * C) * X.1 * (C⁻¹ * C) := by
          simp only [Matrix.mul_assoc]
      _ = X.1 := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    apply Subtype.ext
    show C * (C⁻¹ * Y.1 * C) * C⁻¹ = Y.1
    calc C * (C⁻¹ * Y.1 * C) * C⁻¹ = (C * C⁻¹) * Y.1 * (C * C⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Y.1 := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem map_conjTranspose_mul_eq_map_transpose_mul (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (Y : Matrix m m A) :
    ((Y.map φ).map σ).transpose * Y.map φ = (Yᴴ * Y).map φ := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, conjTranspose_apply, map_sum, hφ]

theorem card_map_equiv (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a)) :
    Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  refine Nat.card_congr
    { toFun := fun Y => ⟨Y.1.map φ, ?_⟩
      invFun := fun X => ⟨X.1.map φ.symm, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ, Y.2]
    ext i j
    simp [Matrix.one_apply]
  · have h1 : ((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ = 1 := by
      rw [← map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ]
      have : (X.1.map φ.symm).map φ = X.1 := by ext i j; simp
      rw [this, X.2]
    have h2 : (X.1.map φ.symm)ᴴ * X.1.map φ.symm
        = (((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ).map φ.symm := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, RingEquiv.symm_apply_apply]
    rw [h2, h1]
    ext i j
    simp [Matrix.one_apply]
  · intro Y; apply Subtype.ext; ext i j; simp
  · intro X; apply Subtype.ext; ext i j; simp

theorem exists_norm [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ)
    (hq : Fintype.card k = q ^ 2) (c : k) (hc : σ c = c) : ∃ y, σ y * y = c := by
  classical
  by_cases h0 : c = 0
  · exact ⟨0, by simp [h0]⟩
  · have h := Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc
    rw [if_neg h0] at h
    have hpos : 0 < (Finset.univ.filter fun y : k => σ y * y = c).card := by
      by_contra hz
      push_neg at hz
      have hz' : (Finset.univ.filter fun y : k => σ y * y = c).card = 0 := by omega
      simp only [hz'] at h
      push_cast at h
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    exact ⟨y, (Finset.mem_filter.mp hy).2⟩

theorem card_inert [Fintype k] (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (u : m → A) (hu : ∀ i, star (u i) = u i) (hunit : ∀ i, IsUnit (u i)) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal u * X = diagonal u} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  have hy : ∀ i, ∃ y, σ y * y = φ (u i) := fun i =>
    exists_norm σ hσ hne q hq (φ (u i)) (by rw [← hφ, hu])
  choose y hy using hy
  set a : m → A := fun i => φ.symm (y i) with ha_def
  have ha : ∀ i, star (a i) * a i = u i := by
    intro i
    apply φ.injective
    rw [map_mul, hφ]
    simp [ha_def, hy]
  have hCC : (diagonal a)ᴴ * diagonal a = diagonal u := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact ha i
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [ha i]; exact hunit i)
  have hC : IsUnit (diagonal a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hau))
  rw [← hCC, card_conj (diagonal a) hC, card_map_equiv φ σ hφ]

private theorem map_conjTranspose_mul_mul_eq (φ : A →+* k) (X H : Matrix m m A) :
    (Xᴴ * H * X).map φ = (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2

private theorem map_star_eq_transpose_map_of_isHermitian (φ : A →+* k) {M : Matrix m m A} (hM : Mᴴ = M) :
    M.map (fun a => φ (star a)) = (M.map φ)ᵀ := by
  ext i j
  have h := congrFun (congrFun hM j) i
  rw [conjTranspose_apply] at h
  simp only [map_apply, transpose_apply]
  rw [h]

private theorem matrix_eq_of_map_and_map_star_eq (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    {M N : Matrix m m A} (h1 : M.map φ = N.map φ)
    (h2 : M.map (fun a => φ (star a)) = N.map (fun a => φ (star a))) : M = N := by
  ext i j
  apply hb.1
  exact Prod.ext (congrFun (congrFun h2 i) j) (congrFun (congrFun h1 i) j)

theorem card_split (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} = Nat.card (GL m k) := by
  classical
  have hdet : (H.map φ).det = φ H.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hGu : IsUnit (H.map φ).det := by
    rw [hdet]; exact hu.map φ
  have cond : ∀ X : Matrix m m A, Xᴴ * H * X = H ↔
      (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ = H.map φ := by
    intro X
    rw [← map_conjTranspose_mul_mul_eq]
    constructor
    · intro h; rw [h]
    · intro h
      apply matrix_eq_of_map_and_map_star_eq φ hb h
      have hM : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
        simp [conjTranspose_mul, hH, Matrix.mul_assoc]
      rw [map_star_eq_transpose_map_of_isHermitian φ hM, map_star_eq_transpose_map_of_isHermitian φ hH, h]
  have hP : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, IsUnit (X.1.map φ).det := by
    intro X
    have h := congrArg Matrix.det ((cond X.1).mp X.2)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h
    exact hGu.ne_zero h.symm
  have key : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H},
      (X.1.map fun a => φ (star a))ᵀ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
    intro X
    have h := (cond X.1).mp X.2
    have hu' : IsUnit (H.map φ * X.1.map φ).det := by
      rw [det_mul]; exact hGu.mul (hP X)
    calc (X.1.map fun a => φ (star a))ᵀ
        = (X.1.map fun a => φ (star a))ᵀ * (H.map φ * X.1.map φ) * (H.map φ * X.1.map φ)⁻¹ := by
          rw [Matrix.mul_assoc _ (H.map φ * X.1.map φ), Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
      _ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
          rw [← Matrix.mul_assoc _ (H.map φ), h]
  refine Nat.card_eq_of_bijective (fun X => Matrix.nonsingInvUnit (X.1.map φ) (hP X)) ⟨?_, ?_⟩
  · intro X Y hXY
    have hPe : X.1.map φ = Y.1.map φ := congrArg Units.val hXY
    have hQe : X.1.map (fun a => φ (star a)) = Y.1.map (fun a => φ (star a)) := by
      calc X.1.map (fun a => φ (star a)) = ((X.1.map fun a => φ (star a))ᵀ)ᵀ :=
            (transpose_transpose _).symm
        _ = (H.map φ * (H.map φ * Y.1.map φ)⁻¹)ᵀ := by rw [key X, hPe]
        _ = Y.1.map (fun a => φ (star a)) := by rw [← key Y, transpose_transpose]
    exact Subtype.ext (matrix_eq_of_map_and_map_star_eq φ hb hPe hQe)
  · intro U
    let e := Equiv.ofBijective _ hb
    let X : Matrix m m A := Matrix.of fun i j =>
      e.symm ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)
    have hX : ∀ i j, (φ (star (X i j)), φ (X i j)) =
        ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j) :=
      fun i j => e.apply_symm_apply _
    have hXP : X.map φ = (↑U : Matrix m m k) := by
      ext i j; exact congrArg Prod.snd (hX i j)
    have hXQ : X.map (fun a => φ (star a)) = (H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ := by
      ext i j; exact congrArg Prod.fst (hX i j)
    have hc : Xᴴ * H * X = H := by
      rw [cond, hXP, hXQ, transpose_transpose]
      calc H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹ * H.map φ * (↑U : Matrix m m k)
          = H.map φ * (↑U⁻¹ : Matrix m m k) * ((H.map φ)⁻¹ * H.map φ) * (↑U : Matrix m m k) := by
            simp only [Matrix.mul_assoc]
        _ = H.map φ := by
            rw [Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul,
              Matrix.mul_one]
    refine ⟨⟨X, hc⟩, ?_⟩
    apply Units.ext
    exact hXP

end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjAlg : K ≃ₐ[ℚ] K := (starRingAut : RingAut K).toRatAlgEquiv

abbrev cmF : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers (conjAlg K))

theorem conjAlg_apply (x : K) : conjAlg K x = star x := rfl

theorem mem_cmF_iff (x : K) : x ∈ cmF K ↔ star x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h f hf
    have hs : conjAlg K ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) x :=
      MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def, conjAlg_apply, h])
    have := MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hs) hf)
    rwa [AlgEquiv.smul_def] at this

theorem star_coe_cmF (x : cmF K) : star (x : K) = x := (mem_cmF_iff K x).1 x.2

variable {K}

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  by_contra h
  push_neg at h
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  have hφ : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext a
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1 φ a, h a]
  have hc := hK.1.isComplex (InfinitePlace.mk φ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  exact hc hφ

theorem exists_skew (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ w : K, w ≠ 0 ∧ star w = -w := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
  rw [star_sub, star_star]
  ring

theorem isReal_embedding_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ψ : K →+* ℂ) :
    ComplexEmbedding.IsReal (ψ.comp (algebraMap (cmF K) K)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hK.2.1 ψ]
  exact congrArg ψ (star_coe_cmF K a)

theorem isReal_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (v : InfinitePlace (cmF K)) : v.IsReal := by
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := K) v
  show (w.comap (algebraMap (cmF K) K)).IsReal
  have e : w.comap (algebraMap (cmF K) K) = InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rw [e, InfinitePlace.isReal_mk_iff]
  exact isReal_embedding_cmF hK _

theorem totPos_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (a : cmF K) :
    TotPos (a : K) ↔ ∀ φ : cmF K →+* ℝ, 0 < φ a := by
  constructor
  · intro h φ
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have hr := isReal_embedding_cmF hK w.embedding
    have hw' : InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) =
        InfinitePlace.mk (Complex.ofRealHom.comp φ) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
      exact hw
    rw [InfinitePlace.mk_eq_iff] at hw'
    have e : w.embedding.comp (algebraMap (cmF K) K) = Complex.ofRealHom.comp φ := by
      rcases hw' with e | e
      · exact e
      · rwa [ComplexEmbedding.isReal_iff.1 hr] at e
    have h1 := h w.embedding
    have e2 : w.embedding (a : K) = (φ a : ℂ) := RingHom.congr_fun e a
    rw [e2, Complex.ofReal_re] at h1
    exact h1
  · intro h ψ
    have hr := isReal_embedding_cmF hK ψ
    have e : ((hr.embedding a : ℝ) : ℂ) = ψ (a : K) := hr.coe_embedding_apply a
    rw [← e, Complex.ofReal_re]
    exact h _

end Formalism.HermitianLattices.Ext.L3
end
end

