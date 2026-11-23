module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelSummationBound
section
open Finset

namespace GlobalTheory.CompanionTheory.AbelBounds

theorem abel_nat (a D : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range (n + 1), -a p * D p =
      ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)
        + a n * (-∑ k ∈ range (n + 1), D k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 := sum_range_succ (fun p => (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)) n
    have e2 := sum_range_succ D (n + 1)
    rw [sum_range_succ (fun p => -a p * D p) (n + 1), ih, e1, e2]
    ring

theorem sum_diff (a : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range n, (a p - a (p + 1)) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem abel_bound_nat (a D : ℕ → ℝ) (n : ℕ) (Up Lo Cc : ℝ) (hUp : 0 ≤ Up) (hLo : 0 ≤ Lo)
    (hmono : ∀ p, p < n → a (p + 1) ≤ a p) (h0 : |a 0| ≤ 2) (hn : |a n| ≤ 2)
    (hY : ∀ p, p < n → -Lo ≤ -∑ k ∈ range (p + 1), D k ∧ -∑ k ∈ range (p + 1), D k ≤ Up)
    (hC : |∑ k ∈ range (n + 1), D k| ≤ Cc) :
    -(4 * Lo + 2 * Cc) ≤ ∑ p ∈ range (n + 1), -a p * D p ∧
      ∑ p ∈ range (n + 1), -a p * D p ≤ 4 * Up + 2 * Cc := by
  rw [abel_nat]
  have htel := sum_diff a n
  have hdiff : a 0 - a n ≤ 4 := by
    have := (abs_le.mp h0).2
    have := (abs_le.mp hn).1
    linarith
  have hup : ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) ≤ 4 * Up := by
    calc ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)
        ≤ ∑ p ∈ range n, (a p - a (p + 1)) * Up := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_range.mp hp
          exact mul_le_mul_of_nonneg_left (hY p hp').2 (sub_nonneg.mpr (hmono p hp'))
      _ = (a 0 - a n) * Up := by rw [← sum_mul, htel]
      _ ≤ 4 * Up := mul_le_mul_of_nonneg_right hdiff hUp
  have hlo : -(4 * Lo) ≤ ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) := by
    calc -(4 * Lo) ≤ (a 0 - a n) * (-Lo) := by nlinarith
      _ = ∑ p ∈ range n, (a p - a (p + 1)) * (-Lo) := by rw [← sum_mul, htel]
      _ ≤ ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_range.mp hp
          exact mul_le_mul_of_nonneg_left (hY p hp').1 (sub_nonneg.mpr (hmono p hp'))
  have hlast : |a n * (-∑ k ∈ range (n + 1), D k)| ≤ 2 * Cc := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hn hC (abs_nonneg _) (by norm_num)
  have := abs_le.mp hlast
  constructor <;> linarith [this.1, this.2]

noncomputable def ext0 {N : ℕ} (f : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k < N then f ⟨k, h⟩ else 0

theorem extendByZeroOnSubset_apply_coe {N : ℕ} (f : Fin N → ℝ) (k : Fin N) : ext0 f k = f k := by
  simp [ext0]

theorem sum_Iic_ext_zero {N : ℕ} (D : Fin N → ℝ) (p : Fin N) :
    ∑ k ∈ Finset.Iic p, D k = ∑ k ∈ range ((p : ℕ) + 1), ext0 D k := by
  refine sum_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    have : k ≤ p := Finset.mem_Iic.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le this)
  · intro x _ y _ h
    exact Fin.ext h
  · intro k hk
    have hk' : k < (p : ℕ) + 1 := mem_range.mp (by simpa using hk)
    have hkN : k < N := lt_of_le_of_lt (Nat.le_of_lt_succ hk') p.2
    refine ⟨⟨k, hkN⟩, ?_, rfl⟩
    simp only [Finset.coe_Iic, Set.mem_Iic]
    exact Fin.mk_le_of_le_val (Nat.le_of_lt_succ hk')
  · intro k _
    exact (extendByZeroOnSubset_apply_coe D k).symm

theorem abel_bound : ∀ (N : ℕ) (a D : Fin N → ℝ) (Up Lo Cc : ℝ), 0 ≤ Up → 0 ≤ Lo → 0 ≤ Cc →
    (∀ p q, p ≤ q → a q ≤ a p) → (∀ p, |a p| ≤ 2) →
    (∀ p : Fin N, (p : ℕ) + 1 < N → -Lo ≤ -∑ k ∈ Finset.Iic p, D k ∧
      -∑ k ∈ Finset.Iic p, D k ≤ Up) →
    (∀ p : Fin N, (p : ℕ) + 1 = N → |∑ k ∈ Finset.Iic p, D k| ≤ Cc) →
    -(4 * Lo + 2 * Cc) ≤ ∑ p, -a p * D p ∧ ∑ p, -a p * D p ≤ 4 * Up + 2 * Cc := by
  intro N a D Up Lo Cc hUp hLo hCc hmono hbd hY hC
  rcases N with _ | n
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    constructor <;> linarith
  have hsum : ∑ p, -a p * D p = ∑ p ∈ range (n + 1), -ext0 a p * ext0 D p := by
    rw [← Fin.sum_univ_eq_sum_range (fun p => -ext0 a p * ext0 D p)]
    exact sum_congr rfl fun p _ => by rw [extendByZeroOnSubset_apply_coe, extendByZeroOnSubset_apply_coe]
  rw [hsum]
  have hlt : ∀ p, p < n → p < n + 1 := fun p hp => Nat.lt_succ_of_lt hp
  refine abel_bound_nat (ext0 a) (ext0 D) n Up Lo Cc hUp hLo ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have e1 := extendByZeroOnSubset_apply_coe a ⟨p, hlt p hp⟩
    have e2 := extendByZeroOnSubset_apply_coe a ⟨p + 1, Nat.succ_lt_succ hp⟩
    simp only at e1 e2
    rw [e1, e2]
    exact hmono _ _ (Fin.mk_le_mk.mpr (Nat.le_succ p))
  · have e := extendByZeroOnSubset_apply_coe a ⟨0, Nat.succ_pos n⟩
    simp only at e
    rw [e]
    exact hbd _
  · have e := extendByZeroOnSubset_apply_coe a ⟨n, Nat.lt_succ_self n⟩
    simp only at e
    rw [e]
    exact hbd _
  · intro p hp
    have h := hY ⟨p, hlt p hp⟩ (Nat.succ_lt_succ hp)
    rw [sum_Iic_ext_zero] at h
    exact h
  · have h := hC ⟨n, Nat.lt_succ_self n⟩ rfl
    rw [sum_Iic_ext_zero] at h
    exact h

end GlobalTheory.CompanionTheory.AbelBounds
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementForm
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_numerator_of_mem_adjoin_insert_inv :
    ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  intro T Ω _ _ u f S hS F hF hf s
  obtain ⟨s, hs⟩ := s
  subst hS
  show ∃ (G : MvPolynomial T ℚ) (k : ℕ), s * f ^ k = aeval u G
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨X i, 0, by simp⟩
  | algebraMap q => exact ⟨C q, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * F ^ k₂ + G₂ * F ^ k₁, k₁ + k₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, hF, ← h₁, ← h₂]
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * G₂, k₁ + k₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAway
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem adjoin_inv_isLocalization_away (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω)
    (G : Set Ω) (hA : A = Algebra.adjoin ℚ G) (g : A) (hg : g ≠ 0)
    (hS : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G)) (hle : A ≤ S') :
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI : Algebra A S' := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hg0 : (g : Ω) ≠ 0 := fun h => hg (Subtype.ext h)
  have hinv : (g : Ω)⁻¹ ∈ S' := by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have key : ∀ x ∈ S', ∃ (n : ℕ) (a : A), x * (g : Ω) ^ n = (a : Ω) := by
    intro x hx
    rw [hS] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact ⟨1, 1, by simp [hg0]⟩
      · refine ⟨0, ⟨x, ?_⟩, by simp⟩
        rw [hA]; exact Algebra.subset_adjoin hx
    | algebraMap r => exact ⟨0, algebraMap ℚ A r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * g ^ m + b * g ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  refine IsLocalization.Away.mk g ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨(g : Ω)⁻¹, hinv⟩ : S') ?_
    apply Subtype.ext
    change (g : Ω) * (g : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ hg0
  · intro s
    obtain ⟨n, a, ha⟩ := key s s.2
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    change (s : Ω) * (g : Ω) ^ n = (a : Ω)
    exact ha
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = (b : Ω) := congrArg (fun x : S' => (x : Ω)) hab
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoin
section
namespace GlobalTheory.CompanionTheory.FieldGen

theorem isAlgebraic_adjoin_range_self {k E σ : Type} [Field k] [Field E] [Algebra k E] (y : σ → E) :
    Algebra.IsAlgebraic
      (Algebra.adjoin k (Set.range fun j =>
        (⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ :
          IntermediateField.adjoin k (Set.range y))))
      (IntermediateField.adjoin k (Set.range y)) := by
  set E' := IntermediateField.adjoin k (Set.range y) with hE'
  set y' : σ → E' := fun j => ⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ with hy'
  set A := Algebra.adjoin k (Set.range y') with hA
  have hmap : ∀ p ∈ Algebra.adjoin k (Set.range y), ∃ p' ∈ A, (p' : E) = p := by
    intro p hp
    have h1 : Algebra.adjoin k (Set.range y) = A.map (IntermediateField.val E') := by
      rw [hA, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [h1] at hp
    obtain ⟨p', hp', rfl⟩ := Subalgebra.mem_map.1 hp
    exact ⟨p', hp', rfl⟩
  constructor
  intro z
  obtain ⟨v, hv⟩ := z
  obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.1 hv
  by_cases hq0 : q = 0
  · have hz : (⟨v, hv⟩ : E') = 0 := by
      apply Subtype.ext
      simp [hpq, hq0]
    rw [hz]
    exact isAlgebraic_zero
  obtain ⟨p', hp', hpp⟩ := hmap p hp
  obtain ⟨q', hq', hqq⟩ := hmap q hq
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [← hqq]; rfl)
  refine ⟨Polynomial.C (⟨q', hq'⟩ : A) * Polynomial.X - Polynomial.C ⟨p', hp'⟩, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) h
    simp at h2
    exact hq'0 (congrArg Subtype.val h2 :)
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, sub_eq_zero]
    change q' * (⟨v, hv⟩ : E') = p'
    apply Subtype.ext
    show (q' : E) * v = p'
    rw [hpp, hqq, hpq]
    field_simp

theorem algebraicIndependent_of_adjoin_eq :
    ∀ (K L J : Type) [Field K] [Field L] [Algebra K L] [Finite J] (x y : J → L),
      AlgebraicIndependent K x →
      IntermediateField.adjoin K (Set.range x) = IntermediateField.adjoin K (Set.range y) →
      AlgebraicIndependent K y := by
  intro K L J _ _ _ _ x y hx hxy
  set E := IntermediateField.adjoin K (Set.range y) with hE
  have hal := isAlgebraic_adjoin_range_self (k := K) y
  set y' : J → E := fun j => ⟨y j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩ with hy'
  have hxmem : ∀ j, x j ∈ E := fun j => by
    rw [← hxy]
    exact IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  set x' : J → E := fun j => ⟨x j, hxmem j⟩ with hxd
  have hx' : AlgebraicIndependent K x' := AlgebraicIndependent.of_comp E.val hx
  have hle : Cardinal.mk J ≤ Algebra.trdeg K E := hx'.cardinalMk_le_trdeg
  have htb := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K y' hle
  exact htb.1.map' (f := E.val) E.val.injective

end GlobalTheory.CompanionTheory.FieldGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualModuleFiniteProjective
section
namespace GlobalTheory.CompanionTheory.Ggeo.HomDual

noncomputable def homEquivDual (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] :
    (P →ₗ[R] Localization.Away f) ≃ₗ[Localization.Away f] Module.Dual (Localization.Away f) P :=
  { toFun := fun g =>
      LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f) g
    invFun := fun g => g.restrictScalars R
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finite_projective_hom : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P] [Module.Projective (Localization.Away f) P],
    Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧
      Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  intro R P _ f _ _ _ _ _ _
  let e := homEquivDual R P f
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end GlobalTheory.CompanionTheory.Ggeo.HomDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorFieldEmbedding
section
open NumberField Module

namespace GlobalTheory.CompanionTheory.TraceProj

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) : Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  rw [Ideal.mem_bot]
  exact hn

theorem sum_repr_smul_dual (E : Type) [Field E] [NumberField E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B D : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i))
    (hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0)
    (hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k))
    (a : 𝓞 E) (l : ι) :
    ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k = algebraMap (𝓞 E) E a * D l := by
  have hB' : ∀ k, algebraMap (𝓞 E) E a * B k = ∑ i, ((b.repr (a * b k) i : ℤ) : E) * B i := by
    intro k
    rw [hB k, ← map_mul]
    conv_lhs => rw [← b.sum_repr (a * b k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hB, zsmul_eq_mul]
  have hterm : ∀ k i, Algebra.trace ℚ E (D l * (((b.repr (a * b k) i : ℤ) : E) * B i)) =
      (b.repr (a * b k) i : ℚ) * (if i = l then 1 else 0) := by
    intro k i
    rw [← hD i l, Algebra.traceForm_apply, mul_left_comm,
      show (((b.repr (a * b k) i : ℤ) : E)) * (D l * B i) =
        (b.repr (a * b k) i : ℚ) • (D l * B i) by rw [Rat.smul_def]; push_cast; rfl,
      LinearMap.map_smul, smul_eq_mul]
  have hcoord : ∀ k, D.repr (algebraMap (𝓞 E) E a * D l) k = (b.repr (a * b k) l : ℚ) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrepr, Algebra.traceForm_apply, mul_comm (algebraMap (𝓞 E) E a) (D l), mul_assoc, hB' k,
      Finset.mul_sum, map_sum]
    simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ∑ k, ((b.repr (a * b k) l : ℤ) : E) * D k
      = ∑ k, D.repr (algebraMap (𝓞 E) E a * D l) k • D k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcoord, Rat.smul_def]
        push_cast
        rfl
    _ = algebraMap (𝓞 E) E a * D l := D.sum_repr _

theorem exists_coeff (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 E)) (B : Basis ι ℚ E)
    (hB : ∀ i, B i = algebraMap (𝓞 E) E (b i)) :
    ∃ c : ι → K, ∑ k, c k * σ (b k) = 1 ∧
      ∀ (a : 𝓞 E) (l : ι), ∑ k, ((b.repr (a * b k) l : ℤ) : K) * c k = σ a * c l := by
  have hnd := traceForm_nondegenerate ℚ E
  let D := (Algebra.traceForm ℚ E).dualBasis hnd B
  have hD : ∀ i j, Algebra.traceForm ℚ E (D j) (B i) = if i = j then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hnd B j i
  have hrepr : ∀ (x : E) (k : ι), D.repr x k = Algebra.traceForm ℚ E x (B k) := fun x k =>
    LinearMap.BilinForm.dualBasis_repr_apply hnd B x k
  let σ' : E →+* K := IsFractionRing.lift (injective_of_charZero E K σ)
  have hσ' : ∀ x, σ' (algebraMap (𝓞 E) E x) = σ x := IsFractionRing.lift_algebraMap _
  have h1 : ∑ k, D k * B k = 1 := by
    have h0 : ∑ k, D k * B k - 1 = 0 := by
      refine hnd.1 _ fun x => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
        Algebra.trace_eq_matrix_trace D x, Matrix.trace]
      simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrepr, Algebra.traceForm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    exact sub_eq_zero.mp h0
  refine ⟨fun k => σ' (D k), ?_, fun a l => ?_⟩
  · calc ∑ k, σ' (D k) * σ (b k) = σ' (∑ k, D k * B k) := by simp [map_sum, hB, hσ']
      _ = 1 := by rw [h1, map_one]
  · have h := congrArg σ' (sum_repr_smul_dual E b B D hB hD hrepr a l)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_mul, hσ'] using h

theorem exists_eigen_projector : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧
      ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L)
        (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W),
        ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  intro E _ _ K _ _ σ
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_coeff E K σ b (integralBasis E) (fun i => integralBasis_apply E i)
  let eqv := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun k => b (eqv.symm k), fun k => c (eqv.symm k), ?_, ?_⟩
  · rw [← hc1]
    exact Equiv.sum_comp eqv.symm (fun i => c i * σ (b i))
  · intro L W _ _ _ j ρ a w
    rw [Equiv.sum_comp eqv.symm (fun i => j (c i) • ρ (b i) w)]
    have hmul : ∀ i, ρ a (ρ (b i) w) = ∑ l, ((b.repr (a * b i) l : ℤ) : L) • ρ (b l) w := by
      intro i
      rw [← Module.End.mul_apply, ← map_mul]
      conv_lhs => rw [← b.sum_repr (a * b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, LinearMap.sum_apply, Int.cast_smul_eq_zsmul]
    have hj : ∀ l, ∑ i, j (c i) * ((b.repr (a * b i) l : ℤ) : L) = j (σ a) * j (c l) := by
      intro l
      have h := congrArg j (hc2 a l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_intCast] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, hj l]

end GlobalTheory.CompanionTheory.TraceProj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpSplit
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem existsUnique_valuationRing_lift : ∀ (O V C : Type) [CommRing O] [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (b : O →+* V) (Z : Scheme.{0}) (s : Z ⟶ Spec (CommRingCat.of O)) [IsProper s] (y : Spec (CommRingCat.of C) ⟶ Z), y ≫ s = Spec.map (CommRingCat.ofHom ((algebraMap V C).comp b)) → ∃! y' : Spec (CommRingCat.of V) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ y' = y ∧ y' ≫ s = Spec.map (CommRingCat.ofHom b) := by
  intro O V C _ _ _ _ _ _ _ b Z s hs y hy
  have hv : ValuativeCriterion s := by
    have h : (@IsProper : MorphismProperty Scheme.{0}) s := hs
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hc : CommSq y (Spec.map (CommRingCat.ofHom (algebraMap V C))) s
      (Spec.map (CommRingCat.ofHom b)) := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩
  let S : ValuativeCommSq s :=
    { R := V, K := C, i₁ := y, i₂ := Spec.map (CommRingCat.ofHom b), commSq := hc }
  obtain ⟨u⟩ := hv S
  refine ⟨u.default.l, ⟨u.default.fac_left, u.default.fac_right⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  have := u.uniq ⟨y', h1, h2⟩
  exact congrArg CommSq.LiftStruct.l this

end GlobalTheory.CompanionTheory.Ar.Flat
end

