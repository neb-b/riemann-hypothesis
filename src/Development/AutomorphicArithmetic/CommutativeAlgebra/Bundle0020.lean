module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SpecializationTensorRingHomProperties
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

section
variable {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

private lemma map_val_injective (R : Subalgebra k L) :
    Function.Injective
      (Algebra.TensorProduct.map R.val (AlgHom.id k A) : R ⊗[k] A →ₐ[k] L ⊗[k] A) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (R.val.toLinearMap) Subtype.val_injective
  have e : ∀ z : R ⊗[k] A, LinearMap.rTensor A R.val.toLinearMap z =
      Algebra.TensorProduct.map R.val (AlgHom.id k A) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  intro x y hxy
  apply h
  rw [e, e, hxy]

private lemma spz_add {R : Subalgebra k L} {φ : R →ₐ[k] k} {y y' : L ⊗[k] A} {a a' : A}
    (h : Spz R φ y a) (h' : Spz R φ y' a') : Spz R φ (y + y') (a + a') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv, rfl⟩ := h'
  exact ⟨u + v, by rw [map_add (f := _), hu, hv], by simp only [map_add (f := _)]⟩

private lemma spz_tmul (R : Subalgebra k L) (φ : R →ₐ[k] k) (r : R) (a : A) :
    Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a) :=
  ⟨r ⊗ₜ[k] a, by simp, by simp⟩

private noncomputable def contr (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] :
    B ⊗[k] A →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ LinearMap.lTensor B l

private lemma contr_tmul (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] (b : B) (a : A) :
    contr l B (b ⊗ₜ[k] a) = l a • b := by
  simp [contr]

private lemma exists_contr_ne_zero {y : L ⊗[k] A} (hy : y ≠ 0) :
    ∃ l : A →ₗ[k] k, contr l L y ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k A
  let E := TensorProduct.equivFinsuppOfBasisRight (R := k) (M := L) (N := A) b
  have hE : E y ≠ 0 := fun h => hy (E.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hE
  refine ⟨b.coord i, ?_⟩
  have key : ∀ z : L ⊗[k] A, contr (b.coord i) L z = E z i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [contr_tmul, E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Finsupp.add_apply]
  rw [key]
  simpa using hi
end

theorem UpperTheory.specialization_tensor_ring_hom_properties :
    ∀ (k L A : Type) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A], (∀ (R : Subalgebra k L) (φ : R →ₐ[k] k), (∀ (y : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y a' → a = a') ∧ (∀ (y y' : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y' a' → Spz R φ (y + y') (a + a') ∧ Spz R φ (y * y') (a * a') ∧ Spz R φ (y - y') (a - a')) ∧ (∀ (r : R) (a : A), Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a)) ∧ ∀ (A' : Type) [CommRing A'] [Algebra k A'] (g : A →ₐ[k] A') (y : L ⊗[k] A) (a : A), Spz R φ y a → Spz R φ (Algebra.TensorProduct.map (AlgHom.id k L) g y) (g a)) ∧ (∀ y : L ⊗[k] A, ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ φ : R →ₐ[k] k, ∃ a, Spz R φ y a) ∧ ∀ y : L ⊗[k] A, y ≠ 0 → ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ (φ : R →ₐ[k] k) (a : A), Spz R φ y a → a ≠ 0 := by
  intro k L A _ _ _ _ _
  refine ⟨fun R φ => ⟨?_, ?_, spz_tmul R φ, ?_⟩, ?_, ?_⟩
  · rintro y a a' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [map_val_injective R (hu.trans hv.symm)]
  · intro y y' a a' h h'
    refine ⟨spz_add h h', ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u * v, by rw [map_mul, hu, hv], by simp only [map_mul]⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u - v, by rw [map_sub, hu, hv], by simp only [map_sub]⟩
  · rintro A' _ _ g y a ⟨u, rfl, rfl⟩
    refine ⟨Algebra.TensorProduct.map (AlgHom.id k R) g u, ?_, ?_⟩
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact ⟨∅, fun R _ φ => ⟨0, 0, by simp, by simp⟩⟩
    | tmul l b =>
      classical
      refine ⟨{l}, fun R hs φ => ?_⟩
      have hl : l ∈ R := hs (by simp)
      exact ⟨_, spz_tmul R φ ⟨l, hl⟩ b⟩
    | add x y hx hy =>
      classical
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, fun R hst φ => ?_⟩
      obtain ⟨a, ha⟩ := hs R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      obtain ⟨b, hb⟩ := ht R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      exact ⟨a + b, spz_add ha hb⟩
  · intro y hy
    classical
    obtain ⟨l, hl⟩ := exists_contr_ne_zero hy
    set c := contr l L y with hc
    refine ⟨{c, c⁻¹}, fun R hs φ a ha h0 => ?_⟩
    have hcR : c ∈ R := hs (by simp)
    have hcR' : c⁻¹ ∈ R := hs (by simp)
    obtain ⟨u, hu, hua⟩ := ha
    have e1 : ∀ z : R ⊗[k] A, ((contr l R z : R) : L) =
        contr l L (Algebra.TensorProduct.map R.val (AlgHom.id k A) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, Subalgebra.coe_add]
    have e2 : ∀ z : R ⊗[k] A, φ (contr l R z) =
        l (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul, mul_comm]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have h1 : contr l R u = ⟨c, hcR⟩ := Subtype.ext (by rw [e1, hu])
    have h2 : φ ⟨c, hcR⟩ = 0 := by rw [← h1, e2, hua, h0, map_zero]
    have h3 : (⟨c, hcR⟩ : R) * ⟨c⁻¹, hcR'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hl)
    have h4 := congrArg φ h3
    rw [map_mul, h2, zero_mul, map_one] at h4
    exact zero_ne_one h4
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassOfBoundedOfCyclesLift
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory

set_option backward.isDefEq.respectTransparency false in
private theorem hb_step {C : Type*} [Category C] [Preadditive C] (K D : CochainComplex C ℤ)
    (H : ∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 →
      ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f)
    (n p₀ : ℤ) (z : Cochain K D n) (hz : δ n (n + 1) z = 0)
    (hv : ∀ (p q : ℤ) (hpq : p + n = q), p₀ < p → z.v p q hpq = 0) :
    ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q), p₀ ≤ p →
      (z - δ (n - 1) n γ).v p q hpq = 0 := by
  have hf : z.v p₀ (p₀ + n) rfl ≫ D.d (p₀ + n) (p₀ + n + 1) = 0 := by
    have h0 := congrArg (fun c => Cochain.v c p₀ (p₀ + n + 1) (by omega)) hz
    simp only [Cochain.zero_v] at h0
    rw [δ_v n (n + 1) rfl z p₀ (p₀ + n + 1) (by omega) (p₀ + n) (p₀ + 1) (by omega) rfl,
      hv (p₀ + 1) (p₀ + n + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at h0
    exact h0
  obtain ⟨g, hg⟩ := H p₀ (p₀ + n) (z.v p₀ (p₀ + n) rfl) hf
  refine ⟨Cochain.single g (n - 1), ?_⟩
  intro p q hpq hp
  rw [Cochain.sub_v, δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
    Cochain.single_v_eq_zero g (n - 1) (p + 1) q (by omega) (by omega), comp_zero, smul_zero, add_zero]
  rcases hp.lt_or_eq with hlt | rfl
  · rw [hv p q hpq hlt, Cochain.single_v_eq_zero g (n - 1) p (q - 1) (by omega) (by omega), zero_comp,
      sub_zero]
  · subst hpq
    rw [Cochain.single_v, hg, sub_self]

end UpperTheory

theorem UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift :
    ∀ (K D : Cx ℤ) [K.IsStrictlyLE 0] (a : ℤ) [D.IsStrictlyGE a], (∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 → ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f) → ∀ n : ℤ, Subsingleton (CohomologyClass K D n) := by
  intro K D _ a _ H n
  have hz0 : ∀ (z : Cocycle K D n) (k : ℕ), ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q),
      -(k : ℤ) < p → ((z : Cochain K D n) - δ (n - 1) n γ).v p q hpq = 0 := by
    intro z k
    induction k with
    | zero =>
      refine ⟨0, fun p q hpq hp => ?_⟩
      exact (K.isZero_of_isStrictlyLE 0 p (by simpa using hp)).eq_of_src _ _
    | succ k ih =>
      obtain ⟨γ, hγ⟩ := ih
      obtain ⟨γ', hγ'⟩ := UpperTheory.hb_step K D H n (-(k : ℤ)) ((z : Cochain K D n) - δ (n - 1) n γ)
        (by rw [δ_sub, z.δ_eq_zero, δ_δ, sub_zero]) (fun p q hpq hp => hγ p q hpq hp)
      refine ⟨γ + γ', fun p q hpq hp => ?_⟩
      rw [δ_add, ← sub_sub]
      exact hγ' p q hpq (by push_cast at hp; omega)
  have all : ∀ z : Cocycle K D n, CohomologyClass.mk z = 0 := by
    intro z
    obtain ⟨γ, hγ⟩ := hz0 z (n - a + 1).toNat
    have hk := Int.self_le_toNat (n - a + 1)
    have hzero : (z : Cochain K D n) - δ (n - 1) n γ = 0 := by
      apply Cochain.ext
      intro p q hpq
      rw [Cochain.zero_v]
      by_cases hp : -((n - a + 1).toNat : ℤ) < p
      · exact hγ p q hpq hp
      · exact (D.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, γ, (sub_eq_zero.mp hzero).symm⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [all x, all y]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TensorFractionRingExistsMulEqOfDenominator
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add (f := _), map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
end

