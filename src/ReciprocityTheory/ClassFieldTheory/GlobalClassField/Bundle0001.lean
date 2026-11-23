module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLim
section
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

open _root_.Neutral.B1 Topology Function
open scoped commutatorElement

variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}

theorem toAb_surjective : Surjective (toAb F) := QuotientGroup.mk'_surjective _

theorem abRestrict_toAb_eq_one_iff (h : IsFiniteAbelian F L) (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    abRestrict F L h (toAb F g) = 1 ↔ g ∈ L.fixingSubgroup := by
  have := h.isGalois
  rw [abRestrict_mk, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]

theorem isGalois_algebraicClosure [CharZero F] : IsGalois F (AlgebraicClosure F) := ⟨⟩

theorem isFiniteAbelian_of_commutator_le [CharZero F] (hfd : FiniteDimensional F L)
    (hc : commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≤ L.fixingSubgroup) :
    IsFiniteAbelian F L := by
  have := isGalois_algebraicClosure (F := F)
  have hn : L.fixingSubgroup.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn
  have hG : IsGalois F L := (InfiniteGalois.normal_iff_isGalois L).1 hn
  refine ⟨hfd, hG, fun a b => ?_⟩
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) a
  obtain ⟨k, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) b
  have h2 : ⁅g, k⁆ ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) L).ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k))
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem mem_closure_commutator_iff [CharZero F] (g : Field.absoluteGaloisGroup F) :
    g ∈ (commutator (Field.absoluteGaloisGroup F)).topologicalClosure ↔
      ∀ L : IntermediateField F (AlgebraicClosure F), IsFiniteAbelian F L → g ∈ L.fixingSubgroup := by
  have := isGalois_algebraicClosure (F := F)
  constructor
  · intro hg L hL
    have h1 : toAb F g = 1 := (QuotientGroup.eq_one_iff g).2 hg
    exact (abRestrict_toAb_eq_one_iff hL g).1 (by rw [h1, map_one])
  · intro hg
    let C : ClosedSubgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
      ⟨(commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).topologicalClosure,
        Subgroup.isClosed_topologicalClosure _⟩
    have hC : (IntermediateField.fixedField C.1).fixingSubgroup = C.1 :=
      InfiniteGalois.fixingSubgroup_fixedField C
    show g ∈ C.1
    rw [← hC]
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : IntermediateField.adjoin F {x} ≤ IntermediateField.fixedField C.1 :=
      IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx)
    have hab : IsFiniteAbelian F (IntermediateField.adjoin F {x}) := by
      refine isFiniteAbelian_of_commutator_le hfd ?_
      refine le_trans ?_ (IntermediateField.fixingSubgroup_le hle)
      rw [hC]
      exact Subgroup.le_topologicalClosure _
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hg _ hab) x
      (IntermediateField.mem_adjoin_simple_self F x)

theorem abRestrict_separates [CharZero F] (x : Field.absoluteGaloisGroupAbelianization F)
    (hx : ∀ (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L), abRestrict F L h x = 1) : x = 1 := by
  obtain ⟨g, rfl⟩ := toAb_surjective x
  refine (QuotientGroup.eq_one_iff g).2 ((mem_closure_commutator_iff g).2 fun L hL => ?_)
  exact (abRestrict_toAb_eq_one_iff hL g).1 (hx L hL)

theorem abRestrict_ext [CharZero F] {x y : Field.absoluteGaloisGroupAbelianization F}
    (hxy : ∀ (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L),
      abRestrict F L h x = abRestrict F L h y) : x = y := by
  have := abRestrict_separates (x * y⁻¹) fun L h => by rw [map_mul, map_inv, hxy L h, mul_inv_cancel]
  exact mul_inv_eq_one.mp this

end ReciprocityTheory.DiscreteGroups.GlobalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def inertiaGroup (Q : Ideal (𝓞 L)) : Subgroup (L ≃ₐ[K] L) :=
  (Q.toAddSubgroup.inertia (𝓞 L ≃ₐ[𝓞 K] 𝓞 L)).comap (galRestrict (𝓞 K) K L (𝓞 L)).toMonoidHom

variable {K L}

theorem mem_inertiaGroup {Q : Ideal (𝓞 L)} {τ : L ≃ₐ[K] L} :
    τ ∈ inertiaGroup K L Q ↔ ∀ x : 𝓞 L, galRestrict (𝓞 K) K L (𝓞 L) τ x - x ∈ Q :=
  Iff.rfl

theorem galRestrict_apply_eq_smul (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    galRestrict (𝓞 K) K L (𝓞 L) τ x = τ • x := by
  apply RingOfIntegers.ext
  exact algebraMap_galRestrict_apply (𝓞 K) τ x

theorem inertiaGroup_eq_inertia (Q : Ideal (𝓞 L)) :
    inertiaGroup K L Q = Q.toAddSubgroup.inertia (L ≃ₐ[K] L) := by
  ext τ
  rw [mem_inertiaGroup]
  simp only [galRestrict_apply_eq_smul]
  rfl

theorem isFrobAt_iff_forall (τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) :
    IsFrobAt K L τ Q ↔ ∀ x : 𝓞 L, τ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q := by
  simp only [← galRestrict_apply_eq_smul]
  rfl

theorem under_smul_ideal (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) : (σ • Q).under (𝓞 K) = Q.under (𝓞 K) := by
  ext a
  rw [Ideal.mem_under, Ideal.mem_under, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  have : σ⁻¹ • (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
    rw [← galRestrict_apply_eq_smul, AlgEquiv.commutes]
  exact iff_of_eq (congrArg (· ∈ Q) this)

theorem isFrobAt_smul (σ τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) (h : IsFrobAt K L τ Q) :
    IsFrobAt K L (σ * τ * σ⁻¹) (σ • Q) := by
  rw [isFrobAt_iff_forall] at h ⊢
  intro x
  rw [under_smul_ideal, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  simpa [smul_sub, mul_smul] using h (σ⁻¹ • x)

section Over

variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]

theorem exists_liesOver (L : Type) [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal := by
  obtain ⟨⟨Q, h1, h2⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  exact ⟨Q, h1, h2⟩

theorem isFrobAt_unique (hv : IsUnramifiedIn K v L) (τ τ' : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q)
    (h' : IsFrobAt K L τ' Q) : τ = τ' := by
  have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    Ideal.ramificationIdx_eq_one_iff.mp (hv Q inferInstance inferInstance)
  have e := h.eq_of_isUnramifiedAt h' Q.primeCompl_le_nonZeroDivisors
  apply (galRestrict (𝓞 K) K L (𝓞 L)).injective
  exact AlgEquiv.ext fun x => DFunLike.congr_fun e x

variable [IsGalois K L]

theorem exists_smul_eq [Q'.IsPrime] [Q'.LiesOver v.asIdeal] : ∃ σ : L ≃ₐ[K] L, σ • Q = Q' :=
  Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal Q Q' (L ≃ₐ[K] L)

include v in
theorem card_inertiaGroup : Nat.card (inertiaGroup K L Q) = Q.ramificationIdx (𝓞 K) := by
  rw [inertiaGroup_eq_inertia]
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal Q).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[K] L))

theorem isFrobAt_of_comm (hc : ∀ a b : L ≃ₐ[K] L, a * b = b * a) [Q'.IsPrime]
    [Q'.LiesOver v.asIdeal] (τ : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q) : IsFrobAt K L τ Q' := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq v Q Q'
  have := isFrobAt_smul σ τ Q h
  rwa [hc σ τ, mul_inv_cancel_right] at this

end Over

end ReciprocityTheory.DiscreteGroups.GlobalClassField
end
end

