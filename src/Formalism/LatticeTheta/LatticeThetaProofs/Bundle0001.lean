module

public import Formalism.LatticeTheta.Statement

@[expose] public section

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.CovolumeDual
section
open MeasureTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

lemma covolDual_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

lemma covolDual_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ V) (e : Module.Basis ι ℝ V) :
    o.toBasis.det (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) * o.toBasis.det e = 1 := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  set P := o.toBasis.toMatrix e with hP
  set Q := o.toBasis.toMatrix (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) with hQ
  have hM : Qᵀ * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ k, Qᵀ i k * P k j =
        ⟪LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e i, e j⟫ := by
      simp only [hP, hQ, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← o.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm (o k)]
    rw [hsum]
    have h := LinearMap.BilinForm.apply_dualBasis_left covolDual_nondegenerate e i j
    simp only [innerₗ_apply_apply] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hM, Matrix.det_one]

lemma covolDual_vol_fd {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ V) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def,
    MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.DualLattice
section
@[expose] section

noncomputable section

namespace Formalism.H

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma dualLattice_innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  first
    | exact (LinearMap.BilinForm.nondegenerate_iff (innerₗ V)
        (fun x => by rw [innerₗ_apply_apply]; exact real_inner_self_nonneg) isSymm_inner).2
        (fun x => by rw [innerₗ_apply_apply]; exact inner_self_eq_zero)
    | (unfold LinearMap.BilinForm.Nondegenerate
       intro m hm
       have h := hm m
       rw [innerₗ_apply_apply] at h
       exact inner_self_eq_zero.mp h)

lemma innerₗ_isSymm : LinearMap.BilinForm.IsSymm (innerₗ V) := by
  first
    | exact fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _
    | exact ⟨fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _⟩
    | (intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)
    | (constructor; intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)

variable [FiniteDimensional ℝ V]

lemma exists_basis_span_eq (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (e : Module.Basis ι ℝ V),
      Submodule.span ℤ (Set.range e) = Λ := by
  classical
  exact ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, inferInstance,
    Module.Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ Λ),
    Module.Basis.ofZLatticeBasis_span ℝ Λ _⟩

lemma isLattice_of_eq_span {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
  subst h
  refine ⟨inferInstance, ?_⟩
  intro _
  infer_instance

lemma dualLattice_dual_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) =
      Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ V) dualLattice_innerₗ_nondegenerate e)) := LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) dualLattice_innerₗ_nondegenerate e

end Formalism.H
end
end

