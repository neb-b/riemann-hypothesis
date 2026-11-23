module

public import Formalism.LatticeTheta.LatticeThetaProofs.Bundle0002
public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries
public import Formalism.LatticeTheta.LatticeThetaProofs.Bundle0001

@[expose] public section

namespace Formalism.H

section
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem dualIsLattice : DualIsLattice (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  refine isLattice_of_eq_span (LinearMap.BilinForm.dualBasis (innerₗ V)
    dualLattice_innerₗ_nondegenerate e) (dual Λ) ?_
  rw [← he, dualLattice_dual_span_eq e]

theorem dualDual : DualDual (V := V) := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  rw [← he, dualLattice_dual_span_eq e, dualLattice_dual_span_eq,
    LinearMap.BilinForm.dualBasis_dualBasis _ innerₗ_isSymm]

variable [MeasurableSpace V] [BorelSpace V]

theorem covolumeDual : CovolumeDual (V := V) := by
  intro Λ _ _ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  subst he
  have h := covolDual_det_mul
    ((stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)) e
  set o := (stdOrthonormalBasis ℝ V).reindex ((stdOrthonormalBasis ℝ V).toBasis.indexEquiv e)
  set eD := LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e with heD
  have hli : LinearIndependent ℤ e := e.linearIndependent.restrict_scalars' ℤ
  have hliD : LinearIndependent ℤ eD := eD.linearIndependent.restrict_scalars' ℤ
  have heq : Submodule.span ℤ (Set.range eD) = dual (Submodule.span ℤ (Set.range e)) :=
    (dualLattice_dual_span_eq e).symm
  have hb : ((↑) : Submodule.span ℤ (Set.range e) → V) ∘ Module.Basis.span hli = e :=
    funext fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  have hbD : ((↑) : dual (Submodule.span ℤ (Set.range e)) → V) ∘
      (Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq) = eD :=
    funext fun i => by simp [Module.Basis.span_apply]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume
      ((Module.Basis.span hliD).map (LinearEquiv.ofEq _ _ heq)) o.toBasis,
    ZLattice.covolume_eq_det_mul_measureReal _ MeasureTheory.volume (Module.Basis.span hli) o.toBasis, hb, hbD,
    covolDual_vol_fd, mul_one, mul_one, ← abs_inv]
  exact congrArg abs (eq_inv_of_mul_eq_one_left h)

theorem poissonDecay : PoissonDecay (V := V) := poissonDecay_of (dualIsLattice V) (lattice_summable_decay V) (poisson_periodization V)
  (unfolding_fourier_coefficient V) (lattice_fourier_series V)

theorem poissonSchwartz : PoissonSchwartz (V := V) := poissonSchwartz_of (poissonDecay V) (schwartz_decay_gaussian V)

end

end Formalism.H
