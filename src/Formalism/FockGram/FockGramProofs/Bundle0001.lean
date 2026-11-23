module

public import Mathlib
public import Formalism.FockGram.StatementLat

@[expose] public section

-- bundled from Formalism.FockGram.FockGramProofs.CovolGram
section
open Matrix LinearMap Module MeasureTheory

noncomputable section

namespace Formalism.E

theorem covolumeEqSqrtDetGram : CovolGram := by
  intro E ι _ _ _ _ _ _ _ b
  classical

  have hc : Fintype.card (Fin (Module.finrank ℝ E)) = Fintype.card ι := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq hc)
  have hfd : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume),
      measureReal_def, ZSpan.measure_fundamentalDomain b volume o.toBasis, hfd, mul_one,
      ENNReal.toReal_ofReal (abs_nonneg _)]

  have hg : Matrix.gram ℝ b = (o.toBasis.toMatrix b)ᵀ * o.toBasis.toMatrix b := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [← o.sum_inner_mul_inner (b i) (b j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm (o k) (b i)]
  rw [hcov, hg, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]

end Formalism.E
end
end

-- bundled from Formalism.FockGram.FockGramProofs.SubIndexNorm
section
open Matrix Module

namespace Formalism.E

theorem indexEqNormDet : SubIndexNorm := by
  intro S M ι _ _ _ _ _ _ _ b N bN
  classical
  haveI : Module.Free S M := Module.Free.of_basis b
  haveI : Module.Finite S M := Module.Finite.of_basis b
  haveI : Module.Free ℤ M := Module.Free.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  haveI : Module.Finite ℤ M := Module.Finite.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  let e0 : M ≃ₗ[S] N := b.equiv bN (Equiv.refl ι)
  let f : M →ₗ[S] M := N.subtype ∘ₗ e0.toLinearMap
  have hS : b.det (fun i => (bN i : M)) = LinearMap.det f := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext x y
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [f, e0]
  let N' : Submodule ℤ M := N.restrictScalars ℤ
  let e : M ≃ₗ[ℤ] N' := (e0.trans (Submodule.restrictScalarsEquiv ℤ S M N).symm).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv N' e
  have hcard : Nat.card (M ⧸ N') = Nat.card (M ⧸ N) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv
  rw [← hcard, ← h1, hS, ← LinearMap.det_restrictScalars]
  congr 2

end Formalism.E
end

