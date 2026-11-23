module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001

@[expose] public section

noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.SerBridgeGLW

theorem trace_piTensorMap {s : ℕ} {M : Fin s → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let b := fun c => Module.Free.chooseBasis ℂ (M c)
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ i, (b c).repr (f c (b c i)) i := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (b c)]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]

theorem levi_mul' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  show blk K b c (((p * q : parab K b) : GL ι K) : Matrix ι ι K) =
    blk K b c ((p : GL ι K) : Matrix ι ι K) * blk K b c ((q : GL ι K) : Matrix ι ι K)
  rw [← blk_mul b c p.2.1 q.2.1]
  rfl

theorem levi_one' (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  show blk K b c (((1 : parab K b) : GL ι K) : Matrix ι ι K) = 1
  exact Matrix.submatrix_one _ Subtype.val_injective

def inflRep (K : Type) [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    Representation ℂ (parab K b) (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam p
  map_one' := by
    simp only [infl, levi_one', map_one]
    exact PiTensorProduct.map_one
  map_mul' p q := by
    simp only [infl, levi_mul', map_mul]
    exact PiTensorProduct.map_mul _ _

theorem mem_inv_linHom_iff {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (f : V →ₗ[ℂ] W) :
    f ∈ (Representation.linHom ρV ρW).invariants ↔ ∀ g, f ∘ₗ ρV g = ρW g ∘ₗ f := by
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g x)) (h g)
    simp only [Representation.linHom_apply, LinearMap.comp_apply, Representation.inv_self_apply] at this
    simp only [LinearMap.comp_apply]
    exact this.symm
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g⁻¹ x)) (h g)
    simp only [LinearMap.comp_apply, Representation.self_inv_apply] at this
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    exact this.symm

end PI.SerBridgeGLW
