module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_entries {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = m.1.val i j) ∧
      ∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = m.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> rfl

theorem blocks_of_blk_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (hk : blk h w m X ∈ GlobalTheory.LFun.KGL w (n := n)) :
    m.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ m.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [CtLevel.blk_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w m X).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w _ _).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w m X).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w _ _).2] at this

end PositivityTheory.Rg.BcB.F.Tail.B

end
