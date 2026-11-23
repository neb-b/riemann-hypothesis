module

public import Formalism.RankGapBounds.TheoremALocOfLemmaA

@[expose] public section

noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

theorem tensor_reduction_holds : TensorStep := by
  intro k _ ι _ A _ _ B l e hB y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [smul_comm]
    refine Submodule.smul_mem _ r ?_
    have h1 : l ^ (∑ i, e i) • PiTensorProduct.tprod k f =
        PiTensorProduct.tprod k (fun i => ((⟨l ^ e i • f i, hB i (f i)⟩ : B i) : A i)) := by
      show _ = PiTensorProduct.tprod k (fun i => l ^ e i • f i)
      rw [MultilinearMap.map_smul_univ]
      simp only [RingHom.id_apply, Finset.prod_pow_eq_pow_sum]
    rw [h1]
    exact ⟨PiTensorProduct.tprod k (fun i => (⟨l ^ e i • f i, hB i (f i)⟩ : B i)), by
      rw [PiTensorProduct.map_tprod]; rfl⟩
  | add x y hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

end Formalism.RankGapBounds.FormsTensorLocalization
