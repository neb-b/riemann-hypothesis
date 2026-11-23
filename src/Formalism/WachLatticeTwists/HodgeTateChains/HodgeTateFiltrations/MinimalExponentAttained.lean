module

public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.Bundle0001
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem rVal : StatRVal := by
  intro ℓ _ w m hm h2 hw U i
  have key := (Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ w m hm h2 hw).2
    ((U.erase i).map ⟨fun a => a - i, sub_left_injective⟩) (by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      intro a ha h0
      exact (Finset.mem_erase.1 ha).1 (by omega))
  have hev : (Rpoly ℓ w U i).eval 1 =
      ∏ a ∈ U.erase i, (1 - ((w ^ (-(a - i)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    unfold Rpoly
    rw [eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [neg_sub]
  rw [Finset.prod_map, Finset.sum_map, Finset.card_map] at key
  simp only [Function.Embedding.coeFn_mk] at key
  rw [hev]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  unfold rI
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
