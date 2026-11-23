module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

@[expose] public section

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cntE_eq_zero_of_empty {D : Formalism.BasicNotions.D7} {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (h : EZ T' F0 Λ Z = ∅) : cntE T' F0 Λ Z = 0 := by
  unfold cntE
  rw [h]
  simp

theorem nu_eq_zero_of_empty {D : Formalism.BasicNotions.D7} {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (Z : MatZ D) (h : ∀ Λ ∈ what₂, EZ T' F0 Λ Z = ∅) :
    Formalism.L2.SG.CntLocal.nu T' F0 what₂ Z = 0 := by
  unfold Formalism.L2.SG.CntLocal.nu
  rw [Finset.sum_eq_zero (fun Λ hΛ => by rw [cntE_eq_zero_of_empty T' F0 Λ Z (h Λ hΛ)]; simp), zero_div]

end PI.CntNotIntW
