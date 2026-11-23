module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

end Mat

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.NonGenericLocalCheck

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem img_mul' (g h : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * h) Λ = img g (img h Λ) := by
  unfold img; rw [← Submodule.map_comp]; rfl

theorem img_one' (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x; simp [img]

theorem move_one (t : Term V M r) : move 1 t = t := by
  cases t; simp [move, img_one']

theorem move_mul (g h : V ≃ₗ[E] V) (t : Term V M r) : move (g * h) t = move g (move h t) := by
  simp [move, img_mul']

theorem over_of_isTermOver {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r)
    (h : IsTermOver P d t) : Over P d t := by
  refine ⟨1, fun _ _ => rfl, d, ⟨1, one_mem _, ?_, ?_, ?_⟩, by rwa [move_one]⟩
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x' y' x y hy' hy; rw [show y = x from Subtype.ext hy, show y' = x' from Subtype.ext hy']

theorem over_move_iff {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) (g : V ≃ₗ[E] V)
    (hg : IsUnitary H g) : Over P d (move g t) ↔ Over P d t := by
  constructor
  · rintro ⟨h, hh, d', hd, ht⟩
    exact ⟨h * g, fun x y => (hh _ _).trans (hg x y), d', hd, by rwa [move_mul]⟩
  · rintro ⟨h, hh, d', hd, ht⟩
    refine ⟨h * g⁻¹, fun x y => (hh _ _).trans ?_, d', hd, ?_⟩
    · rw [← hg]; simp
    · rwa [← move_mul, mul_assoc, inv_mul_cancel, mul_one]

end Loc

section Glob

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs

variable {D : D7}

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

end Glob

end GlobalTheory.LocOver.Check
