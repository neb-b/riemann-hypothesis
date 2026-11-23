module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions NumberField Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coordLat (W : HSpace E) : Submodule (𝓞 E) (Fin W.rank → E) :=
  W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))

def congSet (cm : CMData F E) (W : HSpace E) (g : ℕ) : Set (Formalism.UG.UPts cm.sig W.gram (Af F)) :=
  {x | (x : GL (Fin W.rank) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) (coordLat W)) ∧
    ∀ y ∈ lamAf (F := F) (coordLat W), ∃ z ∈ lamAf (F := F) (coordLat W),
      ((x : GL (Fin W.rank) (E ⊗[F] Af F)) - 1 : Matrix (Fin W.rank) (Fin W.rank) (E ⊗[F] Af F)) *ᵥ y =
        (g : E ⊗[F] Af F) • z}

structure InstData (cm : CMData F E) (W : HSpace E) (ε : InfinitePlace F → Fin W.rank → Bool)
    (φ : InfinitePlace F → (E →+* ℂ)) where
  J_herm : Formalism.UG.IsHerm (starRingEnd E) W.gram
  J_det : W.gram.det ≠ 0
  L_span : Submodule.span E (coordLat W : Set (Fin W.rank → E)) = ⊤
  L_fg : (coordLat W).FG
  L_dual : ∀ x : Fin W.rank → E, x ∈ coordLat W ↔
    ∀ y ∈ coordLat W, Formalism.UG.hform (starRingEnd E) W.gram y x ∈ (algebraMap (𝓞 E) E).range
  φ_over : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a
  P : InfinitePlace F → Matrix (Fin W.rank) (Fin W.rank) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * W.gram.map (φ v) * P v = Formalism.REAL.Jm (ε v)
  topf : TopologicalSpace (Formalism.UG.UPts cm.sig W.gram (Af F))
  topf_group : @IsTopologicalGroup _ topf _
  topf_open : ∀ g : ℕ, 1 ≤ g → @IsOpen _ topf (congSet cm W g)
  topf_basis : ∀ U ∈ @nhds _ topf 1, ∃ g : ℕ, 1 ≤ g ∧ congSet cm W g ⊆ U

end GlobalTheory.RowLev
