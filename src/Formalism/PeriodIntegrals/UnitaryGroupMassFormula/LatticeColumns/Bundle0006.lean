module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.PrincipalCongruenceLeLevel

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HSubCmp
section
noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl MassDataIdxStIm
open scoped TensorProduct

section Split

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

theorem pr_eq_iff {m : Type} (v w : m → R ⊗[F] E) : v = w ↔ pr1 θ v = pr1 θ w ∧ pr2 θ v = pr2 θ w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    apply θ.injective
    have e1 := congrFun h1 i
    have e2 := congrFun h2 i
    rw [fst_apply_alt, fst_apply_alt] at e1
    rw [snd_apply_alt, snd_apply_alt] at e2
    exact Prod.ext e1 e2

theorem mem_Hsub_iff {r : ℕ} (P : Frame E n r) (g : HA R σ J) :
    g ∈ Hsub R σ J P ↔ ∀ b : Fin (r + 1 + r),
      cmp1 σ J θ g *ᵥ pr1 θ (ratV (F := F) R (tupH P b)) = pr1 θ (ratV (F := F) R (tupH P b)) ∧
      cmp2 σ J θ g *ᵥ pr2 θ (ratV (F := F) R (tupH P b)) = pr2 θ (ratV (F := F) R (tupH P b)) := by
  rw [show (g ∈ Hsub R σ J P) ↔ g ∈ stabT R σ J (tupH P) from Iff.rfl, mem_stabT]
  refine forall_congr' fun b => ?_
  rw [pr_eq_iff θ]
  simp only [lin, Matrix.mulVecLin_apply, firstProj_split_mulVec, secondProj_split_mulVec]
  rfl

end Split

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxDone
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem global_index_eq_prod_local : IdxProdH := idxProdH_of level_components_surjective level_membership_local

def LocRedRest : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HImU X hb u p

theorem locRedH_of_rest (h : LocRedRest) : LocRedH :=
  locRedH_of fun X hb hK u hT hL p =>
    ⟨(h X hb hK u hT hL p).1, (h X hb hK u hT hL p).2.1, hKerIn_of_levelSubgroupCharacter_of_normalized X hb hK hL u p, (h X hb hK u hT hL p).2.2⟩

theorem idxCountStep_of_rest (h : LocRedRest) : IdxCountStep :=
  idxCountStep_of global_index_eq_prod_local (locRedH_of_rest h)

end PIW.MassDataColumns
end
end

