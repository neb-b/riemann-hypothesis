module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
public import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.ExistsUniqueIrredSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace PositivityTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end PositivityTheory.Pf1.SegRepC.Uniq

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.SegTwo

def RhoNuRhoReducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def revTensor {d : ℕ} (σ : IrrRep (GL (Fin d) k)) :=
  piTensor fun a : Fin 2 => segTerm σ.ρ 2 a.rev



end PositivityTheory.Pf1.SegRepC.SegTwo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacMultiProdOfSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.Lift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_multiProd_segTerm {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
  isSmooth_parInd _ _


set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_multiProd_of_sub {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (isSmooth_multiProd_segTerm σ l)
    (IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective))

theorem perm_eq_one_of_lt_succ {l : ℕ} (w : Equiv.Perm (Fin l))
    (h : ∀ (i : ℕ) (hi : i + 1 < l), w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩) : w = 1 := by
  cases l with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have hm : StrictMono w.symm := Fin.strictMono_iff_lt_succ.2 fun i => h i.1 (by omega)
    have he : ∀ y, w.symm y = y := fun y => by
      have := congrArg (fun e : Fin (n + 1) ≃o Fin (n + 1) => e y)
        (Subsingleton.elim (hm.orderIsoOfSurjective _ w.symm.surjective) (OrderIso.refl _))
      simpa using this
    ext x
    have hx := he (w x)
    simp only [Equiv.symm_apply_apply] at hx
    simp [← hx]

end PositivityTheory.Pf1.SegRepC.Lift

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacOfLe
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end PositivityTheory.Pf1.SegRepC.PiLocalization₂

end
end

