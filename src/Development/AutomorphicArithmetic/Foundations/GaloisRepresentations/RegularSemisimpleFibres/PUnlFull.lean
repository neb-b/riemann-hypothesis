module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unlFull :
    UnlFull := by
  intro k _ _ _ _ _ N V _ _ π s x hd hs hu
  have hmem : ∀ a, x a ∈ Finset.univ.val.map x := fun a =>
    Multiset.mem_map_of_mem x (Finset.mem_univ_val a)
  have hx : ∀ a, (x a).IsCusp := fun a => hs.isCusp (hmem a)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k s N (fun a => Segment.single (x a) (hx a)) x hd
      (fun a b => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx a) (hx b) (hu _ (hmem b) _ (hmem a))
        (hu _ (hmem a) _ (hmem b)))
      (fun a => (single_spec (hx a)).2.1)
  have h1 := GlobalTheory.LocGL.SupportPerm.isSubquotient_prodIrr_of_hasSupport
    UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N s ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ x hd hs
  haveI := GlobalTheory.ReducedFactor.nontrivial_of_irr hs.isIrreducible
  have equiv_of_sub {G A B : Type} [Group G] [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] {σ : Representation ℂ G B}
      {ρ : Representation ℂ G A} (h : IsSubquotient σ ρ) [Nontrivial B]
      (hirr : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : B)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E⟩ := equiv_of_sub h1 hP
  exact ⟨E.symm⟩
