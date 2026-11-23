module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB

namespace PositivityTheory.Rg.BcB.CV.AdelicTopology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ratCent_subset_range (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem discrete_ratCent (d : GL (Fin n) E) : DiscreteTopology (ratCent d) :=
  DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n)))
    GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (ratCent_subset_range d)

theorem countable_ratCent (d : GL (Fin n) E) : Countable (ratCent d) := by
  have := GlobalTheory.CompanionTheory.UnfoldCut.countable_GL (E := E) (n := n)
  have h : (ratCent d : Set (GA E n)).Countable :=
    (Set.countable_range (ratGL E n)).mono fun _ hx => by
      obtain ⟨g, hg⟩ := ratCent_subset_range d hx
      exact ⟨g, hg⟩
  exact h.to_subtype

end PositivityTheory.Rg.BcB.CV.AdelicTopology

theorem PositivityTheory.Rg.BcB.CV.pf_AdTop : PositivityTheory.Rg.BcB.DegBdd → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.CV.AdTop := by
  intro hD _ E _ _ _ n
  haveI : T2Space (GA E n) := GlobalTheory.CompanionTheory.UnfoldCut.t2Space_adelicGL_cmField (E := E) (n := n)
  haveI : T1Space (GA E n) := T2Space.t1Space
  refine ⟨GlobalTheory.CompanionTheory.UnfoldCut.locallyCompact_GA, inferInstance, GlobalTheory.CompanionTheory.UnfoldCut.secondCountable_GA,
    GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA, fun W => ?_, fun d => ?_⟩
  · let _ : MeasurableSpace (GA E n) := borel _
    have : BorelSpace (GA E n) := ⟨rfl⟩
    exact ((hD E n).2 W).measurable
  · have := PositivityTheory.Rg.BcB.CV.AdelicTopology.discrete_ratCent d
    exact ⟨Subgroup.isClosed_of_discrete, inferInstance, PositivityTheory.Rg.BcB.CV.AdelicTopology.countable_ratCent d⟩
