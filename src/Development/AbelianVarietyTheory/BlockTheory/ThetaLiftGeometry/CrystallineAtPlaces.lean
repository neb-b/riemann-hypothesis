module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits NumberField IsDedekindDomain GlobalTheory.HTW

variable (D : D7)

def Splits (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i]
      ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable {D} (L : SizeData₂ D) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Place

variable {D}

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces
