module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section AnyLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end AnyLat

section Row

variable (D : D7)

def sumMap {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    ((D.sp.X 0).V × D.host.E) →ₗ[D.host.E] (VS D).V :=
  (D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)

def latL {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) :=
  (Lsub Λ (lf D F0)).comap ((sumMap D F0).restrictScalars (𝓞 D.host.E))

abbrev flagPairDefinitePartLattice {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
  L0X D Λ (lf D F0)

end Row

theorem mem_orthModIsotropicLatticePerpNegative_iff (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (hz : F0.z = D.zmOf u) (Λ : LatV D) (w : (D.sp.X 0).V) :
    w ∈ flagPairDefinitePartLattice D F0 Λ ↔ (w, (0 : D.host.E)) ∈ latL D F0 Λ := by
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w) = 0 := by
    have h1 : (VS D).hT (D.sp.iXY 0 w) F0.z = 0 := by
      rw [hz, D7.zmOf, map_smul, D.sp.zm_orth w, smul_zero]
    have h2 := (VS D).herm.eq (D.sp.iXY 0 w) F0.z
    rw [h1, map_zero] at h2
    exact h2.symm
  simp [flagPairDefinitePartLattice, L0X, L0sub, latL, sumMap, h0]

end GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

end
