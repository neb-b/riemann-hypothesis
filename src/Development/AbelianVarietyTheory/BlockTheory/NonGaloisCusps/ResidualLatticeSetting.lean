module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def maxLam (i : X.Tw) (M : ℕ) (ι : Type) : Ideal (abelian₂ X i M ι) :=
  (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ⊔
    Ideal.span (Set.range fun q : ι => toLam X i M ι (MvPolynomial.X q))

theorem maxLam_ne_top (i : X.Tw) (M : ℕ) (ι : Type) : maxLam X i M ι ≠ ⊤ := by
  classical
  let ε : abelian₂ X i M ι →ₐ[X.O0 i] X.O0 i := MonoidAlgebra.lift (X.O0 i) (X.O0 i) (Del X i M ι) 1
  let φ : abelian₂ X i M ι →+* IsLocalRing.ResidueField (X.O0 i) :=
    (IsLocalRing.residue (X.O0 i)).comp ε.toRingHom
  have hle : maxLam X i M ι ≤ RingHom.ker φ := by
    unfold maxLam
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [φ, ε, IsLocalRing.residue_eq_zero_iff] using hc
    · rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      simp [φ, ε, toLam]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top φ) hle

variable {X} (bkP : BKPh X)


end GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

end
