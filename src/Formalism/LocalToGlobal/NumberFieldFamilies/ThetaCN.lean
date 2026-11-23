module

public import Formalism.LocalToGlobal.NumberFieldFamilies.Bundle0002
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCT
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCR

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tri

variable {R : Type} [CommRing R] {ρ : ℕ}

def UTri (T : Matrix (Fin ρ) (Fin ρ) R) : Prop := ∀ j i, i ≤ j → (T - 1) j i = 0

theorem left_inv {K : Type} [Field K] {n : ℕ} (C : Matrix (Fin n) (Fin ρ) K) (h : LinearIndependent K C.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) K, L * C = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end Tri

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def eA : Matrix (Fin B.rank) (Fin d.ρ) (AE D) := d.e.map (incA D)

def lA : Matrix (Fin d.ρ) (Fin B.rank) (AE D) := (left_inv d.e d.e_iso.1).choose.map (incA D)

def tM (n : GA D B) : Matrix (Fin d.ρ) (Fin d.ρ) (AE D) := HMul.hMul (lA d) (HMul.hMul (mt B n) (eA d))

def bV (n : GA D B) (x : Fin B.rank → D.host.E) : Fin d.ρ → AE D := (lA d).mulVec ((mt B n).mulVec (ratV x) - ratV x)

def Perp (x : Fin B.rank → D.host.E) : Prop :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram).mulVec x = 0

def Good (n : GA D B) : Prop :=
  HMul.hMul (mt B n) (eA d) = HMul.hMul (eA d) (tM d n) ∧ UTri (tM d n) ∧
    ∀ x, Perp d x → (mt B n).mulVec (ratV x) = ratV x + (eA d).mulVec (bV d n x)

variable {d}


theorem trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R] (r : E) :
    Algebra.trace R (R ⊗[F] E) (inclR R r) = algebraMap F R (Algebra.trace F E r) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  rfl

end Formalism.L2.Fam.ThC

end
