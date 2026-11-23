module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsElemDiv {v : HeightOneSpectrum (𝓞 F)} (x : GL (Fin n) (Fv F v)) (d : Fin n → (Fv F v)ˣ) : Prop :=
  ∃ k₁ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
    ∃ k₂ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      x.1 = k₁.1 * Matrix.diagonal (fun i => (d i : Fv F v)) * k₂.1

def IsInertUnder (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  (v : HeightOneSpectrum (𝓞 F))

def latMoved (g : GLoc σ J v) : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
  (latLoc F L v).comap ((Matrix.mulVecLin (matHom (Fv F v) σ J g⁻¹).1).restrictScalars (intLoc F E v))

def latLength (g : GLoc σ J v) : ℕ∞ :=
  Module.length (intLoc F E v)
    (latLoc F L v ⧸ (latLoc F L v ⊓ latMoved σ J L v g).submoduleOf (latLoc F L v))

def graphHgt (g : GLoc σ J v) : ℝ≥0 :=
  hgtFin σ (dblGram finSumFinEquiv J) L v (ioH (Fv F v) σ rfl (g, 1))

def SplitAt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : Prop :=
  ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ g : GLoc σ J v,
    (∃ d, IsElemDiv (splitEquivIn h hJ τ β g) d) ∧
    (∀ d, IsElemDiv (splitEquivIn h hJ τ β g) d →
      graphHgt σ J L v g = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹) ∧
    graphHgt σ J L v g ≤ 1

def InertAt : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
    (∃ l : ℕ, latLength σ J L v g = l ∧
      graphHgt σ J L v g = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ))) ∧
    graphHgt σ J L v g ≤ 1

def GraphNormFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → SplitAt σ J L v h hJ ∧ InertAt σ J L v

omit [NumberField E] in
theorem mem_latMoved {g : GLoc σ J v} {x : Fin n → Fv F v ⊗[F] E} :
    x ∈ latMoved σ J L v g ↔ (matHom (Fv F v) σ J g⁻¹).1 *ᵥ x ∈ latLoc F L v := Iff.rfl


end GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def IsInP (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X.IsHermitian ∧ ∀ i j, ε i = ε j → X i j = 0

def realRank : ℕ := min (Fintype.card {i // ε i = true}) (Fintype.card {i // ε i = false})

end Matrices

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end
end

