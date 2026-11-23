module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

structure SignedPar (n : ℕ) where
  lam : Fin n → ℝ
  sgn : Fin n → Bool
  hc : Formalism.QuantumDeterminants.IsHCParam lam

namespace SignedPar

variable {n : ℕ} (P : SignedPar n)

def p : ℕ := (Finset.univ.filter fun a => P.sgn a = true).card

def q : ℕ := (Finset.univ.filter fun a => P.sgn a = false).card

def IsOfSig (p q : ℕ) : Prop := P.p = p ∧ P.q = q

def low : Fin n → ℝ := Formalism.QuantumDeterminants.lowK P.sgn P.lam

end SignedPar

section Chains

variable {R : Ranks} (c : HCParam R)

end Chains

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := V.gram.map (tauE D τ)

end Adelic

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsDSPar {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDS P.sgn P.lam σ

end Rep

section Signatures

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latAt (v : HeightOneSpectrum (𝓞 F)) {M : ℕ} (L : Set (Fin M → E)) :
    AddSubgroup (Fin M → v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

def LocIsom (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) {M M' : ℕ} (G : Matrix (Fin M) (Fin M) E)
    (G' : Matrix (Fin M') (Fin M') E) (L : Set (Fin M → E)) (L' : Set (Fin M' → E)) : Prop :=
  ∃ (A : Matrix (Fin M') (Fin M) (v.adicCompletion F ⊗[F] E)) (B : Matrix (Fin M) (Fin M') (v.adicCompletion F ⊗[F] E)),
    A * B = 1 ∧ B * A = 1 ∧
    Formalism.UG.cT (Algebra.TensorProduct.map (AlgHom.id F (v.adicCompletion F)) hc.sig).toRingHom A *
              G'.map (fun x => (1 : v.adicCompletion F) ⊗ₜ[F] x) * A = G.map (fun x => (1 : v.adicCompletion F) ⊗ₜ[F] x) ∧
    ∀ y, y ∈ latAt v L ↔ A.mulVec y ∈ latAt v L'

def coordLat (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def HermSignatures (hc : CMData F E) : Prop :=
  (∀ (M : ℕ) (sg : (E →+* ℂ) → ℕ × ℕ), 1 ≤ M → (∀ τ, (sg τ).1 + (sg τ).2 = M) →
    (∀ τ, sg (ComplexEmbedding.conjugate τ) = sg τ) → Even (∑ w : InfinitePlace E, (sg w.embedding).2) →
      ∃ W : HSpace E, W.rank = M ∧ W.SigOK ∧ W.sig = sg) ∧
  (∀ M p q : ℕ, 1 ≤ M → p + q = M → ∃ W : HSpace E, W.rank = M ∧ W.SigOK ∧ ∀ τ, W.sig τ = (p, q)) ∧
  (∀ W W' : HSpace E, W.SigOK → W'.SigOK → W.sig = W'.sig →
    ∃ ι : W.V ≃ₗ[E] W'.V, HSpace.IsIsomEmb W W' (ι : W.V →ₗ[E] W'.V)) ∧
  ∀ W W' : HSpace E, W.rank = W'.rank → ∀ v : HeightOneSpectrum (𝓞 F),
    LocIsom hc v W.gram W'.gram (coordLat W) (coordLat W')

def IsSkewSelfDual {M : ℕ} (S : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  Sᴴ = -S ∧ S.det ≠ 0 ∧ Submodule.IsLattice E L ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ S.mulVec x ∈ (1 : Submodule (𝓞 E) E)

def SkewSig (δ : E) {M : ℕ} (S : Matrix (Fin M) (Fin M) E) (p q : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, Formalism.UG.HasSignature ((δ⁻¹ • S).map τ) p q

def SkewSignatures (hc : CMData F E) (δ : E) : Prop :=
  ∀ M : ℕ, Even M →
    (∀ p q : ℕ, p + q = M → ∃ (S : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)),
      IsSkewSelfDual S L ∧ SkewSig δ S p q) ∧
    ∀ (S S' : Matrix (Fin M) (Fin M) E) (L L' : Submodule (𝓞 E) (Fin M → E)),
      IsSkewSelfDual S L → IsSkewSelfDual S' L' →
        (∀ p q : ℕ, SkewSig δ S p q → SkewSig δ S' p q →
          ∃ g : GL (Fin M) E, (g : Matrix (Fin M) (Fin M) E)ᴴ * S' * (g : Matrix (Fin M) (Fin M) E) = S) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), LocIsom hc v S S' (L : Set (Fin M → E)) (L' : Set (Fin M → E))

end Signatures

def IsWittIndex {M : ℕ} (G : Matrix (Fin M) (Fin M) ℂ) (r : ℕ) : Prop :=
  IsGreatest {s | ∃ W : Submodule ℂ (Fin M → ℂ), Module.finrank ℂ W = s ∧
    ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ G.mulVec y = 0} r

def WittIndexReal : Prop :=
  ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → IsWittIndex G (min p q)

def Signatures : Prop :=
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E), Even (Module.finrank ℚ F) → (∀ x : E, IsOfFinOrder x → x = 1 ∨ x = -1) →
    ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → star δ = -δ →
      HermSignatures hc ∧ SkewSignatures hc δ) ∧
  WittIndexReal

end GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Volume

variable {D : D7}

def volBox (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (B : D.what₂.Tau → Set (UpqT P Q)) : Set (GA D V) :=
  {h | ∃ k ∈ KsphC V ∅, ∃ g ∈ GinfC V, h = k * g ∧
    ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) g}

def IsProductForm (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (μ : Measure (GA D V)) : Prop :=
  ∀ B : D.what₂.Tau → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    μ (volBox θ V A B) = ∏ ρ, D.cd.cd P Q (B ρ)

variable (D)

end Volume

section Ideles

variable (D : D7)

abbrev AE : Type := AF D.host.F ⊗[D.host.F] D.host.E

abbrev IdE : Type := (AE D)ˣ

abbrev IdF : Type := (AF D.host.F)ˣ

def resF : IdF D →* IdE D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom :
    AF D.host.F →+* AF D.host.F ⊗[D.host.F] D.host.E).toMonoidHom

def ratF : D.host.Fˣ →* IdF D := Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom

def conjId : IdE D →* IdE D := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def normId : IdE D →* IdE D := MonoidHom.id (IdE D) * conjId D

end Ideles

section Hecke

variable (D : D7)

def normGroup : Subgroup (IdF D) := (ratF D).range ⊔ (normId D).range.comap (resF D)


variable {D}


variable (D)

end Hecke

section Witt

variable {D : D7}

variable (D)

end Witt

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryVolumePairs

end
end

