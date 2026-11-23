module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplS
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcS.LT

def SplitStr : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)), IsCMExt F E σ → ¬ IsField (Fv F v ⊗[F] E) →
    ∃ π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v,
      (∀ s, π₁ (sigR (Fv F v) σ s) = π₂ s) ∧ (∀ s, π₂ (sigR (Fv F v) σ s) = π₁ s) ∧
      (∀ c : Fv F v, π₁ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c ∧
        π₂ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c) ∧
      (∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t) ∧
      (∀ p q : Fv F v, ∃ s, π₁ s = p ∧ π₂ s = q)

end Formalism.L2.SG.Pf.NcS.LT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplit
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcSplit

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def SplitOm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (r : ℕ)
    (P : Frame E n r) (MG : MeasG σ J r) (MW : MeasW σ J P)
    (hT : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j)
    (νH : Measure (Fin (r + 1 + r) → Fin n → AF F ⊗[F] E)) (Λ : Set (Fin n → E)),
    StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → (gramE σ J (tupH P)).det ≠ 0 → 2 * (r + 1 + r) < n → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J →
    Formalism.L2.SG.Pf.NcWeil.SWc1W F E σ n J → MG.IsTextNorm → MW.IsTextNorm →
    IsOmT F E σ n J ψ (gramE σ J (tupH P)) hT νH →
    IsCompatT F E σ n J (tupH P) MG.μG MW.μH νH →
    0 < MG.μGf (Kf σ J Λ) → MG.μGf (Kf σ J Λ) < ⊤ →
    ∃ a' : ℝ, 0 < a' ∧
      (AllSome (SdW F E σ n J (Ainf F) (psiInf F ψ) (r + 1 + r)) fun μinf =>
       AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) (r + 1 + r)) fun νinf =>
       AllSome (fun fibInf : HermR (Ainf F) σ (r + 1 + r) → Measure (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) =>
         IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
           {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
       ∀ f : HA (Ainf F) σ J → ENNReal, Measurable f →
         ∀ s : (Fin (r + 1 + r) → Fin n → Ainf F ⊗[F] E) → HA (Ainf F) σ J,
           (∀ y, (∃ g : HA (Ainf F) σ J, g • ratTup (Ainf F) (tupH P) = y) → s y • ratTup (Ainf F) (tupH P) = y) →
           ∫⁻ g, f g ∂MG.μGinf = ENNReal.ofReal a' *
             ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf F) σ J)) ∂MW.μHinf
               ∂(fibInf (hermOf (Ainf F) σ (gramE σ J (tupH P)) hT))) ∧
      (MG.μGf (Kf σ J Λ)).toReal * a' =
        (MW.μHf (Subtype.val ⁻¹' (Kf σ J Λ : Set (HA (Af F) σ J)))).toReal *
          ∏' v : HeightOneSpectrum (𝓞 F),
            (omAt σ J ψ v ((gramE σ J (tupH P)).map (inclR (Fv F v)))
              {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • ratTup (Fv F v) (tupH P)}).toReal

end Formalism.L2.SG.Pf.NcSplit
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmLocU
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcLoc

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OmLocU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) → IsSDLoc σ J v Λ → UnramAt (E := E) v → a ≤ n → IsPrim v Λ Y →
  (∃ w ∈ OEv (E := E) v, (gramR (Fv F v) σ J Y).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J Y).det * w = 1) →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} =
      ENNReal.ofReal (absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (n - a + 1) n,
          (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

end Formalism.L2.SG.Pf.NcLoc
end
end

