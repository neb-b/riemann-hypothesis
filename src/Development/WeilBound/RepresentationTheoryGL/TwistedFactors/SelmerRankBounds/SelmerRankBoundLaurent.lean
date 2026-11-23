module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NumberField.AdeleRing TensorProduct

namespace PositivityTheory.Rg.Tf.Geo

def N0 : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ a, galAd σ (adeleMap F E a) = adeleMap F E a) ∧ (∀ x : E, galAd σ (algebraMap E 𝔸[E] x) = algebraMap E 𝔸[E] (σ x)) ∧
    (∀ y, (galAd σ)^[Module.finrank F E] y = y) ∧ Continuous (galAd σ) ∧ (∀ y, (galAd σ y).1 = galInf σ y.1) ∧
    (∀ a, galInf σ (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) a) = GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) a) ∧ Continuous (galInf σ) ∧
    Topology.IsClosedEmbedding (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (∀ y, atFin v (galAd σ y) = galFin σ v (atFin v y)) ∧
      (∀ a : 𝔸[F], atFin v (adeleMap F E a) = incFin E v (a.2 v)) ∧ (∀ a, galFin σ v (incFin E v a) = incFin E v a) ∧
      Continuous (galFin σ v) ∧ Topology.IsClosedEmbedding (incFin E v)

def SelmerRankBoundLaurent : Prop := ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (γ : GL (Fin n) F), IsRegSemisimple γ →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : GL (Fin n) (v.adicCompletion F),
      x⁻¹ * finAt v (AdelicGLn.diagonal F n γ) * x ∈ GLnLocal.integralGL (v.adicCompletion F) n ↔
      ∃ t, t * finAt v (AdelicGLn.diagonal F n γ) = finAt v (AdelicGLn.diagonal F n γ) * t ∧
        ∃ y ∈ GLnLocal.integralGL (v.adicCompletion F) n, x = t * y

end PositivityTheory.Rg.Tf.Geo
