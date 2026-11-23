module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Inj

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

section Model
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)

theorem std_of_cof (hM : M.IsGood ψ) {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (h2.and hM.std).mono fun _ h => h.1.trans h.2

theorem pure_eq_pureA (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∃ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∀ f : SInf F (Fin n × Fin d), pure f φ = pureA F f g :=
  ⟨_, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 (std_of_cof M ψ hM h2),
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 (std_of_cof M ψ hM h2)⟩, fun _ => rfl⟩

theorem pure_at (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) (f : SInf F (Fin n × Fin d)) (v : Pl F) :
    ∃ r : (Fin n × Fin d → AF F) → ℂ, (∀ x z, At (evFin F v) z → r (x + z) = r x) ∧
      ∀ φ₂ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ w, w ≠ v → φ₂ w = φ w) →
        pure f φ₂ = tens (evFin F v) (φ₂ v) r := by
  classical
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (std_of_cof M ψ hM h2)
  refine ⟨r, hr, fun φ₂ h => ?_⟩
  have : φ₂ = Function.update φ v (φ₂ v) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp
    · rw [Function.update_of_ne hw, h w hw]
  rw [e (φ₂ v), ← this]
end Model

variable {B : Base F E} {Γ : Geo σ a a'} {X : Chars F E} {om : Rep σ Γ.V Γ.W} {om' : Rep σ Γ.V' Γ.W}

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

end GlobalTheory.CompanionTheory.Ar.RT.Inj

end
