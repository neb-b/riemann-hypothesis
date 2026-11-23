module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem WitA.iso' [IsCMField F] (e : RepIso r r') (h : WitA ι r) : WitA ι r' :=
  have u : ∀ {r r' : G F Ω →* GL (Fin n) (Qbar l)}, RepIso r r' → ∀ v, (Unl1 r v → Unl1 r' v) ∧ (PotUnl r v → PotUnl r' v) :=
    fun e _ => ⟨fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩, fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩⟩
  ⟨fun v hv k => (u e v).2 (h.1 v hv ((u e.symm' v).1 k)), fun π hreg ha =>
    (h.2 π hreg (attC_iso e.symm' ha)).imp fun _ ht v hv => ht v (hv.imp id (u e.symm' v).2)⟩

end UpperTheory.V.Z.Win
