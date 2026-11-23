module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Columns.Bundle0002
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RowForms

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
  (j : H.V →ₛₗ[σ] M) (c : Module.Basis H.ι ℂ M) (hc : ∀ i, c i = j (H.b i))




end Gen

section Pack

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)





end Pack

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (hX : B.fields.Ok)



theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

end Build





end GlobalTheory.Mem.Df.Model

end
