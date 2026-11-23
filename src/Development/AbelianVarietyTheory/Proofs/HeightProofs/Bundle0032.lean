module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.PointAtPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice NumberField

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (σ : D.host.E →+* ℂ) :
    (∃ ρ, tauE D ρ = σ) ↔ ¬ ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    letI := D.host.cmStar
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    have h1 : star x = D.host.conj x := bridge_star_holds D.R D.host x
    have h2 : D.host.emb g (star x) = starRingEnd ℂ (D.host.emb g x) :=
      IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb g) x
    rw [h1] at h2
    exact h2.symm
  have key : ∀ g', (∃ ρ, tauE D ρ = D.host.emb g') ↔ g' ∈ D.R.Psi := fun g' => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g']
    exact exists_congr fun ρ => eq_comm
  rw [hc, key, key]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    Formalism.L2.Pj.archM V θ (a * b) = Formalism.L2.Pj.archM V θ a * Formalism.L2.Pj.archM V θ b := by
  unfold Formalism.L2.Pj.archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.L2.Pj.archM V θ 1 = 1 := by
  unfold Formalism.L2.Pj.archM
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_mem (V : HSp D) (k : GA D V) (h1 : k ∈ GfC V) (h2 : k ∈ GinfC V) : k = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have a1 : (infHom V k).1 = (infHom V 1).1 := by rw [map_one]; exact congrArg Units.val h1
  have a2 : (finHom V k).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val h2
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => e.injective (Prod.ext ?_ ?_)))
  · rw [(he _).1, (he _).1]; exact congrFun (congrFun a1 a) b
  · rw [(he _).2, (he _).2]; exact congrFun (congrFun a2 a) b

theorem existsUnique_isAtTau (V : HSp D) (τ : D.what₂.Tau)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ)) :
    ∃! h : GA D V, IsAtTau θ V τ g h := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => tauE_injective (hr _)
  obtain ⟨h1, -, -, h2⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  obtain ⟨h, hh, hu⟩ := h2 (fun σ => if r σ = τ then g else 1) (fun σ => by
    by_cases c : r σ = τ
    · rw [if_pos c, ← hr σ, c]
      exact hg
    · rw [if_neg c, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one])
  have hu' : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h = if ρ = τ then g else 1 := fun ρ => by
    have := hu ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩
    simp only [hsurj] at this
    exact this
  refine ⟨h, ⟨hh, (hu' τ).trans (if_pos rfl), fun ρ c => (hu' ρ).trans (if_neg c)⟩, fun h' hh' => ?_⟩
  have e : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h' = Formalism.L2.Pj.archM V (θ ρ) h := fun ρ => by
    rw [hu']
    by_cases c : ρ = τ
    · rw [if_pos c, c]; exact hh'.2.1
    · rw [if_neg c]; exact hh'.2.2 ρ c
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ (h1 _ fun σ => ?_) (mul_mem hh'.1 (inv_mem hh)))
  rw [archM_mul, e, ← archM_mul, mul_inv_cancel, archM_one]

end GlobalTheory.PointAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSplitIdemIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

end GlobalTheory.WeilTieCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms

theorem denom_norm_natCast_le_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | (apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one ..)

theorem denom_global {F : Type} [Field F] [NumberField F] (H : HeightOneSpectrum (𝓞 F) → NNReal)
    (hH : ∀ v, 1 ≤ H v) (hf : (Function.mulSupport H).Finite) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ v, ∀ y : v.adicCompletion F, ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | (apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator ..)

theorem denom_exists_int {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ r : 𝓞 E, (r : E) = k * e := by
  first
  | exact @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | (apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers ..)


open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Formalism.L2.Pj in
theorem denomBound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    DenomBound θ V := by
  first
  | exact @_root_.GlobalTheory.AdeleDenominators.denomBound
  | exact _root_.GlobalTheory.AdeleDenominators.denomBound
  | (apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleDenominators.denomBound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleDenominators.denomBound ..)

end GlobalTheory.SmoothForms
end

