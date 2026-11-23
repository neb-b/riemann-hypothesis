module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.SharpRestriction.GlobalSchurBounds.TuSizeOfRealPlaceSecondLayer
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Formalism.LocalToGlobal.TieTwRecOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AttachedRepConjugateInvariant
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory.RealGal.AttConj

section Gen

variable {F Ω K : Type} [Field F] [Field Ω] [Algebra F Ω] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem inv_apply_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g y) = y := by
  show (g⁻¹ * g) y = y
  rw [inv_mul_cancel]
  rfl

theorem apply_inv_apply (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) : g ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) = y := by
  show (g * g⁻¹) y = y
  rw [mul_inv_cancel]
  rfl

theorem val_le_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y ≤ 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem val_lt_one_smul (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y) < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff',
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω).injective]

theorem exists_of_fixed [CharZero K] [IsAlgClosure K Ω] (z : Ω) (hz : ∀ t : Formalism.ConjugateSelfDual.G K Ω, t z = z) :
    ∃ y : K, algebraMap K Ω y = z := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have h := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K Ω)
  have hz' : z ∈ IntermediateField.fixedField (⊥ : IntermediateField K Ω).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro t _
    exact hz t
  rw [h] at hz'
  exact IntermediateField.mem_bot.1 hz'

theorem exists_ringEquiv (g : Formalism.ConjugateSelfDual.G F Ω)
    (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)) :
    ∃ γ : K ≃+* K, ∀ x, algebraMap K Ω (γ x) = g (algebraMap K Ω x) := by
  choose f hf using h1
  choose f' hf' using h2
  have hinj := (algebraMap K Ω).injective
  let φ : K →+* K :=
    { toFun := f
      map_one' := hinj (by simp [hf])
      map_mul' := fun x y => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun x y => hinj (by simp [hf]) }
  let ψ : K →+* K :=
    { toFun := f'
      map_one' := hinj (by simp [hf'])
      map_mul' := fun x y => hinj (by simp [hf'])
      map_zero' := hinj (by simp [hf'])
      map_add' := fun x y => hinj (by simp [hf']) }
  refine ⟨RingEquiv.ofRingHom φ ψ ?_ ?_, fun x => hf x⟩
  · ext x
    exact hinj (by
      show algebraMap K Ω (f (f' x)) = algebraMap K Ω x
      rw [hf, hf', apply_inv_apply])
  · ext x
    exact hinj (by
      show algebraMap K Ω (f' (f x)) = algebraMap K Ω x
      rw [hf', hf, inv_apply_apply])

variable [NumberField K]

theorem ine_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := K) A) :
    c s ∈ ReciprocityTheory.Gal.Ine (F := K) (g • A) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply]
    exact hs.2 _ hx

theorem frob_conj (g : Formalism.ConjugateSelfDual.G F Ω) (c : Formalism.ConjugateSelfDual.G K Ω →* Formalism.ConjugateSelfDual.G K Ω)
    (hc : ∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹)
    (A : ValuationSubring Ω) (q : ℕ) (s : Formalism.ConjugateSelfDual.G K Ω) (hs : Formalism.ConjugateSelfDual.IsFrob A q s) :
    Formalism.ConjugateSelfDual.IsFrob (g • A) q (c s) := by
  have hcs : ∀ y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun y => DFunLike.congr_fun (hc s) y
  refine ⟨?_, fun x hx => ?_⟩
  · show (res F Ω K (c s)) • (g • A) = g • A
    rw [hc s, mul_smul, mul_smul, inv_smul_smul]
    show g • (s • A) = g • A
    rw [show s • A = A from hs.1]
  · rw [val_le_one_smul] at hx
    rw [val_lt_one_smul, map_sub, hcs, inv_apply_apply, map_pow]
    exact hs.2 _ hx

end Gen

end GlobalTheory.RealGal.AttConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkGl
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.link_gl : ∀ (𝒜 : FamClass)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D)
    (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2), (Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm) ∧ (Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0) := by
  intro 𝒜 hduty tie hU hG
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hCabs : (0 : ℝ) ≤ 2 := by norm_num
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  have hGLm := Formalism.MainNotions.Wire.famGLmin_of_realPlaceSecondLayer (D3 3 𝒜) tie hU hG
  have hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm :=
    ((hGLm.muRank 3 hC0').and
      (Closed.of_class (P := fun Fm _ => TuSize Fm) fun _ _ hc => hc.2.2.1)).imp fun _ _ _ h c => h.1 h.2 c
  have hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0 :=
    hGLm.link8 2 3 hCabs hC0 fun Fm hc => (hduty Fm (d3_a hc)).2.2.2.2.1
  exact ⟨hRk, hGL⟩

end
end

