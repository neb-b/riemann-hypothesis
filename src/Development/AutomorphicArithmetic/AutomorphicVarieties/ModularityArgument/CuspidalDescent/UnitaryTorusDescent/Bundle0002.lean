module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.ToTL
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PiFamilyProdHomBijectiveCharacterization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.HasHTOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.P

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}

theorem lgAwayT (k : LocGlobT ι r w τ) (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion L) → WD h) (hrc : IsRecT h rc) : WOT ι r (rc (algNorm τ)) := (k A h rc hrc).1 hw

theorem woTypeT {h : IsPlaceOver A w} {y : WD h} (k : WOT ι r y) (χ : Fin n → G L Ω →* ℂˣ)
    (t : IsTypeWD h (fun i => (χ i).comp (Ine (F := L) A).subtype) y) : IsWDOf ι r y :=
  WDT.isWDOf k (typeTor L Ω n w A h χ y t)


end UpperTheory.V.Z.Desc.P
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.TypeEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem te_unr {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {w : Plc L}
    {A : ValuationSubring Ω} {h : IsPlaceOver A w} (x : WD h) (t : ℝ) :
    ((x.lpTw t).mono0 ↔ x.mono0) ∧ ∀ s, (x.lpTw t).charPol (ineIncl h s) = x.charPol (ineIncl h s) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk]
  exact ⟨by simp, fun s => by simp⟩

private theorem te_loc (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (NZ : UpperTheory.NonzeroTypeTheory.NZ) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ)
    {w : Plc L} {A : ValuationSubring Ω} (h : IsPlaceOver A w) (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (χ : Fin n → Dec (F := L) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := L) A))) (hv : ∀ i g, (χ i g : ℂ) ∈ (algebraMap O ℂ).range) :
    ∃ (m : ℕ) (τ : KO (w.adicCompletion L) (Fin n) →* GL (Fin m) O), IsOpen (τ.ker : Set (KO (w.adicCompletion L) (Fin n))) ∧
      ∀ π : SmIrr (GLw n w), (∃ y : Fin m → π.V, y ≠ 0 ∧ ∀ (k : KO (w.adicCompletion L) (Fin n)) i,
        ∑ a, algebraMap O ℂ (τ k i a) • π.ρ k (y a) = y i) ↔
        ∀ rc, IsRec h rc → IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm π)) := by
  obtain ⟨rc, hrc⟩ := Z.Win.exRec P h
  have hsm : ∀ i, IsSmooth (h := h) ((χ i).comp (Subgroup.inclusion (Weil_le_Dec h))) := fun i =>
    (ho i).preimage (f := Subgroup.inclusion (Ine_le_Dec (F := L) A)) (continuous_inclusion (Ine_le_Dec (F := L) A))
  have hT := NZ L Ω A w h rc hrc n χ ho
  rw [← show KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w (n := n) from SphCompletion.KO_completion w n] at hT
  obtain ⟨d, ξ, -, hξ, hπ⟩ := hT
  refine typeLoc O _ _ GlobalTheory.SplitFlip.isCompact_KO _ d ξ hξ (fun π => ?_) fun γ σ σ' f h1 h2 hσ rc' hrc' => ?_
  · rw [hπ π, UpperTheory.NonzeroTypeTheory.Cond]
    have e : IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm π)) ↔ _ :=
      UpperTheory.isTypeWeilDeligne_iff_monodromy_zero_charpoly L Ω n w A h _ _
    have hV : Z.Win.IsRecV h rc := Z.Win.toV hrc
    obtain ⟨a, ha, ε, H⟩ := hV
    rw [algNorm, H.nu_eq, (te_unr _ _).1] at e
    simp only [(te_unr _ _).2] at e
    simp only [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    refine Iff.trans e.symm ⟨fun h0 rc' hrc' => ?_, fun h0 => ?_⟩
    · have h1 : IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm π)) := by
        rw [algNorm, H.nu_eq]
        exact h0
      have hg : UpperTheory.Zero.LLC.Good (algNorm π) := by
        obtain ⟨b, hb, -, hχ⟩ := h1
        obtain ⟨z, hz, hc⟩ := UpperTheory.Zero.LLC.abConv L Ω A w h rc (Z.Desc.P.toTL P hrc) (algNorm π)
          (fun j : Fin n => (χ j).comp (Subgroup.inclusion (Weil_le_Dec h))) fun t => by
            rw [← hb, WD.charPol_mk, hχ t, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
            rfl
        exact ⟨z, hz, fun y hy => Or.inl (hc y hy)⟩
      rw [Z.Win.uniqRec P hrc' hrc _ hg]
      exact h1
    · have := h0 rc hrc
      rwa [algNorm, H.nu_eq] at this
  · have := typeConj P L Ω n w A h rc' hrc' γ.toRingEquiv σ σ' f h1 h2 χ ho (hσ rc' hrc')
    convert this using 2 with i
    ext s
    obtain ⟨z, hz⟩ := hv i (Subgroup.inclusion (Ine_le_Dec A) s)
    change (χ i _ : ℂ) = γ (χ i _ : ℂ)
    rw [← hz, γ.commutes]

private theorem te_root {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Finite (ResidueField O)] {a b : Oˣ}
    (ha : a ^ (Nat.card (ResidueField O) - 1) = 1) (hb : b ^ (Nat.card (ResidueField O) - 1) = 1)
    (h : residue O a = residue O b) : a = b := by
  letI := Fintype.ofFinite (ResidueField O)
  have hu : ((a * b⁻¹ : Oˣ) : O) ^ (Nat.card (ResidueField O) - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ha, hb]; simp
  have hr : residue O (a * b⁻¹ : Oˣ) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, Units.mul_inv, map_one]
  have h1 := geom_sum_mul ((a * b⁻¹ : Oˣ) : O) (Nat.card (ResidueField O) - 1)
  rw [hu, sub_self] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · have h3 := congrArg (residue O) h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, map_zero, nsmul_eq_mul, mul_one] at h3
    rw [Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero] at h3
    simp at h3
  · exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h2))
end

