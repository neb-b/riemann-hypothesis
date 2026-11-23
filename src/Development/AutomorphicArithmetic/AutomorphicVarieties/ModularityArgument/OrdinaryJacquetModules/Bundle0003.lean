module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PartPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ExpTor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.LocalUnitCase.UnitaryIdeleSplitPlaceSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Z.Ord.coreOrd :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → CoreOrd := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP a K _ _ D ψ hU lam hlam y hy
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨Y, F, hY, hF0, hF, hop⟩ :=
    UpperTheory.V.Z.Ord.partPt hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K y hx
  obtain ⟨hD, hch⟩ := UpperTheory.V.Hi.coreEig hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨d, ξ, Y, hY, hD, fun v => ?_⟩
  have hle : H.OrdAt θ ι x.toRingHom lam ξ K c0 ≤ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    unfold HSet.OrdAt
    exact iSup_le fun _ => inf_le_left
  have hC : F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := ⟨hF.1, hle hF.2⟩
  have hne : ∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) ≠ 0 := fun j => by
    obtain ⟨s, hs⟩ := (hA.art_spec v).surj (unif _)
    rw [← hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs]
    exact (map_ne_zero ι).2 ((Units.isUnit _).map y).ne_zero
  obtain ⟨ω, hsm, hPS, hinv, hb⟩ := UpperTheory.V.Z.Ord.ordScal hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp
    Y K c0 le_rfl F hC hF0 v (fun j => ι (y (H.gen θ a K (.inr (v, j))))) fun j => ⟨hne j, hop _⟩
  exact ⟨ω, hPS, hch v ω hsm hinv hb⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SatOfFrob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem sat_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ}
    (h : Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) (h' : Af.FrobEig ι ρ w (Af.algSat n (normV w) B')) : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have hc : (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have e' := Multiset.map_injective (mul_right_injective₀ hc) (a₁ := B.map Units.val) (a₂ := B'.map Units.val)
    (by simpa [Af.algSat, Multiset.map_map] using e)
  exact Multiset.map_injective Units.val_injective e'
end

