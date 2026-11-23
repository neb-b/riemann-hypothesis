module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h)
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.total_reciprocity :
    HypothesesH → RecTot := by
  intro H E Ω _ _ _ _ _ _ n c a d hn P w ρ σ _ hP hS τ e A h rc hrc
  have L := H.litN.loc
  have h1 := GlobalTheory.FormDict.RecTLaws.locProd_eq hrc hn σ τ e
  have h2 : ∀ i, rc (cls (ParLaws.toRep (σ i))) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cls (ParLaws.toRep (ρ i)))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i => by
    have hd : ∑ _ : Fin (d i), a i = d i * a i := by simp
    exact GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ hrc (_root_.GlobalTheory.GenericUnitaryBridge.genericUnitaryDualGL_of_hypotheses L.unit L.sq L.gen L.multi L.cos) L.cos (a i) (d i) _ hd (ρ i) (σ i)
      (hS i).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E (a i) (P i) w (ρ i) (hP i))
      (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd (ρ i) (σ i) (hS i).2.2)
  rw [rec_algNorm hrc]
  change _ = (rc (cls (ParLaws.toRep τ))).lpTw _
  rw [h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.LocGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.twist_local_components_compatible :
    TwistLoc := by
  intro E _ _ _ a P t w ρ hρ
  refine ⟨_, hρ.twist (GlobalTheory.HeckeGal.Model.absPow E t), ?_⟩
  refine (GlobalTheory.LocGL.IrrGL.tw_of ρ.ρ ρ.smooth ρ.irred _
    (isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E t) w)).symm.trans ?_
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E t) w
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω), (∀ v, (s.w v).under (𝓞 (Lp L)) = v) ∧ ∀ w : Plc L, Dec (F := Lp L) (s.A (w.under (𝓞 (Lp L)))) ≤ (W.resP L Ω).range → IsSplitAt w := by
  intro l _ L Ω _ _ _ _ _ _ s
  obtain ⟨_, _, _, _, w, A, hAw, hAv, _⟩ := s
  refine ⟨fun v => ?_, fun w' hw' => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (hAv _) hw' w' rfl⟩
  have h1 := hAw v
  have h2 := hAv v
  apply HeightOneSpectrum.ext
  ext x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← h1 (algebraMap _ _ x), ← h2 x]
  have hx : ((algebraMap (𝓞 (Lp L)) (𝓞 L) x : 𝓞 L) : L) = algebraMap (Lp L) L (x : Lp L) := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply]
end

