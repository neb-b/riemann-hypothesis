module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0011
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcRegAlgPolarizedPair
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcPolar

theorem exists_sign_twist {K : Type} [Field K] [NumberField K] [IsCMField K] (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) (b : ℤ) :
    ∃ k : ℕ, ∀ v, (χ * quadChar K ^ k).locInf v (-1) = (-1) ^ b := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hval : ∀ (k : ℕ) v, (χ * quadChar K ^ k).locInf v (-1) = χ.locInf v₀ (-1) * (-1) ^ k := fun k v => by
    change χ.locInf v (-1) * (quadChar K ^ k).locInf v (-1) = _
    rw [locInf_pow, quadChar_locInf, h v v₀]
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  simp only [hval, Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb' <;> rw [e, hb'.neg_one_zpow]
  · exact ⟨0, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨0, fun _ => by simp⟩

end GlobalTheory.BcPolar
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsBis
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.SatAeProof

theorem main : AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat v B := by
  intro hA F _ _ _ a π
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  exact sat_ae_of_smooth GlobalTheory.RealGal.SatLocProof.main π.finPart hsm fun w =>
    let ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.RealGal.locCompR_of_admissibleReal hA F a π w
    ⟨σ, hiso σ hσ⟩

end GlobalTheory.RealGal.SatAeProof
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsMore
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CMPatch

theorem res_injective (F Ω E : Type) [Field F] [Field Ω] [Algebra F Ω] [Field E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] : Function.Injective (res F Ω E) := by
  intro a b h
  ext x
  have := congrArg (fun σ : G F Ω => σ x) h
  simpa using this

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (S : Set (QCM F Ω)), S.Infinite → ∀ r : ∀ Q : ↥S, G ↥Q.1.K Ω →* GL (Fin a) (Qbar l), (∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q)) → ∃ ρ : G F Ω →* GL (Fin a) (Qbar l), Continuous ρ ∧ IsSSRep ρ ∧ ∀ᶠ Q : ↥S in Filter.cofinite, IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) ∧ RepIso (r Q) (ρ.comp (res F Ω ↥Q.1.K)) := by
  intro F Ω _ _ _ _ _ _ l _ ι a π S hS r hr
  classical
  haveI : Infinite ↥S := hS.to_subtype
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := _root_.GlobalTheory.RealGal.SignChar.main F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    haveI : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact _root_.GlobalTheory.RealGal.trace_conj_of_attRes F Ω ↥Q.1.K Q.1.two l ι a π (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact _root_.GlobalTheory.RealGalCompat.trace_eq F Ω Q.1 Q'.1 l ι a π (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine ⟨hres, GlobalTheory.T.semisimple_iso_of_trace_eq (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_⟩
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

end GlobalTheory.CMPatch
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfiniteQuadraticFieldsSplitInertia
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_quadratic_fields_split_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : HeightOneSpectrum (𝓞 F) → Prop), (∀ᶠ u in Filter.cofinite, T u) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range}.Infinite := by
  first | exact @GlobalTheory.RealGal.exists_infinite_qcm_split_ram | exact GlobalTheory.RealGal.exists_infinite_qcm_split_ram | (intros; apply GlobalTheory.RealGal.exists_infinite_qcm_split_ram <;> assumption)
end

