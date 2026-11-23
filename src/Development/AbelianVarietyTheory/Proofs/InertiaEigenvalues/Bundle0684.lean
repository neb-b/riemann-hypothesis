module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClsEqHomModInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientOfFullRepresentation
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.GTwoTheta

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

theorem zero_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hjm ρ
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]
    rintro (h | h)
    · have := hcl _ h; linarith
    · rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith
  · simpa only [JW, cloudT, lowT, ↓reduceIte] using h0

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]
    rcases hq with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inl hq

theorem neg_one_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (-1 : ℚ) ∉ JW D up j ρ :=
  fun h => ((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem dR_WT (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  have := D.nd.lPrime i
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e :=
    (GlobalTheory.DecompForms.main D i r ρ π).1 hD
  have hsum := (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc
  exact ⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1,
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem twistedRep_no_invariants_purity (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hr : GoodR D.nd i r)
    (hπ : π ∈ D.nd.Z i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) = ⊥ ∧ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) = ⊥ := by
  have := D.nd.lPrime i
  have hjr := D.nd.j_range i
  obtain ⟨hdrW, hdrT⟩ := dR_WT D i r ρ π w hw C hD hc
  obtain ⟨τ₀⟩ := GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le
  obtain ⟨g, ρ', -, -, hW⟩ := hJ i r hr w hw C τ₀
  obtain ⟨-, hW0, -, hT0⟩ := hW ρ π hπ hD 0
  constructor
  · refine _root_.GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_
    refine hW0.trans ?_
    rw [if_neg]
    push_cast
    exact zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _
  · refine _root_.GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_
    refine hT0.trans ?_
    rw [if_neg]
    rw [GlobalTheory.JumpSets.dualS_int]
    push_cast
    exact neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem chi_jump (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hamb : ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0)
    (c : ℕ) (hc1 : 1 ≤ c) (hct : c ≤ D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a ↔ a = (c : ℤ) - 1 := by
  have := D.nd.lPrime i
  have hm := hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a
  refine (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _
    (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_
  refine (Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_
  split_ifs with h <;> simp [h]

theorem tw_jumps (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    (∀ (x y : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a =
        multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r y)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a) ∧
    (∀ (x : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a ≤ 1) ∧
    (∀ x : D.nd.X i,
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ (-1)) := by
  have hjr := D.nd.j_range i
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i r hr w hw C τ
  refine ⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩
  · rw [← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]
  · rw [← locC_rTwO, (hx x a).2.1]
    split_ifs <;> norm_num
  · rw [← locC_rTwO, (hx x (-1)).1]
    push_cast
    exact ((hJc _ hjr.1 hjr.2 ρ').2.1 _).1

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

end GlobalTheory.GTwoTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExtStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  first | exact @GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | exact GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' | (intros; apply GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleUntwistedCharUnramifiedOfResidueRealis
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

theorem admissibleUntwistedCharUnramified_of_residueRealisation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) (hR : ∀ S : TopSit P, S.Real) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P := by
  intro K LL n r emb D Γ hst hgal h1 h2 h3 X _ _ _
  let S : TopSit P :=
    { K := K, LL := LL, n := n, r := r, nz := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hst⟩, emb := emb, D := D, Γ := Γ,
      hyp := ⟨hst, hgal, h1, h2, h3⟩ }
  have hcrys : S.CrysCalc := GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hstd : S.StdAdm := StdAdm.stdAdm S hcrys hcl
  have hL : S.Lem0 (S.Γ.Wchi 1) := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl hstd).2 1 le_rfl S.D.one_le_letterBlockLength
  have hb : S.ResBound (S.Γ.Wchi 1) 1 := (CharBound.resBound_chars S (hR S)).2 hL
  have hu : S.UnrAdm := GlobalTheory.UnramAdm.unramified_admissible S hcrys hcl hstd hL
  exact ChiOne.cls_eq_homModInertia S hL hb hu X

end GlobalTheory.TopSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTrivialH1f_of_decl : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  first | exact @GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | exact GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | (intros; apply GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_rec_compatible : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) s, HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  first | exact @GlobalTheory.LocLanglands.charPol_eq_prod_support | exact GlobalTheory.LocLanglands.charPol_eq_prod_support | (intros; apply GlobalTheory.LocLanglands.charPol_eq_prod_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Formalism.IndefR.Lift

noncomputable section

namespace GlobalTheory.SplitChange

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW ν : (AE D)ˣ →* Circle}
  {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem resEta_zero_of_triv {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hF : ∀ a, ν (idF D a) = 1) :
    ResEta D ν 0 :=
  ⟨h.1, fun η _ a => by rw [hF, pow_zero]⟩

theorem exists_twist_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g x y, IsDetRoot V h x → IsDetRoot W g y →
      om' (h, g) = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std V W χV χW ν ν om ho hν hν
    (resEta_zero_of_triv ho.resS hF) (resEta_zero_of_triv ho.resS hF)
  refine ⟨o, h1, fun h g x y hx hy => ?_⟩
  rw [h2 h g x y hx hy, Circle.coe_mul, Circle.coe_inv, mul_comm]

theorem twist_eq_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {h : GA D V} {g : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V h x) (hy : IsDetRoot W g y) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) f := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  calc
    om' (h, g) f = o (h, g) f :=
      GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W _ _ om' o ho' h1 (h, g) f hf
    _ = _ := by rw [h2 h g x y hx hy, LinearMap.smul_apply]

theorem exists_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV) (hW : MuVal W ν nW) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  refine ⟨o, h1, fun h g => ?_⟩
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [h2 h g x y hx hy, hV.2 h x hx, hW.2 g y hy]

theorem twist_eq (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f := by
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [twist_eq_root ho hν hF ho' hx hy hf, hV.2 h x hx, hW.2 g y hy]

theorem thetaKO_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    thetaKO om' h g f = nW g * (nV h)⁻¹ * thetaKO om h g f := by
  unfold thetaKO
  rw [twist_eq ho hν hF ho' hV hW h g hf, Pi.smul_apply, smul_eq_mul]

theorem chrTh_tup {C : Type*} [CommGroup C] (μ : ℕ → C) (η ν : C) (j : ℕ) :
    chrTh (tup μ ν) η j = ((chrTh μ η j).1 * ν, (chrTh μ η j).2 * ν) := by
  unfold chrTh tup
  rw [mul_right_comm]

theorem change_of_splitting_pair (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW ν : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν)
    (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W χV χW om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  refine ⟨?_, fun nV nW hV hW => ⟨exists_twist ho hν hF hV hW, fun om' ho' h g f hf => twist_eq ho hν hF ho' hV hW h g hf⟩,
    fun om₁ h1 => GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W χV χW om₁ om h1 ho⟩
  obtain ⟨nV, hV, -⟩ := GlobalTheory.Member.exists_muVal D V ν hν hF
  obtain ⟨nW, hW, -⟩ := GlobalTheory.Member.exists_muVal D W ν hν hF
  exact ⟨nV, nW, hV, hW⟩

theorem change_of_splitting (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : ℕ → (AE D)ˣ →* Circle)
    (η ν : (AE D)ˣ →* Circle) (j : ℕ) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ho : IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' ∧
        ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  rw [chrTh_tup]
  exact change_of_splitting_pair D ψ V W _ _ ν om ho hν hF

end GlobalTheory.SplitChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionOverQOrDEqUnramifiedSupSqrt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HubLoc

open Formalism.FrobeniusOrbits

section Gen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem kw_eq_sup_of_gens (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (g₁ g₂ g₃ : H.E)
    (hgen : ∀ M : IntermediateField ℚ_[l] (Om l), J g₁ ∈ M → J g₂ ∈ M → J g₃ ∈ M → ∀ x : H.E, J x ∈ M) :
    Kw.1 = IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) ⊔
      IntermediateField.adjoin ℚ_[l] {J g₃} := by
  set M := IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) with hM
  set N := M ⊔ IntermediateField.adjoin ℚ_[l] {J g₃} with hN
  have hfM : FiniteDimensional ℚ_[l] ↥M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x
  have hfy : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {J g₃}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) _)
  have hfN : FiniteDimensional ℚ_[l] ↥N := IntermediateField.finiteDimensional_sup _ _
  have hcl : IsClosed ((N : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional N.toSubalgebra.toSubmodule
  have h1 : J g₁ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h2 : J g₂ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h3 : J g₃ ∈ N := le_sup_right (a := M) (IntermediateField.mem_adjoin_simple_self _ _)
  apply le_antisymm
  · intro x hx
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨z, rfl⟩
    exact hgen N h1 h2 h3 z
  · refine sup_le ?_ ?_
    · rw [hM, IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      exacts [hE g₁, hE g₂]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hE g₃

theorem sq_aE_image : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
  rw [← map_pow, H.sqq_sq]; simp

theorem sq_bE_image : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
  rw [← map_pow, H.sqd_sq]; simp

theorem kw_eq_sup_sqrt (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (hl : l = H.q ∨ l = H.d) :
    ∃ M : IntermediateField ℚ_[l] (Om l), M ≤ MaximalUnramifiedExtension l ∧ ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
  have hh := H.hyp
  have hq2 : H.q % 4 = 3 := by have := hh.2.2.1; omega
  have hd2 : H.d % 4 = 3 := by have := hh.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := hh.2.2.1; have := hh.2.2.2.1; omega
  have hlS : ¬ l ∣ H.QS := UpperTheory.Small.not_dvd_QS H Fact.out (UpperTheory.Small.not_mem_of_qd H hl)
  have hθ := theta_mem_Kur H J
  rcases hl with rfl | rfl
  · refine ⟨_, ?_, _, sq_aE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.q) (H.sqd)
      (H.sqq) fun M m1 m2 m3 x => image_le H J hlS M m1 m3 m2 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.d hh.2.1 hd2 hqd.symm _ (sq_bE_image H J)
  · refine ⟨_, ?_, _, sq_bE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.d) (H.sqq)
      (H.sqd) fun M m1 m2 m3 x => image_le H J hlS M m1 m2 m3 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.q hh.1 hq2 hqd _ (sq_aE_image H J)

end Gen

theorem kw_eq_unram_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
      ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  intro D i hl w hw
  exact kw_eq_sup_sqrt D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense hl

end GlobalTheory.HubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact _root_.GlobalTheory.TheoremTClosing.main (_root_.GlobalTheory.bhattScholze_coeff hBS) hFon C hC D HW F (_root_.GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt hBK hTD hEC D HW F Cm)
end

