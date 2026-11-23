module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStableOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnlFull
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTraceOfMatching
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Mathlib

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt

theorem killsAll_holds : KillsAll := GlobalTheory.T.shintani_lift_kills_product_of_cusp_forms

theorem liftHc_holds : LiftHc := GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted

theorem killsHc_holds : KillsHc := GlobalTheory.T.twistedHarishChandra_isotypic_part

theorem jAppend_holds : JAppend := fun F _ _ θ => (GlobalTheory.T.harishChandraProductCuspidalGL_list_properties F θ).2.1

theorem normEx_holds : NormEx := by
  intro F F' _ _ _ _ s hs t δ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Fintype F := Fintype.ofFinite F
  refine GlobalTheory.T.every_element_is_norm F F' s (fun τ => ?_) t δ
  have e : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F' := by
    ext z; rw [hs z, Nat.card_eq_fintype_card]; rfl
  obtain ⟨⟨i, _⟩, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 τ
  exact ⟨(i : ℤ), by rw [e]; simpa using hi⟩

theorem frobL_holds : FrobL := frobL frobTwo resCl parCons

theorem lblIso_holds : LblIso := lblIso (jdIso cuspIso)

theorem leTop_holds : LeTop := leTop liftOk liftBlocks (leRank liftOk)

theorem baseQ_holds : BaseQ := baseQ cardRes

theorem jdChar_holds : JDChar := jdChar hcChar

theorem typeOfLbl_holds : TypeOfLbl := typeOfLbl meetsIff frobL_holds jdEq

theorem lblOf_holds : LblOf :=
  lblOf meetsIff frobL_holds jdEq cuspChar tensTr cuspIrr tensFix (subqMap finSec UpperTheory.Gal.TypesAndIwahori.paraFactor) suppStd

theorem killsTrue_holds : KillsOn fun _ => True :=
  killsTrue (killsNil killsAll_holds) liftHc_holds killsHc_holds normEx_holds liftOk jdEq jdChar_holds liftDet

theorem lblOn_of (hT : FinTrace) (P₀ : Lbl → Prop) (h₁ : ∀ a l, P₀ a → P₀ (a.lift l)) (h₂ : KillsOn P₀) : LblOn P₀ :=
  lblOn (baseCase resEmbCompat lblIso_holds) liftsFix placeEx resEmbEx unrOfIne P₀ h₁
    (stepSplit stableOf resEmbCompat lblIso_holds P₀)
    (stepInert hT stableOf resEmbCompat (resDeg cardRes) liftOk jdEq P₀ h₂)

theorem lblTrue_of (hT : FinTrace) : LblOn fun _ => True := lblOn_of hT _ (fun _ _ _ => trivial) killsTrue_holds

theorem suppAny_of (hT : FinTrace) : SuppAny :=
  suppAny (lblOn_of hT _ (fun a l h => by simp only [Lbl.lift, h, List.map_nil]) (killsNil killsAll_holds)) lblOf_holds
    typeOfLbl_holds UpperTheory.Gal.TypesAndIwahori.suppOfType_holds UpperTheory.Gal.TypesAndIwahori.blockCount tameChars leTop_holds polTop polBot resEmbEx
    (unifTower liftsFix placeEx unrOfIne) baseQ_holds cardRes artRead (cuspIne tameRead typeChar nameOf baseQ_holds) suppIne

theorem lblMixed_holds : LblMixed :=
  lblMixed lblOf_holds group1 cuspFrob (inertOf typeChar baseQ_holds) unlFull
    (jdPair jAppend_holds hcOne (hcPair hcChar hcOne) (detPair frobL_holds jdEq) jdChar_holds) jdChar_holds
    (lblFull meetsIff frobL_holds jdEq tensTr avgMap (indMap UpperTheory.Gal.TypesAndIwahori.indSupp UpperTheory.Gal.TypesAndIwahori.paraFactor) tensInc)

theorem mixType_of (hT : FinTrace) : MixType :=
  mixType (lblTrue_of hT) lblMixed_holds sepOf leTop_holds polTop typeOfLbl_holds resEmbEx baseQ_holds cardRes

theorem suppAny_holds (h : GlobalTheory.DZA.InflMatching) : SuppAny := suppAny_of (L.finTrace_of_matching h)

theorem mixType_holds (h : GlobalTheory.DZA.InflMatching) : MixType := mixType_of (L.finTrace_of_matching h)

theorem suppBC_holds (h : GlobalTheory.DZA.InflMatching) : SuppBC := suppBC_of_mix (suppAny_holds h) (mixUnlinked (mixType_holds h))

end UpperTheory.Gal.InertialTypesAlt
