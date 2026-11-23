module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLocLaurent
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open ReciprocityTheory.ChartRestriction.G.Geo

def FlagPair.fullFlag' (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
    [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ}
    {V : Type*} [AddCommGroup V] [Module Ω V] {E E' : ChartBundle O (mseg x) N V} (φ : FlagPair O x E E') :
    FullFlag O x E' where
  Vs := φ.Vs
  mono := φ.mono
  dim := φ.dim
  top := φ.top
  deg := φ.deg'
  gen := φ.gen'
  gen_mem := φ.gen'_mem
  frame := φ.frame'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FullFlagVerticalSymmetric.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (fl₁ fl₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B)
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (n : ℕ) (Y : Fin n → K → ℤ) (R : MvPolynomial (Fin n) ℤ) (b : K → ℤ) (f g : MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₁.deg Y)
                                  (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₂.deg Y)
            (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def VerticalDivisorFibreVariety.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support,
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreSemilocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_quot_span_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R') (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R' (R' ⧸ Ideal.span {ψ r}) := by
  let _ : Algebra R R' := ψ.toRingHom.toAlgebra
  let e : (R ⧸ Ideal.span {r}) ≃ₐ[R] R' ⧸ Ideal.span {ψ r} :=
    Ideal.quotientEquivAlg _ _ (AlgEquiv.ofRingEquiv (f := ψ) fun _ => rfl)
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  rw [e.toLinearEquiv.length_eq, Module.length_eq_of_surjective ψ.surjective]


set_option maxHeartbeats 2000000 in
theorem BlowUpFibreSemilocal.proof (ha : HomLocRingLocal.Statement.{u})
    (hb : DivCycleHomLoc.Statement.{u}) (hiso : BlowUpLocRingIso.Statement.{u})
    (hfin : BlowUpOverLocFinite.Statement.{u}) (hmax : BlowUpOverLocMax.Statement.{u}) :
    BlowUpFibreSemilocal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel g hg hgW hz
  have := hP.multiProj.isPrime
  obtain ⟨hfinite, hrank⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  obtain ⟨e, he⟩ := hmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hbl : IsModelOver (blowUpOf P u) n := BlowUpModel.full O K ι J P n hP N u hu hu'
  refine ⟨blowUpOverLoc P W u, inferInstance, inferInstance, inferInstance, hfinite,
    Subring.inclusion_injective _, hrank, e, fun 𝔫 => ⟨?_, (he 𝔫).2⟩⟩
  obtain ⟨h, hloc⟩ := (he 𝔫).1
  generalize e 𝔫 = Q at h hloc ⊢
  obtain ⟨Q, hQmin, hQrel, hQW⟩ := Q
  dsimp only at h hloc ⊢
  have hblQ : blowUpOf P u ≤ Q := le_trans le_sup_left hQmin.1.2
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hgl : IsMultiHomog (liftForm (J := J) g) (liftMDeg c) := isMultiHomog_liftForm hg
  have hgQ : liftForm (J := J) g ∉ Q := fun hm => hgW (by rw [← hQW]; exact hm)
  have hxbl : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm x)) /
      algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
      homLocRing (blowUpOf P u) Q :=
    Subring.subset_closure ⟨liftMDeg c, _, _, hxl, hgl, hgQ, rfl⟩
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u Q hblQ

  have hlen : Module.length (homLocRing (blowUpOf P u) Q)
      (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) =
        ((divCycle (blowUpOf P u) (liftForm x) Q).toNat : ℕ∞) := by
    have hinj := IsFractionRing.injective (MRing (extIdx ι J) O ⧸ blowUpOf P u)
      (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
    have hne : ∀ y : MRing (extIdx ι J) O, y ∉ blowUpOf P u →
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ y) ≠ 0 := by
      intro y hy
      rw [Ne, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hz0 : (⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q) ≠ 0 := fun h0 =>
      div_ne_zero (hne _ hxbl) (hne _ fun hm => hgQ (hblQ hm)) (congrArg Subtype.val h0)
    have hQp : Q.IsPrime := hQmin.1.1
    have hmult := hb O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl
      hxbl Q hQmin hQrel (liftForm g) hgl hgQ hz'
    have hloc' := ha O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c)
      (liftForm x) hxl hxbl Q hQmin hQrel
    have hn : IsNoetherianRing (homLocRing (blowUpOf P u) Q) := hloc'.2.1
    have hd : ringKrullDim (homLocRing (blowUpOf P u) Q) = 1 := hloc'.2.2
    have hdivQ : divCycle (blowUpOf P u) (liftForm x) Q =
        ((multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Q).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hQmin, hQrel⟩]
    have : Ring.KrullDimLE 1 (homLocRing (blowUpOf P u) Q) := by
      rw [Ring.krullDimLE_iff, hd]
      rfl
    have hfinl : Module.length (homLocRing (blowUpOf P u) Q)
        (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr
        (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hz0))
    rw [hdivQ, Int.toNat_natCast, hmult, ENat.natCast_toNat hfinl]

  let _ := (Subring.inclusion h).toAlgebra
  have := 𝔫.2.isPrime
  have := hloc
  let ψ₁ : Localization.AtPrime 𝔫.1 ≃ₐ[blowUpOverLoc P W u] blowUpLocRing P u Q :=
    IsLocalization.algEquiv 𝔫.1.primeCompl _ _
  let ψ : Localization.AtPrime 𝔫.1 ≃+* homLocRing (blowUpOf P u) Q := ψ₁.toRingEquiv.trans φ.symm
  have hψ : ψ (algebraMap (blowUpOverLoc P W u) (Localization.AtPrime 𝔫.1)
      (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩)) = ⟨_, hz'⟩ := by
    apply φ.injective
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    apply Subtype.ext
    rw [hφ (liftMDeg c) _ _ hxl hgl hgQ, blowUpEval_liftForm, blowUpEval_liftForm]
    rfl
  rw [length_quot_span_ringEquiv ψ, hψ]
  exact hlen

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial HomLocLaurent

noncomputable section

universe u

set_option linter.style.haveILetI false

section Mult

theorem length_quotient_of_surjective {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    (h : Function.Surjective (algebraMap S C)) (I : Ideal C) :
    Module.length S (C ⧸ I) = Module.length C (C ⧸ I) :=
  Module.length_eq_of_surjective h

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
  {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]

theorem multAt_eq_length_locC (hPW : P ≤ W) (x : MRing ι R) :
    multAt (P ⊔ Ideal.span {x}) W =
      Module.length (locC hPW) (locC hPW ⧸ Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  set J := P ⊔ Ideal.span {x}
  set I : Ideal (locC hPW) := Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}
  set θ : MRing ι R →+* locC hPW := (algQC hPW).comp (Ideal.Quotient.mk P) with hθ
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {s : MRing ι R}, s ∉ W → IsUnit (θ s) := fun hs =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h)
  obtain ⟨θW, hθWdef⟩ : ∃ φ : Localization.AtPrime W →+* locC hPW,
      φ = IsLocalization.lift (M := W.primeCompl) (g := θ) fun s => hunit s.2 := ⟨_, rfl⟩
  have hθW : ∀ f, θW (algebraMap (MRing ι R) (Localization.AtPrime W) f) = θ f := fun f => by
    rw [hθWdef]
    exact IsLocalization.lift_eq _ _

  have hval : ∀ (a s : MRing ι R) (hs : s ∈ W.primeCompl),
      (θW (IsLocalization.mk' (Localization.AtPrime W) a ⟨s, hs⟩) : FractionRing (MRing ι R ⧸ P)) *
        fr P s = fr P a := by
    intro a s hs
    have := congrArg θW (IsLocalization.mk'_spec (Localization.AtPrime W) a ⟨s, hs⟩)
    rw [RingHom.map_mul, hθW, hθW] at this
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective θW := by
    rintro ⟨c, a', s', hs', rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsW : s ∉ W := fun h => hs' (Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hsW⟩ : W.primeCompl), Subtype.ext ?_⟩
    have h := hval a s hsW
    change _ = fr P a * (fr P s)⁻¹
    rw [← h, mul_assoc, mul_inv_cancel₀ (hne hsW), mul_one]
  letI : Algebra (Localization.AtPrime W) (locC hPW) := θW.toAlgebra
  let f : Localization.AtPrime W →ₐ[Localization.AtPrime W] (locC hPW ⧸ I) :=
    Algebra.ofId (Localization.AtPrime W) (locC hPW ⧸ I)
  have hf : ∀ y, f y = Ideal.Quotient.mk I (θW y) := fun y => rfl
  have hfs : Function.Surjective f := fun q => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := hsurj c
    exact ⟨y, hf y⟩
  have hker : RingHom.ker f = J.map (algebraMap (MRing ι R) (Localization.AtPrime W)) := by
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
      obtain ⟨⟨c, b', t', ht', hc⟩, hcy⟩ := hy
      obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
      have htW : t ∉ W := fun h => ht' (Ideal.mem_map_of_mem _ h)
      have h1 := hval a s hs
      rw [← hcy] at h1
      change c * fr P x * fr P s = fr P a at h1
      rw [hc] at h1
      change fr P b * (fr P t)⁻¹ * fr P x * fr P s = fr P a at h1
      have hat : a * t - b * x * s ∈ P := by
        have h2 : fr P a * fr P t = fr P b * fr P x * fr P s := by
          rw [← h1]
          calc _ = fr P b * fr P x * fr P s * ((fr P t)⁻¹ * fr P t) := by ring
            _ = _ := by rw [inv_mul_cancel₀ (hne htW), mul_one]
        rw [← fr_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, h2, sub_self]
      have hatJ : a * t ∈ J := by
        have : a * t = (a * t - b * x * s) + (b * s) * x := by ring
        rw [this]
        exact J.add_mem (Ideal.mem_sup_left hat)
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      have hst : s * t ∈ W.primeCompl := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs htW
      have heq : IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hs⟩ : W.primeCompl) *
          algebraMap (MRing ι R) (Localization.AtPrime W) (s * t) =
            algebraMap (MRing ι R) (Localization.AtPrime W) (a * t) := by
        rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, map_mul]
      have hu : IsUnit (algebraMap (MRing ι R) (Localization.AtPrime W) (s * t)) :=
        IsLocalization.map_units (Localization.AtPrime W) (⟨s * t, hst⟩ : W.primeCompl)
      rw [← Ideal.mul_unit_mem_iff_mem _ hu, heq]
      exact Ideal.mem_map_of_mem _ hatJ
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker, hf, hθW, Ideal.Quotient.eq_zero_iff_mem]
      have hJ : J ≤ I.comap θ := by
        refine sup_le (fun p hp => ?_) ?_
        · have h0 : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [Ideal.mem_comap, hθ, RingHom.comp_apply, h0, RingHom.map_zero]
          exact zero_mem _
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span rfl
      exact Ideal.mem_comap.mp (hJ hj)
  have hlen := (Ideal.quotientKerAlgEquivOfSurjective hfs).toLinearEquiv.length_eq
  rw [multAt, length_localizedModule_quotient_eq, ← (Submodule.quotEquivOfEq _ _ hker).length_eq, hlen]
  exact length_quotient_of_surjective hsurj I

end Mult

theorem DivCycleHomLoc.proof (h : HomLocRingLocal.Statement.{u}) : DivCycleHomLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel g hg hgW hz
  haveI := hP.isPrime
  haveI : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_trans le_sup_left hW.1.2
  have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
    (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hx) hW
  haveI : IsLocalRing (homLocRing P W) := (h O K ι P hP c x hx hxP W hW hWrel).1
  choose T hT using hWrel
  rw [← length_quotient_incAC T hPW hT hP.multiHomog hWh, multAt_eq_length_locC hPW x]
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hxz : algQC hPW (Ideal.Quotient.mk P x) =
      incAC hPW ⟨_, hz⟩ * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P x = fr P x / fr P g * fr P g
    rw [div_mul_cancel₀ _ (fr_ne_zero fun h => hgW (hPW h))]
  rw [hxz, Ideal.span_singleton_mul_right_unit hgu]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

