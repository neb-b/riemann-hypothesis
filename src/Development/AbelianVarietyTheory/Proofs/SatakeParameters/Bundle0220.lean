module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjectiveOfFg
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.ClusteredLetterwiseBoxes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensionalStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveDictOfCm
section
namespace GlobalTheory.CurveDictionary

theorem curveDict_of_cm : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.Rep.CurveDict := fun hGood _ hTor =>
  curveDict_of_inputs hGood hTor _root_.GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg _root_.GlobalTheory.CoefWfUnram.coefWf_phW _root_.GlobalTheory.BeCoefficients.beCoef _root_.GlobalTheory.CobExactProof.cobExact _root_.GlobalTheory.CobSimeqProof.cobSimeq
    _root_.GlobalTheory.ShortModelTie.phTie _root_.GlobalTheory.ShortModelTheta.thetaTie_holds _root_.GlobalTheory.InverseSeriesIntegral.v_integral

end GlobalTheory.CurveDictionary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.TwistLetters


set_option maxHeartbeats 4000000 in
theorem wdSpace_twist_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a s m _ _ _ hs hm ht
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v = χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  clear_value χ
  have hl := dmul_mulD_left P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hr := dmul_mulD_right P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt
  have hL1 := @GlobalTheory.T.exists_balancedBilinear_tensorProduct_map _ _ _ _ _ _ _ _ _ _ _ _ _ (mulD P (Bw.repE L s)) (mulD P (Bw.repE L m)) (mulD P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) ℂ _ (algC ι L) (urC ι) _ hl hr
  obtain ⟨Φ, hΦ'⟩ : ∃ Φ : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), ∀ x y, Φ (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) = wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) := hL1
  have hsurj : Function.Surjective Φ := by
    have h2b := _root_.GlobalTheory.Pst.UnitLetter.exists_unit_Dpst P AI hT (Bw.repE L m) χ hχm hm
    obtain ⟨y, hy, y', hyy'⟩ := h2b
    let y₀ : ↥(Dpst P (Bw.repE L m)) := ⟨y, hy⟩
    have h2 := _root_.GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt y₀ y' hyy'
    have hspan : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) = ⊤ := span_wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))
    have hle : Submodule.span ℂ (Set.range (wdMk P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))) ≤ LinearMap.range Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := h2 z
      exact ⟨_, (hΦ' x y₀).trans (by rw [hx])⟩
    intro z
    exact LinearMap.mem_range.mp (hle (Submodule.eq_top_iff'.mp hspan z))
  have hdim : Module.finrank ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m)) =
      Module.finrank ℂ (WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))) := by
    rw [Module.finrank_tensorProduct, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hs,
      GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ hm, GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ L _ _ ht]
    simp
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have key : ∀ {f g : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) →ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)))},
      (∀ x y, f (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y) =
        g (wdMk P ι (Bw.repE L s) x ⊗ₜ wdMk P ι (Bw.repE L m) y)) → f = g := by
    intro f g H
    apply TensorProduct.ext
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L s))
    intro x
    apply LinearMap.ext_on_range (span_wdMk P ι (Bw.repE L m))
    intro y
    exact H x y
  have hW : ∀ σ x y, weilD Bw h P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ((dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) x y) =
      (dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt) (weilD Bw h P (Bw.repE L s) σ x) (weilD Bw h P (Bw.repE L m) σ y) := by
    intro σ x y
    simp only [weilD_apply, Module.End.mul_apply, _root_.GlobalTheory.Pst.TwistLetters.phiU_zpow_dmul P (Bw.repE L s) (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (Bw.repE L m) χ hχm hχt, actD_dmul]
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun σ x => ?_, fun x => ?_⟩
  · have e : Φ ∘ₗ TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) =
        wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, wdRho_mk, hΦ', hW]
    exact LinearMap.congr_fun e x
  · have e : Φ ∘ₗ ((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) +
        (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s))) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) ∘ₗ Φ := by
      apply key
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        wdN_mk, map_add, hΦ', monD_dmul, wdMk_add]
    exact LinearMap.congr_fun e x

end GlobalTheory.Pst.TwistLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
section
noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (π : Representation ℂ G V) (w : V) : Subgroup G where
  carrier := {g | π g w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_eigen_of_sum {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Representation ℂ G V) (θ : G →* ℂˣ) (H : Subgroup G) [H.FiniteIndex] (hHθ : H ≤ θ.ker)
    {ι : Type} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, ∀ h ∈ H, π h (u i) = u i)
    (T : ι → V →ₗ[ℂ] M) (f : M) (hf0 : f ≠ 0)
    (hf : ∀ g, ∑ i ∈ s, T i (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, π g w = ((θ g : ℂˣ) : ℂ) • w := by
  classical
  haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let F : V → G → V := fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w
  have hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x) := by
    intro w g x
    simp only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]
    congr 1
    have : ((θ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y := by
    intro i hi x y hxy
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h := ⟨x⁻¹ * y, hm, by group⟩
    have hθh : θ h = 1 := hHθ hh
    simp only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]
  let e : V → V := fun w => ∑ q : G ⧸ H, F w q.out
  have heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i) := by
    intro i hi g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, hFg, ← Finset.smul_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    apply hFH i hi
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum]
    rw [Finset.sum_comm]
    have : ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f := by
      intro q
      simp only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  by_contra hne
  push_neg at hne
  have hz : ∀ i ∈ s, e (u i) = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨g, hg⟩ := hne _ h0
    exact hg (heig i hi g)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])] at htot
  have hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)

end Algebra

section Topology

theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  open scoped Pointwise in
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  intro L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt
  classical
  have hmem := _root_.GlobalTheory.SpanLoc.main L n a S hS s σ hσ c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨φ, hφ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hφ i)
  let m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map c.toRingHom
  have hm : Continuous m := Units.continuous_map (continuous_id.matrix_map hc)
  let π : Representation ℂ K σ.V := σ.ρ.comp (m.comp K.subtype)
  have hπ : ∀ g : K, π g = σ.ρ (m g) := fun g => rfl
  have hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f := by
    rintro ⟨g, hg⟩
    obtain ⟨κ, hκ, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have : ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i) := by
      intro i _
      rw [hπ, ← hu i]
      exact i.2.2 κ hκ (u i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]
    rw [← hsum]
    rfl
  let H : Subgroup K := θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)
  have hHo : IsOpen (H : Set K) := by
    rw [Subgroup.coe_inf]
    refine hθ.inter ?_
    simp only [Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)
  have hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :
      Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.SplitFlip.isCompact_KO
  haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_sum π θ H inf_le_left φ.support u
    (fun i hi h hh => by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)
      exact (Subgroup.mem_iInf.1 this hi))
    (fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF
  exact ⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩

end GlobalTheory.LocVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTriv
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField
open scoped Matrix

namespace GlobalTheory.RepEqAt

section General

open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_triv (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) {n : ℕ} (hn : 0 < n)
    (Λ : GenLat E N) (hU : Λ.Unimod) :
    ∃ γ : Matrix (Fin N) (Fin N) E, IsUnitaryM γ ∧ ∃ k : ℕ, Nat.Coprime k n ∧
      (∀ v ∈ Λ.La, k • (γ *ᵥ v) ∈ Formalism.L2.Pj.stdLat E N) ∧
      ∀ x ∈ Formalism.L2.Pj.stdLat E N, ∃ v ∈ Λ.La, γ *ᵥ v = k • x := by
  have hsub : ∀ a b : 𝓞 E ⧸ Ideal.span {((1 : ℕ) : 𝓞 E)}, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a - b, by simp⟩)
  have hiso : IsIsomMod Λ 1 0 := by
    refine ⟨fun y => ⟨0, funext fun j => hsub _ _⟩, fun v => ⟨fun _ => ⟨v, v.2, by simp⟩, fun _ => rfl⟩,
      fun v w x y _ _ => ?_⟩
    obtain ⟨a, ha⟩ := (hU w).1 w.2 v v.2
    refine ⟨a - ∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j), ?_⟩
    have e1 : ∑ j, (v : Fin N → E) j * IsCMField.complexConj E ((w : Fin N → E) j) = (a : E) := by
      refine Eq.trans ?_ ha.symm
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) =
        ((∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j) : 𝓞 E) : E) := by
      change _ = algebraMap (𝓞 E) E _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
    rw [e1, e2, Nat.cast_one, one_mul]
    exact (map_sub (algebraMap (𝓞 E) E) _ _).symm
  obtain ⟨γ, hγ, ⟨k, hk, h1, h2⟩, -⟩ :=
    GlobalTheory.RepTrivial.repExists E N hur 1 n one_pos hn Λ 0 hU hiso
  rw [GlobalTheory.GenusLatCompare.span_smul_le_iff] at h1 h2
  exact ⟨γ, hγ, k, hk, fun v hv => h1 _ ⟨v, hv, rfl⟩, fun x hx => h2 x hx⟩

end General

theorem repExS (D : D7) : GL3Theta.repExS D := by
  letI := D.host.cmStar
  intro n hn N L L₀
  have hur := Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  have hst : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hU : ∀ M : SDLat D.host.E N, (⟨M.1⟩ : Formalism.L2.Pj.GenLat D.host.E N).Unimod := fun M v => by
    refine (M.2.2.2 v).trans (forall₂_congr fun w _ => ?_)
    have e : ∀ x y : Fin N → D.host.E, IsCMField.complexConj D.host.E (stdH D.host.E N x y) =
        stdH D.host.E N y x := fun x y => by
      rw [← hst]
      simp [stdH, mul_comm]
    have c : ∀ x y : Fin N → D.host.E, stdH D.host.E N x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range →
        stdH D.host.E N y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      rintro x y ⟨a, ha⟩
      refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E a, ?_⟩
      rw [← e, ← ha]
      exact IsCMField.coe_ringOfIntegersComplexConj D.host.E a
    exact ⟨c w v, c v w⟩
  have hun : ∀ γ : Matrix (Fin N) (Fin N) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ →
      γ ∈ Matrix.unitaryGroup (Fin N) D.host.E := fun γ h => Matrix.mem_unitaryGroup_iff'.2 h
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := exists_triv hur hn _ (hU L)
  obtain ⟨δ, hδ, l, hl, h3, h4⟩ := exists_triv hur hn _ (hU L₀)
  have hδ1 : star δ * δ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun δ hδ)
  have hγ1 : star γ * γ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun γ hγ)
  have hinv : ∀ v, star δ *ᵥ (δ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hδ1, Matrix.one_mulVec]
  refine ⟨⟨star δ * γ, mul_mem (Unitary.star_mem (hun δ hδ)) (hun γ hγ)⟩, k * l,
    Nat.Coprime.mul_left hk hl, ?_, fun x hx => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, e⟩ := h4 _ (h1 v hv)
    have : ((k * l : ℕ) : D.host.E) • ((star δ * γ) *ᵥ v) = u := by
      rw [← hinv u, e, Nat.cast_smul_eq_nsmul, ← Matrix.mulVec_mulVec, smul_smul, mul_comm l k,
        Matrix.mulVec_smul]
    exact this ▸ hu
  · obtain ⟨u, hu, e⟩ := h2 _ (h3 x hx)
    refine ⟨u, hu, ?_⟩
    change (star δ * γ) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, e, smul_smul, Matrix.mulVec_smul, hinv, Nat.cast_smul_eq_nsmul]

end GlobalTheory.RepEqAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJointBCD
section
open NumberField IsDedekindDomain Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.RecS.fam_jointBCD : ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), GlobalTheory.HTW.LJ.ConclusionJa (Fm.D x j) → (∀ i, TwistedPlaces.TwLoc (Fm.D x j) i → TwistedPlaces.InertK (Fm.D x j) ((Fm.D x j).nd.l i) → ∀ π ∈ (Fm.D x j).nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π) → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro eps Fm R a b
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_joints Fm R.C₂ a b
  exact ⟨x0, fun x hx h1 j HW X hJ hP =>
    GlobalTheory.Survey.ClusteredLetterwiseBoxes.frozenBCD_of _ HW X R (h x hx h1 j HW hJ).1 (h x hx h1 j HW hJ).2 hP⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLocInj

open TensorProduct

theorem loc_injective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v} y →
    Dv.loc x = Dv.loc y → x = y := by
  intro L _ _ _ n v w Dv x y hx hy h
  unfold InertDatum.loc at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  apply Subtype.ext; apply Units.ext
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  obtain rfl | hu := eq_or_ne u v
  · ext i j
    have h2 := congrArg (fun g : GL (Fin n) (w.adicCompletion L) => g.val i j) h1
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.GeneralLinearGroup.map] at h2
    simp only [Matrix.map_apply]
    exact Dv.e.injective h2
  · rw [hx u (by simpa using hu), hy u (by simpa using hu)]

end GlobalTheory.InertLocInj
end
end

