module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
section
noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped NNReal ENNReal TensorProduct

theorem chi_Af (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (Af F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = ∏ᶠ v, ‖evalV F v M.det‖ := by
  classical
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.matrixPair_integral_cofinite F κ M M⁻¹
  obtain ⟨hOc, hOs, hOt⟩ := _root_.GlobalTheory.ModuLR.finiteIntegers_compact_secondCountable_t2 F S
  let _ : MeasurableSpace (OPart F S) := borel _
  have _ : BorelSpace (OPart F S) := ⟨rfl⟩

  let φS : Af F →+* SPart F S := RingHom.pi fun v => (evalV F v.1).toRingHom
  let φO : Af F →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (evalV F v.1).toRingHom
  let ι : OPart F S →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (v.1.adicCompletionIntegers F).toSubring.subtype.comp (Pi.evalRingHom _ v)
  have hι : Function.Injective ι := fun x y h => funext fun v => Subtype.ext (congrFun h v)
  let MS : Matrix κ κ (SPart F S) := φS.mapMatrix M
  let MO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M i j), (hS v.1 v.2 i j).1⟩
  let NO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M⁻¹ i j), (hS v.1 v.2 i j).2⟩
  have hdS : MS.det = φS M.det := (RingHom.map_det φS M).symm
  have huS : IsUnit MS.det := hdS ▸ hM.map φS
  have hMO : ι MO.det = φO M.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hNO : ι NO.det = φO M⁻¹.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hON : MO.det * NO.det = 1 := hι (by
    rw [map_mul, hMO, hNO, ← map_mul, ← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one,
      map_one, map_one])
  have huO : IsUnit MO.det := ⟨⟨_, _, hON, by rw [mul_comm]; exact hON⟩, rfl⟩
  let j : ((κ → SPart F S) × (κ → OPart F S)) →+ (κ → Af F) :=
    ((jS F S).toAddMonoidHom.compLeft κ).comp (zipHom κ (SPart F S) (OPart F S))
  have hj : IsOpenEmbedding j :=
    (IsOpenEmbedding.piMap fun _ => GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart F S).comp (_root_.GlobalTheory.ModuLR.zipHom_isOpenEmbedding κ (SPart F S) (OPart F S))
  have key := _root_.GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding (κ → Af F) ((κ → SPart F S) × (κ → OPart F S)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE MS huS) (mulVecCE MO huO)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      apply RestrictedProduct.ext
      intro v
      change evalV F v ((M *ᵥ j x) i) = evalV F v (jS F S ((MS *ᵥ x.1) i, (MO *ᵥ x.2) i))
      rw [evalV_jS]
      by_cases hv : v ∈ S
      · rw [dite_eq_left hv]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dite_eq_left hv]
        rfl
      · rw [dite_eq_right hv]
        change _ = ι ((MO *ᵥ x.2) i) ⟨v, hv⟩
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dite_eq_right hv]
        rfl)
  rw [key, _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, addEquivAddHaarChar_eq_one_of_compactSpace (mulVecCE MO huO), mul_one,
    _root_.GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE (SPart F S)
      (by show IsArtinianRing (∀ v : S, Fv F v.1); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ huS,
    _root_.GlobalTheory.ModuPiLocal.modu_sPart F S _ huS, hdS,
    finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 := GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers F v (MO.det ⟨v, hvS⟩) (NO.det ⟨v, hvS⟩) (congrFun hON ⟨v, hvS⟩)
    have h2 : (MO.det ⟨v, hvS⟩ : Fv F v) = evalV F v M.det := congrFun hMO ⟨v, hvS⟩
    show ‖evalV F v M.det‖ = 1
    rw [← h2]
    exact h1

theorem chi_AF (F : Type) [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (∏ w, ‖(fstA F M.det) w‖) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  have hd₁ : (M.map (fstA F)).det = fstA F M.det := (RingHom.map_det (fstA F).toRingHom M).symm
  have hd₂ : (M.map (sndA F)).det = sndA F M.det := (RingHom.map_det (sndA F).toRingHom M).symm
  have hu₁ : IsUnit (M.map (fstA F)).det := hd₁ ▸ hM.map (fstA F)
  have hu₂ : IsUnit (M.map (sndA F)).det := hd₂ ▸ hM.map (sndA F)
  let j : ((κ → Ainf F) × (κ → Af F)) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := _root_.GlobalTheory.ModuLR.zipHom_isOpenEmbedding κ (Ainf F) (Af F)
  have key := _root_.GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding (κ → AF F) ((κ → Ainf F) × (κ → Af F)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE (M.map (fstA F)) hu₁) (mulVecCE (M.map (sndA F)) hu₂)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      refine Prod.ext ?_ ?_
      · change fstA F _ = _
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl
      · change sndA F _ = _
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl)
  rw [key, _root_.GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE, NNReal.coe_mul, chi_Af F _ hu₂, hd₂,
    _root_.GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE (Ainf F)
      (by show IsArtinianRing (∀ v : InfinitePlace F, v.Completion); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ hu₁, hd₁,
    GlobalTheory.GaugeProdFormula.modu_infinite F _ (hM.map (fstA F))]

theorem chi_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    addEquivAddHaarChar (lrCE g a) = GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) ^ n *
      GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) ^ m := by
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := _root_.GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E m n g a
  apply NNReal.coe_injective
  rw [hchar, chi_AF F Λ hΛ, hdet, _root_.GlobalTheory.absE_eq_prod_norm_fstA_sndA F E]
  simp [map_mul, map_pow]

theorem smul_map_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (μ : Measure (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) [μ.IsAddHaarMeasure]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    μ = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) ^ n *
      (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) : ℝ≥0∞) ^ m) • μ.map (lrCE g a) := by
  have h := addEquivAddHaarChar_smul_map μ (lrCE g a)
  rw [chi_lr F E m n g a] at h
  calc μ = _ := h.symm
    _ = _ := by rw [ENNReal.smul_def]; push_cast; rfl


open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem modu_lrMul : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  intro D m n μ hμ g a
  have _ : LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have _ : SecondCountableTopology (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have hb : BorelSpace (Fin m → Fin n → AE D) := inferInstance
  have _ : BorelSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    ⟨by first | rfl | exact hb.measurable_eq⟩
  exact smul_map_lr D.host.F D.host.E m n μ g a

end GlobalTheory.ModuLR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.SplitEigen

theorem adjoint_apply_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : Module.End ℂ H) (hA : Commute A (LinearMap.adjoint A)) (v : H) (μ : ℂ) (hv : A v = μ • v) :
    LinearMap.adjoint A v = starRingEnd ℂ μ • v := by
  set B : Module.End ℂ H := A - μ • 1 with hBdef
  have hBadj : LinearMap.adjoint B = LinearMap.adjoint A - starRingEnd ℂ μ • 1 := by
    rw [hBdef, map_sub, map_smulₛₗ]
    congr 2
    exact LinearMap.adjoint_id
  have hBv : B v = 0 := by
    rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self]
  have hc : Commute B (LinearMap.adjoint B) := by
    rw [hBadj, hBdef]
    exact (hA.sub_right ((Commute.one_right A).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have h0 : LinearMap.adjoint B v = 0 := by
    have e : inner ℂ (LinearMap.adjoint B v) (LinearMap.adjoint B v) = (0 : ℂ) := by
      rw [LinearMap.adjoint_inner_left]
      have : B (LinearMap.adjoint B v) = LinearMap.adjoint B (B v) := by
        rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      rw [this, hBv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 e
  rw [hBadj, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)) (X : Set M)
    (hS : ∀ b ∈ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u) : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact hS b hb
  | algebraMap r => exact ⟨r, fun u _ => Module.algebraMap_end_apply ℂ ℂ M r u⟩
  | add b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ + μ', fun u hu => by rw [LinearMap.add_apply, hμ u hu, hμ' u hu, add_smul]⟩
  | mul b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ * μ', fun u hu => by rw [Module.End.mul_apply, hμ' u hu, map_smul, hμ u hu, smul_smul, mul_comm]⟩

end GlobalTheory.SplitEigen

namespace GlobalTheory.SplitEigen


set_option maxHeartbeats 40000000 in
theorem label_scalar_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hEx _hH _hGE j c h hh hN P hP hconj d _hd
  obtain ⟨hCoreF, -, -, hOnto, -, -, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hCoreF hEx
  have hM := hCore.models
  obtain ⟨P0, hP0, rfl⟩ := (hOnto _ hP).2 hconj
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hM).2 j A3.A.fam.μ0 h hh ⟨P0, hP0⟩
  have hK := RealDat3.kFormL_of (R := R) (F := F) hM

  have hop : ∀ k, k ≤ (Vc D j).rank → (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inl (⟨P0, hP0⟩, k))) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) := by
    intro k hk
    refine LinearMap.ext_on_range (hK j A3.A.fam.μ0).2 fun b => ?_
    rw [← CxData.jL_opL _ hK]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hsplit k hk _)

  have hT : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))) • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have e1 := (U2.mem_eigPart.1 hx) (Sum.inl (⟨P0, hP0⟩, k))
    have e2 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (U2.liftHeckeOperators A3 (R.toCx3 F) j (Sum.inl (⟨P0, hP0⟩, k)) x) =
        h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H)) (LinearMap.congr_fun (hop k hk) x)).trans rfl
    rw [← e2, e1]
    exact Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H) _ _

  have hD : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))) •
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have ha : LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) =
        h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) := by
      rw [hN.2 _ hP]
      congr 1
      rw [Finsupp.mapRange_single, star_one, GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single]
    have hc : Commute (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))
        (LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))) :=
      ha.symm ▸ hN.1 _ _ hP hP _ _
    exact (LinearMap.congr_fun ha _).symm.trans (adjoint_apply_of_eigen _ hc _ _ (hT k hk x hx))

  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Vc D j) (R.pl P0) hconj _
    (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W) d
  have key := adjoin_scalar _ {u | ∃ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      u = (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)} (by
    rintro b ⟨k, hk, rfl | rfl⟩
    · refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hT k hk x hx)).trans (map_smul _ _ _)))
    · refine ⟨starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hD k hk x hx)).trans (map_smul _ _ _)))) a ha
  obtain ⟨μ, hμ⟩ := key
  refine ⟨μ, fun x hx => (hM.HV j A3.A.fam.μ0).1 ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) (R.pl P0), GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W k
      ((R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)) =
        (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
    obtain ⟨n, hn⟩ := hCore.lev.βV j
    have hn' : IsBaseFrame (Vc D j) (R.βV j) (R.ΛV j) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
    refine GlobalTheory.DefiniteOps.fixed_of_mem (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j A3.A.fam.μ0) hn' (R.pl P0) hP (R.cV j).coef.ρ _ ?_
    have hm := LinearMap.mem_range_self (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)
    rw [(hM.HV j A3.A.fam.μ0).2.1] at hm
    exact hm
  exact (hh _ hP _ _).trans ((GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).trans ((hae _ hfix).symm.trans
    ((hμ _ ⟨x, hx, rfl⟩).trans (map_smul _ _ _).symm)))

end GlobalTheory.SplitEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameRowReductionConjLinearIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLin

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (starRingEnd D.host.E x) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem toEAf_incA_bar (c : 𝓞 D.host.E) :
    toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) =
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
  simp [toEAf, finPart, incA, inclR, Formalism.L2.DIV.oToS, Formalism.UG.inclE]
  rfl

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

variable {D : D7}

theorem tmul_smul_add (p : AF D.host.F) (c x y : D.host.E) :
    p ⊗ₜ[D.host.F] (c * x + y) = (p ⊗ₜ[D.host.F] x) * incA D c + p ⊗ₜ[D.host.F] y := by
  rw [TensorProduct.tmul_add]
  congr 1
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm x c]

theorem rowAdj_smul_add (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D)
    (u v : Fin T.rank → D.host.E) (c : D.host.E) :
    GlobalTheory.LiftDat.rowAdj T βT a e (c • u + v) =
      toEAf D (incA D (starRingEnd D.host.E c)) • GlobalTheory.LiftDat.rowAdj T βT a e u + GlobalTheory.LiftDat.rowAdj T βT a e v := by
  have hM : (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c • u + v) k) * incA D (T.gram k l)) =
      incA D (starRingEnd D.host.E c) • (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] u k) * incA D (T.gram k l)) +
      (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      tmul_smul_add, mul_add, map_add, map_mul, cA_incA, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GlobalTheory.LiftDat.rowAdj
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

theorem rowRed_smul_add : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  intro D T βT a e PP u v hu hv c
  have hz := toEAf_incA_bar (D := D) c
  have hrow := rowAdj_smul_add T βT a e u v (c : D.host.E)
  have hzi : toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hz]; exact Subtype.property _
  have hent : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j =
      toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) * GlobalTheory.LiftDat.rowAdj T βT a e u 0 j + GlobalTheory.LiftDat.rowAdj T βT a e v 0 j := by
    intro j; rw [hrow]; simp [Matrix.add_apply, Matrix.smul_apply]
  have hint : IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hent]
    exact Subring.add_mem _ (Subring.mul_mem _ hzi (hu 0 j)) (hv 0 j)
  refine ⟨hint, ?_⟩
  funext j
  simp only [GlobalTheory.LiftDat.rowRed, redM, dif_pos (hint 0 j), dif_pos (hu 0 j), dif_pos (hv 0 j)]
  have hsub : (⟨GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j, hint 0 j⟩ :
      Formalism.L2.Herm.intAf D.host.F D.host.E) =
      Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) * ⟨_, hu 0 j⟩ + ⟨_, hv 0 j⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, ← hz, hent]
  rw [hsub, RingHom.map_add, RingHom.map_mul, Formalism.L2.DIV.resS_oToS]

end GlobalTheory.RowLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResHeisCont

theorem continuous_res_heisO : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 h𝓨 f hf u
  have hψ := hω.std.1
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B 0 := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf K hK
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun p =>
      ((GlobalTheory.HeisOrtho.continuous_heisO hψ (hω.om_pres p f hf).cont u).comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ]; exact hc p hp _
  · refine Filter.Eventually.of_forall fun y => ?_
    unfold heisO
    exact (continuous_const.mul (hω.om_cont f hf _)).continuousAt

end GlobalTheory.ResHeisCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalanceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_unitary_antidiagonalForm_exponent_balance : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  first | exact @GlobalTheory.diag_unitary_exp_sym | exact GlobalTheory.diag_unitary_exp_sym | (intros; apply GlobalTheory.diag_unitary_exp_sym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrixStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
end

