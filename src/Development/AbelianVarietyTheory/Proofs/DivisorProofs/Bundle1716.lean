module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalOf
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsWeightCompat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem markOver_zsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l l₂ : Level H} {r : ℕ} {L : Lt E r} {mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : MarkOver l l₂ L mk mk₂) (m : ℤ) :
    MarkOver l l₂ L (m • mk) (m • mk₂) := fun a ha => by
  obtain ⟨u, hu, e⟩ := h a ha
  refine ⟨m • u, zsmul_mem hu _, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e, smul_add, smul_comm m l.M]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem div_mul_phiC {s : T.Q.c.F →+* ℂ} {W : HSp D} {j : ℕ} (hV : T.V j s = W) (hc : CUnit (T.cE j s))
    (cst : (T.U j s).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (h : GA D W) :
    cst (castDict hV (T.dict j s) h).1 / T.cE j s (castDict hV (T.dict j s) h).1 * phiC T hV a f h =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (castDict hV (T.dict j s) h).1 * castDict hV (T.mu j s) h *
        rdU (T.U j s) f (castDict hV (T.dict j s) h).1 (castDict hV (T.dict j s) h).2) := by
  subst hV
  have h0 : T.cE j s (T.dict j s h).1 ≠ 0 := norm_ne_zero_iff.1 ((hc _).trans_ne one_ne_zero)
  change cst (T.dict j s h).1 / T.cE j s (T.dict j s h).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
    (T.cE j s (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)) =
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)
  field_simp

theorem inj_of_indep {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module ℂ M] {s : K →+* ℂ}
    (c : X →ₛₗ[s] M) (h : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ fun j => c (b j)) :
    Function.Injective c := (injective_iff_map_eq_zero c).2 fun x hx => by
  by_contra h0
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem exists_ext (O : OM T R i) (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hP : Pinned κ v₀ O)
    (σ : D.what₂.LL →+* ℂ) : ∃ σ' : O.c'.F →+* ℂ, σ'.comp O.jL = σ := by
  have hs : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ : (y : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hF ▸ y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hP.lift.field x).trans hx)⟩
  let e := RingEquiv.ofBijective O.jL ⟨O.jL.injective, hs⟩
  exact ⟨σ.comp e.symm.toRingHom, RingHom.ext fun x => congrArg σ (e.symm_apply_apply x)⟩

end GlobalTheory.GalOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval

theorem lintegral_partL_eq : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hT μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : ℝ≥0, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL T Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ = C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    fun y => hC₁ _ (sliceL_mem hΦ y)
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DblEval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReScalNonzeroIndexPlaceIff
section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.BigOn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLev_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.toLevCh.Is A.μ0) :
    (reScal R lam kap).toLevCh.Is A.μ0 := h

theorem isGrp_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsGrp F) :
    (reScal R lam kap).IsGrp F := { h with }

theorem isFam_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsFam) :
    (reScal R lam kap).IsFam := { h with }

theorem isModels_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsModels) :
    (reScal R lam kap).IsModels := { h with }

theorem isChain_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsChain) :
    (reScal R lam kap).IsChain := { h with }

theorem isThP_rescale (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsThP) :
    (reScal R lam kap).IsThP := { h with }

def reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : CxData B :=
  { X with lam := lam, κ := κ }

theorem liftMatC_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMatC cr b j t = X.liftMatC cr b j t := rfl

theorem liftMat_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMat cr b j t = X.liftMat cr b j t :=
  congrArg (kMat Bs.v0.embedding) (liftMatC_reScalCx X lam κ cr b j t)

theorem iw_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) : ((reScalCx X lam κ).data cr b).Iw = (X.data cr b).Iw := by
  funext j t w
  exact congrArg (fun θ => idx w (X.M b j) (matLat θ ((lv (fc X.zs) b).Tl j t))) (liftMat_reScalCx X lam κ cr b j t)

theorem zs_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : (reScalCx X lam κ).zs = X.zs := rfl

set_option maxHeartbeats 1000000 in
theorem toCx_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) :
    (reScal R lam kap).toCx F = reScalCx (R.toCx F) lam (fun _ => kap) := rfl

theorem reScal_nonzeroIndexPlace_iff (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : (reScal R lam kap).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := by
  unfold RealDat.NonzeroIndexPlace
  rw [toCx_reScal, iw_reScalCx, zs_reScalCx]

theorem isTup_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsTup F) :
    (reScal R lam kap).IsTup F :=
  ⟨fun w hw => h.tw w ((reScal_nonzeroIndexPlace_iff R F lam kap w).1 hw), h.mu_off, h.mu_used, h.mu_ne, h.mu_conj, h.mu_on⟩

end

theorem char_charOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsTup F → (charOf R F).Char F := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h1 h2 h3 h4 h5 h6 h7
  obtain ⟨lam, kap, hs⟩ := GlobalTheory.ScalChoice.exists_isScal D G Pl0 T0 A Ks R F
  have hex : ∃ q : (type_of% R.lam) × ℝ, (reScal R q.1 q.2).Char F :=
    ⟨(lam, kap), isLev_reScal R lam kap h1, isGrp_reScal R F lam kap h2, isFam_reScal R lam kap h3,
      isModels_reScal R lam kap h4, isChain_reScal R lam kap h5, isThP_rescale R lam kap h6, hs,
      isTup_reScal R F lam kap h7⟩
  exact Classical.epsilon_spec hex

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealGramHermitianSpaceDoubledBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestr

open GlobalTheory.Doubling GlobalTheory.DblSchr GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero Formalism.IndefR.Datum

theorem partner_dbl {D : D7} (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
    (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (hgd : gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1) (gs : GA D S) (hgs : mt S gs = (g⁻¹).1.1ᵀ)
    (gdd : GA D (dblSp S)) (hgdd : mt (dblSp S) gdd = ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1ᵀ) :
    gdd = io S (gs, 1) := by
  have hg1 : g.1.1 * (g⁻¹).1.1 = 1 := Units.mul_inv g.1
  have hinv : (gd⁻¹).1.1 = Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hgd, Matrix.fromBlocks_multiply, hg1]
    simp [Matrix.fromBlocks_one]
  have hr : ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1 =
      (Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← map_inv, reG_val, hinv]
  have hm3 : mt (dblSp S) (io S (gs, 1)) =
      (Matrix.fromBlocks (mt S gs) 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  have hm : mt (dblSp S) gdd = mt (dblSp S) (io S (gs, 1)) := by
    rw [hgdd, hr, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, ← hgs, hm3, Matrix.transpose_zero,
      Matrix.transpose_one]
  exact Subtype.ext (Units.ext hm)

theorem restr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omd₀ homd g gd hgd φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨gs, h1, hh1, hgs⟩ := _root_.GlobalTheory.WeilPairPartner.pair_partner D S T JA JB ξ hA hB 1 g
  have h1e : h1 = 1 := Subtype.ext (Units.ext (hh1.trans rfl))
  obtain ⟨gdd, h2, hh2, hgdd⟩ := _root_.GlobalTheory.WeilPairPartner.pair_partner D (dblSp S) T JA (JBd S JB) ξ hA (dblGram_xi D S JB ξ hB) 1
    (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)
  have h2e : h2 = 1 := Subtype.ext (Units.ext (hh2.trans rfl))
  have hgdd' : gdd = io S (gs, 1) := partner_dbl S JB g gd hgd gs hgs gdd hgdd
  subst h1e h2e hgdd'
  have t1 := hom 1 g gs 1 hh1 hgs φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  have t2 := homd 1 (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd) (io S (gs, 1)) 1 hh2 hgdd _ hΦ
  have hφ₂' := _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection D.host.F κ φ₂ hφ₂
  have th₁ := _root_.GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hrat φ₁ hφ₁
  have th₂ := _root_.GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hψ S T JA JB ξ hA hB κ co hrat _ hφ₂'
  have key := t2.2.trans ((congrArg (ωd (io S (gs, 1), 1)) (_root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((_root_.GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor D ψ hψ S T χS χT ω hω ωd hωd gs _ _ th₁ th₂).trans
      ((congrArg (fun f => GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f
        (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (_root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co _ t1.1 φ₂ hφ₂).symm)))
  refine _root_.GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace D ψ hψ (κ ⊕ κ) _ t2.1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ t1.1 φ₂ hφ₂) fun w => ?_
  have := congrFun key ((ddr co).e.symm w)
  simpa only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] using this

end GlobalTheory.DblRestr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperators
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
namespace GlobalTheory.EvKer

theorem ker_trivial : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  intro F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev
  classical
  by_contra hne
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  set φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef
  have hφSB : ∀ w, φ w ∈ SB (κ → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hψ
    · simpa [φ, Function.update_of_ne h, stdInd] using GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w
  have hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w := by
    exact (Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]
  have hmem : pure f₀ φ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)
  have hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0 := by
    funext w
    by_cases h : w = v
    · subst h; simp [φ, hev]
    · simp [φ, Function.update_of_ne h]
  have hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w =
      {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1 := by
    simpa [stdInd] using hstd
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd
  have hzero : e (pure f₀ φ) = 0 := by
    rw [hpure f₀ φ hφSB hφev, hcomp, ← hr 0]
    funext x
    simp [tens]
  have h0 : pure f₀ φ = 0 := hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])
  have hall : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hne
    · simp only [φ, Function.update_of_ne h]
      intro h1
      have := congrFun h1 0
      simp [stdInd, Set.indicator, zero_mem] at this
  have := GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0
  exact hf₀ (by rw [this]; rfl)

end GlobalTheory.EvKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_tensor_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (vac vac₁ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (ei : SInf F κ →L[ℂ] SInf F κ) (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, vac v ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ᶠ v in Filter.cofinite, vac₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ v, ev v (vac v) = vac₁ v) → (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ f φ, (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    (∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x))) →
    (∀ v : Pl (F := F), ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x))) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.TensorSquareIntegral.exists_const_tensor | exact GlobalTheory.TensorSquareIntegral.exists_const_tensor | (intros; apply GlobalTheory.TensorSquareIntegral.exists_const_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBoundCoprimeTorsionMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortSeries_bound_coprime_torsion_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → ∀ s : c.F, (∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (s * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  first | exact @GlobalTheory.SupFull.bound_of_coprime_mul | exact GlobalTheory.SupFull.bound_of_coprime_mul | (intros; apply GlobalTheory.SupFull.bound_of_coprime_mul <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrixStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_for_unipotent_matrix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.unipM S) := by
  first | exact @GlobalTheory.SympUnip.hasOp_unipM | exact GlobalTheory.SympUnip.hasOp_unipM | (intros; apply GlobalTheory.SympUnip.hasOp_unipM <;> assumption)
end

