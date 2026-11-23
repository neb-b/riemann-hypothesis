module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CuspDim.IsoPow

variable {Z : Scheme.{0}} {B : LB Z}

theorem res_res {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Z, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  change (Z.presheaf.map (homOfLE h).op ≫ Z.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

theorem pow_le (n : ℕ) (j : PUnit → B.ι) : (lbPow B n).U j ≤ B.U (j PUnit.unit) :=
  LB.wchart_le B (fun _ => 𝟙 Z) j PUnit.unit

theorem res_pow_g (n : ℕ) (j j' : PUnit → B.ι) {W : Z.Opens} (h : W ≤ (lbPow B n).U j ⊓ (lbPow B n).U j') :
    res h ((lbPow B n).g j j') =
      res (h.trans (inf_le_inf (pow_le n j) (pow_le n j'))) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
  have e : (lbPow B n).g j j' =
      res (inf_le_inf (pow_le n j) (pow_le n j')) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) :=
    Fintype.prod_unique fun a : PUnit.{1} => res (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => 𝟙 Z) j a))
      (inf_le_right.trans (LB.wchart_le B (fun _ => 𝟙 Z) j' a))) (pullU (𝟙 Z) _ (B.g (j a) (j' a))) ^ (n : ℤ)
  rw [e, zpow_natCast, map_pow, res_res]



theorem ev_res_pow {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} {U W : Z.Opens} {y : CxPts q σ} (h : W ≤ U)
    (hy : y ∈ ptsIn q σ W) (u : Γ(Z, U)ˣ) (n : ℕ) :
    ev q σ W (res h u ^ n).val y = ev q σ U u.val y ^ (n : ℤ) := by
  rw [zpow_natCast, ← ev_res h hy, ev_eq hy, ev_eq hy, Units.val_pow_eq_pow_val, map_pow]
  rfl

end GlobalTheory.CuspDim.IsoPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesEvalZeroFormMemAdmissible
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

end GlobalTheory.MixUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.AdelicFourierSch

open Filter GlobalTheory.WeylFourier GlobalTheory.RatWeilOp GlobalTheory.WeylBij


open scoped Classical in
theorem fourier_mem_schA_std (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F))
    [μ.IsAddHaarMeasure] : ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  have hunr := psiUnr_eventually ψ hψ
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl (F := F), BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl (F := F), Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl (F := F), TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := _root_.GlobalTheory.ArchFourier.exists_fourier_sInf F κ μi
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [hunr] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := ftE ψ μ
  have hfam : ∀ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v) := fun φ hφ =>
    ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
  have hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := fun f φ hφ =>
    (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2
  have hgen := schA_le_span_pure F κ
  have hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ := by
    intro Φ hΦ
    refine (Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    show T _ ∈ schA F κ
    rw [hTpure f φ hφ]
    exact pure_mem_schA _ _ (hfam φ hφ)
  have hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ := fun Φ hΦ => by
    refine (Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact (hpureE f φ hφ).1
  intro Φ hΦ
  have h := hT_schA Φ hΦ
  rw [show T Φ = ft ψ μ Φ from ftE_eq ψ μ (hint Φ hΦ)] at h
  exact h

theorem dilate_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {a : F} (ha : a ≠ 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun y => Φ (algebraMap F (AF F) a • y)) ∈ schA F κ := by
  classical
  have hdet : IsUnit (Matrix.diagonal fun _ : κ => a⁻¹).det := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero ha).isUnit
  have hinv : (Matrix.diagonal fun _ : κ => a⁻¹)⁻¹ = Matrix.diagonal fun _ : κ => a := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ ha]
  have h := GlobalTheory.SympChangeBij.levi_mapsTo _ hdet Φ hΦ
  rw [hinv, Matrix.diagonal_map (map_zero _)] at h
  convert h using 2 with y
  rw [LinearMap.funLeft_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem fourier_mem_schA : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Φ hΦ
  have h0 := GlobalTheory.SubstIntertw.isStd_stdChar F
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F _ ψ (GlobalTheory.StdCharFromIsStd.isCharAF h0) hψ
  have h := dilate_mem_schA ha (fourier_mem_schA_std F _ h0 κ μ Φ hΦ)
  convert h using 4 with y x
  rw [hψa, dotProduct_smul, smul_eq_mul]

end GlobalTheory.AdelicFourierSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaOppParab

variable {κ : Type}

def negSnd {M : Type} [Neg M] (x : κ ⊕ κ → M) : κ ⊕ κ → M := Sum.elim (fun i => x (Sum.inl i)) (fun i => -x (Sum.inr i))

theorem negSnd_negSnd {M : Type} [InvolutiveNeg M] (x : κ ⊕ κ → M) : negSnd (negSnd x) = x :=
  funext fun i => by cases i <;> simp [negSnd]

theorem negSnd_add {M : Type} [AddCommGroup M] (x y : κ ⊕ κ → M) : negSnd (x + y) = negSnd x + negSnd y :=
  funext fun i => by cases i <;> simp [negSnd, add_comm]

theorem negSnd_dot {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ y = x ⬝ᵥ negSnd y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

theorem negSnd_dot_negSnd {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ negSnd y = x ⬝ᵥ y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

def negSndL (R M : Type) [Semiring R] [AddCommGroup M] [Module R M] : (κ ⊕ κ → M) ≃ₗ[R] (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  map_add' := negSnd_add
  map_smul' c x := funext fun i => by cases i <;> simp [negSnd, Pi.smul_apply, smul_neg]
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd

def negSndH (M : Type) [TopologicalSpace M] [AddGroup M] [ContinuousNeg M] : (κ ⊕ κ → M) ≃ₜ (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd
  continuous_toFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg
  continuous_invFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg

theorem map_neg_one_mat {n R S G : Type} [DecidableEq n] [Ring R] [Ring S] [FunLike G R S] [RingHomClass G R S]
    (f : G) : (-1 : Matrix n n R).map f = -1 := by
  rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

variable (F : Type) [Field F] [NumberField F]
open scoped Classical

def negOp : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) := LinearMap.funLeft ℂ ℂ negSnd

theorem negOp_apply (φ : (κ ⊕ κ → AF F) → ℂ) (x) : negOp F φ x = φ (negSnd x) := rfl

theorem negOp_negOp (φ : (κ ⊕ κ → AF F) → ℂ) : negOp F (negOp F φ) = φ :=
  funext fun x => by simp [negOp_apply, negSnd_negSnd]

theorem negOp_schr [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) (φ : (κ ⊕ κ → AF F) → ℂ) :
    negOp F (schr ψ w φ) = schr ψ (negSnd w.1, negSnd w.2) (negOp F φ) := by
  funext x
  simp only [negOp_apply, schr, negSnd_dot, negSnd_add, negSnd_negSnd]

theorem pureA_negSnd [Fintype κ] (f : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    negOp F (pureA F f g) = pureA F (f ∘ negSnd) (g ∘ negSnd) := by
  funext x
  simp only [negOp_apply, pureA, Function.comp_apply]
  congr 2
  · funext i
    cases i with
    | inl i => rfl
    | inr i => exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x (Sum.inr i)).1
  · funext i
    cases i with
    | inl i => rfl
    | inr i => rfl

theorem comp_negOp_mem_adm [Fintype κ] {l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (κ ⊕ κ)) :
    l ∘ₗ negOp F ∈ (adeleClass F).adm (κ ⊕ κ) := by
  intro g hg
  let A : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    (negSndL ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearEquiv
  let B := negSndH (κ := κ) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨T, hT⟩ := hl (g ∘ B) ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩
  refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A), fun f => ?_⟩
  rw [LinearMap.comp_apply, pureA_negSnd, ContinuousLinearMap.comp_apply, ← hT]
  rfl

theorem thetaSum_negOp [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ) : thetaSum F (negOp F φ) = thetaSum F φ := by
  unfold thetaSum
  have e := Equiv.tsum_eq (negSndL (κ := κ) F F).toEquiv (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i))
  refine Eq.trans (tsum_congr fun ξ => ?_) e
  show φ (negSnd _) = φ (fun i => algebraMap F (AF F) (negSnd ξ i))
  congr 1
  funext i
  cases i <;> simp [negSnd]


open scoped Classical in
theorem thetaSum_omd_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (cA σ) (dbl (incM F JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ a b JA JB κ _ hcard d hd dd hdd χ hχ omd hS hR q q₀ hq s hqs φ hφ
  let M₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := Matrix.fromBlocks 1 0 0 (-1)
  let M₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E) := Matrix.fromBlocks 1 0 0 (-1)
  have hM₀sq : M₀ * M₀ = 1 := by simp [M₀, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hM₀' : incM F M₀' = M₀ := by
    simp only [M₀, M₀', incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
  let w₀g : GL (Fin b ⊕ Fin b) (AE F E) := ⟨M₀, M₀, hM₀sq, hM₀sq⟩
  have hw₀mem : w₀g ∈ UG (cA σ) (dbl (incM F JB)) := by
    show M₀ᵀ * dbl (incM F JB) * M₀.map (cA σ) = dbl (incM F JB)
    simp only [M₀, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Matrix.fromBlocks_multiply]
  let w₀ : UG (cA σ) (dbl (incM F JB)) := ⟨w₀g, hw₀mem⟩
  have hw₀v : ((w₀ : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = M₀ := rfl
  have hw₀w₀ : w₀ * w₀ = 1 := Subtype.ext (Units.ext hM₀sq)
  let p : UG (cA σ) (dbl (incM F JB)) := w₀ * q * w₀
  have hpv : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      M₀ * ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * M₀ := rfl
  have hp₀ : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      incM F (M₀' * q₀ * M₀') := by
    rw [hpv, hq, ← hM₀']
    simp only [incM, Matrix.map_mul]
  have hMd : M₀ * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hMa : M₀ * (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hqs' : ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) *
        (s : Matrix (Fin b) (Fin b) (AE F E)) := hqs
  have hps : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) * (s : Matrix (Fin b) (Fin b) (AE F E)) := by
    rw [hpv]
    simp only [Matrix.mul_assoc]
    rw [hMd, hqs', ← Matrix.mul_assoc, hMa]
  have hsieg := GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hcard d hd dd hdd χ hχ omd hS hR p (M₀' * q₀ * M₀') hp₀ s hps
  have hrel : ∀ v, dd.e (actB (cA σ) w₀ v) = (negSnd (dd.e v).1, negSnd (dd.e v).2) := by
    intro v
    have hv : actB (cA σ) w₀ v = Matrix.fromCols v.toCols₁ (-v.toCols₂) := by
      rw [actB, hw₀v]
      conv_lhs => rw [← Matrix.fromCols_toCols v]
      rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp
    conv_rhs => rw [← Matrix.fromCols_toCols v]
    rw [hv, hdd, hdd, map_neg]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp [negSnd]
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute ψ hψ (negOp F * omd w₀)
    (fun l hl => by
      rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact hS.adm w₀ _ (comp_negOp_mem_adm F hl))
    (fun w φ hφ => by
      obtain ⟨v, rfl⟩ := dd.e.surjective w
      have e1 : schr ψ (dd.e v) = dd.rho ψ v := rfl
      rw [e1, mul_apply_eq_comp, mul_apply_eq_comp, hS.impl w₀ v φ hφ, Darboux.rho, hrel, negOp_schr]
      simp only [negSnd_negSnd]
      rfl)
  have hsm : ∀ (c : ℂ) (f : (κ ⊕ κ → AF F) → ℂ), thetaSum F (c • f) = c * thetaSum F f := fun c f => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  have hΘw : ∀ X ∈ schA F (κ ⊕ κ), thetaSum F (omd w₀ X) = c * thetaSum F X := fun X hX => by
    have h1 := congrArg (negOp F) (hc X hX)
    rw [mul_apply_eq_comp, negOp_negOp, map_smul] at h1
    rw [h1, hsm, thetaSum_negOp]
  have hq' : q = w₀ * p * w₀ := by
    show q = w₀ * (w₀ * q * w₀) * w₀
    rw [show w₀ * (w₀ * q * w₀) * w₀ = (w₀ * w₀) * q * (w₀ * w₀) by group, hw₀w₀, one_mul, mul_one]
  calc thetaSum F (omd q φ) = thetaSum F (omd w₀ (omd p (omd w₀ φ))) := by
        rw [hq', map_mul, map_mul]; rfl
    _ = c * thetaSum F (omd p (omd w₀ φ)) := hΘw _ (hS.pres _ _ (hS.pres _ _ hφ))
    _ = c * thetaSum F (omd w₀ φ) :=
      congrArg (fun z => c * z) (hsieg (omd w₀ φ) (hS.pres w₀ φ hφ))
    _ = thetaSum F (omd w₀ (omd w₀ φ)) := (hΘw _ (hS.pres _ _ hφ)).symm
    _ = thetaSum F φ := by rw [← mul_apply_eq_comp, ← map_mul, hw₀w₀, map_one, one_apply_eq_self]

end GlobalTheory.ThetaOppParab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUniqueStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeilRep_schrodingerModel_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  first | exact @GlobalTheory.WeilSchUnique.weil_unique | exact GlobalTheory.WeilSchUnique.weil_unique | (intros; apply GlobalTheory.WeilSchUnique.weil_unique <;> assumption)
end

