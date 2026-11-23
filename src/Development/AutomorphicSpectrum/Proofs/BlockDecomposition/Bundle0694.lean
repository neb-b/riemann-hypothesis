module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSection
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverage
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem actW_rat_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (g : HA (AF F) σ J) (X : Fin 1 → Fin 1 → E) (a i : Fin 1) :
    actW (AF F) σ J g (ratTup (AF F) X) a i = (ue (AF F) σ J g : AF F ⊗[F] E) * inclR (AF F) (X a i) := by
  have e : ((ue (AF F) σ J g : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (HA.mat (AF F) σ J g).val 0 0 := by
    simp [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [e]
  simp only [actW, actTup, Matrix.mulVec, dotProduct, ratTup, Fin.sum_univ_one, Subsingleton.elim i 0,
    Subsingleton.elim a 0]

theorem mean_eq_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  intro F E _ _ _ _ _ σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 1
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm 1 J hJ (AF F)
  obtain ⟨ac, -, -, -⟩ := hact 1
  obtain ⟨i1, i2, i3, i4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Ainf F)
  have := k8 1 1
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 1
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 1 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hPsi : Measurable (Psi φ A) :=
    (ENNReal.measurable_ofReal.comp (hφc.comp t1).measurable).indicator hP.measurableSet
  have hmul : Continuous fun (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (a i : Fin 1) => (x : AF F ⊗[F] E) * Y a i :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  set Φ : (Fin 1 → Fin 1 → AF F ⊗[F] E) → ℝ≥0∞ := fun Y => Psi φ A fun a i => (x : AF F ⊗[F] E) * Y a i with hΦd
  have hΦ : Measurable Φ := hPsi.comp hmul.measurable
  have hQ : MeasurableSet {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v} :=
    (hP.preimage hmul).measurableSet
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hterm : ∀ (h : HA (AF F) σ J), Th φ A (x * ue (AF F) σ J h⁻¹) =
      ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _), Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) := fun h => by
    refine tsum_congr fun X => ?_
    simp only [hΦd]
    congr 1
    funext a i
    rw [actW_rat_one, Units.val_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hterm]
    rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 _ Φ hΦ, mean, ← lintegral_indicator hQ]
    refine lintegral_congr fun X => ?_
    simp only [hΦd, Psi, Set.indicator, Set.mem_setOf_eq]
  · simp only [hterm]
    exact Measurable.tsum fun X => hΦ.comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem compact_finite_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc hfin C hC
  obtain ⟨b1, b2, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hcm M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have := hB n M
  have := hB 1 (M + 1)
  have := hB (n + 1) (M + 1)
  obtain ⟨hTG, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm _ _ hJ' R
  obtain ⟨-, k1, k2⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  have e0 : gramR R σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    funext a a'
    simp only [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, JR, blockOne, Fin.sum_univ_succ, hermScal, Fin.cons_zero, Fin.cons_succ,
      map_one, map_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.map_apply,
      Matrix.of_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes t
  obtain ⟨s, sm, s1, s2⟩ := _root_.GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section F E σ hcm _ _ hJ' R hR (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) (by
    rw [e0, Matrix.det_unique]
    exact (ht.isUnit.map (algebraMap F R)).map (algebraMap R (R ⊗[F] E)))
  rw [e0] at s1 s2
  have hCm : MeasurableSet C := hC.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeStage.fibre_block_stages_free F E σ hcm M J hJ t ht n T hT hT' R hR d b lam hlam m m₁ m' hm hm₁ hm' c hc
    (C.indicator 1) (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm] at hint
  have hc' : Continuous (consTup : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    exacts [continuous_const, continuous_const, continuous_const, continuous_apply_apply a i]

  let p : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin 1 → Fin (M + 1) → R ⊗[F] E) := fun X _ => X 0
  have hpc : Continuous p := continuous_pi fun _ => continuous_apply 0
  have hC₁ : IsCompact (p '' C) := hC.image hpc
  obtain ⟨C', hC', hs⟩ := s2 _ hC₁

  let r : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun Y a i => Y a.succ i.succ
  have hrc : Continuous r := continuous_pi fun a => continuous_pi fun i => continuous_apply_apply a.succ i.succ
  have hD : IsCompact ((fun q : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ q.1⁻¹ q.2) '' (C' ×ˢ C)) :=
    (hC'.prod hC).image ((hact (n + 1)).1.comp (continuous_fst.inv.prodMk continuous_snd))
  obtain ⟨K, hK, hKsub⟩ : ∃ K : Set (Fin n → Fin M → R ⊗[F] E), IsCompact K ∧
      ∀ h ∈ C', ∀ X, actW R σ _ h (consTup X) ∈ C → X ∈ K := by
    refine ⟨_, hD.image hrc, fun h hh X hX => ⟨consTup X, ⟨(h, _), ⟨hh, hX⟩, ?_⟩, rfl⟩⟩
    show actW R σ _ h⁻¹ (actW R σ _ h (consTup X)) = consTup X
    rw [← (hact _).2.2.1, inv_mul_cancel, (hact _).2.1]
  have hKf := hfin K hK
  have hfirst : ∀ (h : HA R σ (blockOne (algebraMap F E t) J)) (X : Fin n → Fin M → R ⊗[F] E),
      p (actW R σ _ h (consTup X)) = actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) := fun h X => rfl
  have hae : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    refine measure_mono_null ?_ (hm₁.1 (hermScal R σ (algebraMap F R t)))
    intro y hy hy'
    exact hy hy'.1
  have hbound : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      Ψ y ≤ (p '' C).indicator (fun _ => m' (hermOf R σ T hT) K) y := by
    filter_upwards [hae] with y hy
    have hy' := s1 y hy
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => actW R σ _ (s y) (consTup X) :=
      ((hact _).1.comp (continuous_const.prodMk hc')).measurable
    have hΨy : Ψ y = m' (hermOf R σ T hT) {X | actW R σ _ (s y) (consTup X) ∈ C} := by
      have h1 := hΨ (s y)
      rw [hy'] at h1
      rw [h1]
      have h2 : (fun X : Fin n → Fin M → R ⊗[F] E =>
          C.indicator (1 : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (actW R σ _ (s y) (consTup X))) =
          {X | actW R σ _ (s y) (consTup X) ∈ C}.indicator 1 := by
        funext X
        simp [Set.indicator]
      rw [h2]
      exact lintegral_indicator_one (hmeas hCm)
    by_cases hyC : y ∈ p '' C
    · rw [Set.indicator_of_mem hyC, hΨy]
      exact measure_mono fun X hX => hKsub _ (hs y hyC hy) X hX
    · have hempty : {X | actW R σ _ (s y) (consTup X) ∈ C} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun X hX => hyC ⟨_, hX, ?_⟩
        rw [hfirst, hy']
      rw [hΨy, hempty, measure_empty]
      exact bot_le
  have hloc := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hcm _ _ hJ' R hR 1 _ _ _ (k1 1 (M + 1)) (k2 1) hm₁
    (hermScal R σ (algebraMap F R t))).1
  have hΨf : ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) < ⊤ := by
    refine (lintegral_mono_ae hbound).trans_lt ?_
    rw [lintegral_indicator_const hC₁.measurableSet]
    exact ENNReal.mul_lt_top hKf hC₁.measure_lt_top
  rw [hint]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hΨf

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReduction
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelTheta

def colMajorant {D : D7} (θ : InfFam D) (m : ℕ) (L : Set (Matrix (Fin m) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (N : ℕ) (v : Mx D m 1) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ v i 0‖) ^ N)⁻¹ *
    Set.indicator L (fun _ => (1 : ℝ)) (v.map (finPart D)))

def pureT {D : D7} (θ : InfFam D) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) (x : Mx D m n) : ℂ :=
  f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))

theorem pure_le_colMajorant (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧ ∀ N : ℕ, ∃ C : ℝ,
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤
          ENNReal.ofReal C * ∏ j : Fin n, colMajorant θ V.rank L N (fun i (_ : Fin 1) => x i j) := by
  obtain ⟨C0, L, hL, h0⟩ := _root_.GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant D θ hθ V n f g hg C₁ hC₁ 0
  refine ⟨L, hL, fun N => ?_⟩
  obtain ⟨CN, LN, -, hN⟩ := _root_.GlobalTheory.CompanionTheory.WeilMaj.schwartz_translate_majorant D θ hθ V n f g hg C₁ hC₁ N
  refine ⟨CN, fun y hy x => ?_⟩
  by_cases hall : ∀ j : Fin n, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L
  · refine (hN y hy x).trans ?_
    gcongr with j _
    unfold colMajorant
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) = 1 :=
      Set.indicator_of_mem (hall j) _
    refine le_trans ?_ (le_of_eq h1.symm)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) _ |>.trans le_rfl
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hz : ‖pureT θ f g (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ = 0 := by
      refine le_antisymm ((h0 y hy x).trans (le_of_eq ?_)) bot_le
      rw [Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
      rw [Set.indicator_of_notMem hj, mul_zero, ENNReal.ofReal_zero]
    rw [hz]
    exact bot_le

theorem absTheta_pure_le (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) {c : ℝ} (hc : 0 < c)
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ C₁, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a →
      absTheta V (pureT θ f g) (a * y) ≤
        ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  obtain ⟨L, hL, hmaj⟩ := pure_le_colMajorant D θ hθ V n f g hg C₁ hC₁
  obtain ⟨N₀, hcount⟩ := _root_.GlobalTheory.CompanionTheory.WeilCount.count_main D θ hθ V Xf Yf hW hc L hL
  obtain ⟨C', hC'⟩ := hcount N₀ le_rfl
  obtain ⟨C, hC⟩ := hmaj N₀
  refine ⟨max C 0 * max C' 0 ^ n, by positivity, fun y hy t ht a ha => ?_⟩
  have h1 := GlobalTheory.CompanionTheory.ColProd.absTheta_le_pow_of_colProd D V (pureT θ f g) (colMajorant θ V.rank L N₀)
    (ENNReal.ofReal C) y (hC y hy) a
  have hP : 0 ≤ ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have h2 : ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ) ≤
      ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) :=
    (hC' t ht a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP))
  have hpow : (∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n =
      ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring
  calc absTheta V (pureT θ f g) (a * y)
      ≤ ENNReal.ofReal C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, colMajorant θ V.rank L N₀ (invPt V a ξ)) ^ n := h1
    _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (max C' 0 * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) ^ n := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (max C 0 * max C' 0 ^ n * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_pow (mul_nonneg (le_max_right _ _) hP),
          ← ENNReal.ofReal_mul (le_max_right _ _), mul_pow, hpow, mul_assoc]

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Φ : Mx D V.rank n → ℂ), Φ ∈ schwartzA θ V.rank n → ∀ {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (Ω C₀ : Set (GA D V)) (K : Subgroup (GA D V)) (c : ℝ), IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GA D V)) → 0 < c → (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → a⁻¹ * p * a ∈ C₀) → ∃ C : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ k ∈ K, absTheta V Φ (p * a * k) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hsub
  have hC₁ : IsCompact (C₀ * (K : Set (GA D V))) := hC₀.mul hK
  obtain ⟨-, m, f, g, hg, hdom⟩ := _root_.GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ V.rank n Φ hΦ
  have key := fun i => absTheta_pure_le D θ hθ V n (f i) (g i) (hg i) Xf Yf hW hc _ hC₁
  choose Ci hCi0 hCi using key
  refine ⟨∑ i, Ci i, fun p hp t ht a ha k hk => ?_⟩
  have hy : a⁻¹ * p * a * k ∈ C₀ * (K : Set (GA D V)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk
  have hsplit : p * a * k = a * (a⁻¹ * p * a * k) := by group
  have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  rw [hsplit]
  calc absTheta V Φ (a * (a⁻¹ * p * a * k))
      ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ∑ i, ‖pureT θ (f i) (g i) (invPt V (a * (a⁻¹ * p * a * k)) ξ)‖ₑ :=
        ENNReal.tsum_le_tsum fun ξ => hdom _
    _ = ∑ i, absTheta V (pureT θ (f i) (g i)) (a * (a⁻¹ * p * a * k)) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ i, ENNReal.ofReal (Ci i * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        Finset.sum_le_sum fun i _ => hCi i _ hy t ht a ha
    _ = ENNReal.ofReal ((∑ i, Ci i) * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hCi0 i) hP]

end GlobalTheory.CompanionTheory.SiegelTheta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat

theorem coordW_latV_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam v
  obtain ⟨t1, t2, t3, t4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := (hlam v).1
  have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
    (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mv := GlobalTheory.CompanionTheory.SW.WBox.map_coordW (Fv F v) hK (lam v) 1 1
  have hset : (latV b v : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) =
      (GlobalTheory.CompanionTheory.SW.WBox.eW (Fv F v) hK 1 1) ⁻¹'
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mv.measure_preimage_equiv, Measure.pi_pi]
  simp [(hlam v).2]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

def unitPermNonzero {E : Type} [Field E] (q : Eˣ) :
    ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) ≃ ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) where
  toFun X := ⟨fun a i => (q : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : (q : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  invFun X := ⟨fun a i => ((q⁻¹ : Eˣ) : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : ((q⁻¹ : Eˣ) : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  left_inv X := by
    apply Subtype.ext
    funext a i
    simp
  right_inv X := by
    apply Subtype.ext
    funext a i
    simp

theorem Th_ofE_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  intro F E _ _ _ _ φ A q y
  unfold Th
  rw [← Equiv.tsum_eq (unitPermNonzero q)
    (fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)))]
  refine tsum_congr fun X => ?_
  congr 1
  funext a i
  have hq : ((ofE q : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (AF F) (q : E) := rfl
  have hX : ((unitPermNonzero q X).1 a i) = (q : E) * X.1 a i := rfl
  rw [Units.val_mul, hq, hX, map_mul]
  ring

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawa
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, iw₁, lev⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ hcm n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, iw₂, good⟩ := _root_.GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good F E σ hcm n J hJ r X Y hW
  obtain ⟨K, hK, iw, -⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ hcm n J hJ r X Y hW
    K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ lev good
  exact ⟨K, hK, iw⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ue_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  intro F E _ _ _ _ _ σ _ J hJ h
  have hg : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) * JR (AF F) J *
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = JR (AF F) J := h.2
  have hx : ((ue (AF F) σ J h : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) 0 0 := by
    simp only [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have he := congrFun (congrFun hg 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, cT, JR, Matrix.transpose_apply,
    Matrix.map_apply, Fin.default_eq_zero, Fin.isValue] at he
  have hj : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have hu : IsUnit (inclR (F := F) (AF F) (J 0 0)) := (IsUnit.mk0 _ hj).map (inclR (F := F) (AF F))
  show ((1 : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ _ * _
  rw [hx, Units.val_one, ← Algebra.TensorProduct.one_def]
  apply hu.mul_left_cancel
  rw [mul_one]
  exact he.symm.trans (by ring)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

