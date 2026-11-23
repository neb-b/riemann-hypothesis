module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0668
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforward
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_UsetF_eq_MidF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hCM := D.hCM
  have hlam := D.hlam
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id D.hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨hK, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, hlf1, -, -, -, hae1⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hCM (M + 1) 1 _ hJ' R D.hR d b lam hlam m₁ D.hm₁
  obtain ⟨hm, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ hCM M n J D.hJ R D.hR d b lam hlam m' D.hm'
  obtain ⟨-, -, h₃, -, h₅, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 1) _ hJ' R
  have hc := (hact (n + 1)).1
  haveI := hBorel n M
  haveI := hBorel (n + 1) (M + 1)
  haveI := hBorel 1 (M + 1)
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordW R b lam n M) := inferInstance
  haveI : SigmaFinite (m₁ (hermScal R σ (algebraMap F R t))) := inferInstance
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : SFinite (Measure.pi fun _ : Fin n => coordK R b lam) := inferInstance
  have hB : MeasurableSet B₀ := D.hB₀.measurableSet
  rw [_root_.GlobalTheory.CompanionTheory.SW.StageF.Unfold1F.first_step_free F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ]
  unfold MidF
  refine setLIntegral_congr_fun hB fun x hx => ?_
  refine congrArg _ ?_
  set f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → (Fin n → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ :=
    fun y₀ c X => φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) with hfdef
  have hf : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      f p.1 p.2.1 p.2.2 := by
    have hcm : Measurable (fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) p.1 p.2) := by
      haveI : SecondCountableTopology (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J)) := inferInstance
      haveI : OpensMeasurableSpace (HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
        Prod.opensMeasurableSpace
      exact hc.measurable
    have hg : Measurable (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        ((s p.1, vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) p.2.1 p.2.2) :
          HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))) :=
      (D.hs.comp measurable_fst).prodMk
        ((Unfold.measurable_vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))).comp measurable_snd)
    exact hφ.comp (hcm.comp hg)
  have hae : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ)
          (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) =
        ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, f y₀ c X ∂(m' S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
    filter_upwards [hae1 (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    exact _root_.GlobalTheory.CompanionTheory.SW.StageF.Fibre.chi_at_fibreF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  rw [lintegral_congr_ae hae]
  have key := Unfold.swap_through_fibres (m₁ (hermScal R σ (algebraMap F R t)))
    (Measure.pi fun _ => coordK R b lam) (coordW R b lam n M) (coordHerm R σ b lam n)
    {X | LinearIndependent (R ⊗[F] E) X} Set.univ MeasurableSet.univ m' hm (fun S hS => absurd (Set.mem_univ S) hS)
    D.hm'.2.1 f hf
  simp only [Measure.restrict_univ] at key
  exact key

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionUnique
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.FoldF

theorem foldF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (_root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (_root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermSplit.herm_split F E σ hσ R d b lam hlam n
  obtain ⟨m₀, D₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hs0c, hacS, hcvc, hschc, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hBopen : IsOpen (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := D.hB₀.preimage hs0c
  have hGon0 := _root_.GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.fibre_measure_extension_symmetric F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hGoff0 : ∀ S, S ∉ BsetF R σ B₀ →
      ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibSF
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ BsetF R σ B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (BsetF R σ B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => Fold.corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ := h
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S', Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨Fold.qM R σ t (cr r), Fold.qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      Pint σ J t m₁ m' s φ (u : R) z.1 z.2
    have hf : Measurable f :=
      hmeas.comp (measurable_const.prodMk measurable_id)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [Fold.schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨Fold.qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            Fold.qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (Fold.qM R σ t) h1)
        rw [h3]
      have hB : e (x, r, S'') ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := by
        show s0 R _ ∈ B₀
        rw [h0]
        exact hx
      rw [hGon _ hB, h0, h1, h2, ← hu]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := rfl
  rw [hL]
  unfold MidF
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.StageF.FoldF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugation
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc GlobalTheory.CompanionTheory.FourierN
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n : ℕ}

theorem adj_mul_sq (x y : Mx D n n) : adj (x * y) = adj y * adj x := adj_mul x y

theorem rat_mul_sq (x y : Matrix (Fin n) (Fin n) D.host.E) : (rat (x * y) : Mx D n n) = rat x * rat y := rat_mul x y

theorem rat_one_sq : (rat (1 : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n) = 1 :=
  Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))

theorem adj_one_sq : adj (1 : Mx D n n) = 1 := by
  rw [← rat_one_sq, ← rat_conjTranspose, Matrix.conjTranspose_one]

theorem rat_gl_mul_inv (a : GL (Fin n) D.host.E) : (rat a.1 * rat (a⁻¹).1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show a.1 * (a⁻¹).1 = 1 from by simp, rat_one_sq]

theorem rat_gl_inv_mul (a : GL (Fin n) D.host.E) : (rat (a⁻¹).1 * rat a.1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show (a⁻¹).1 * a.1 = 1 from by simp, rat_one_sq]

def congH (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) : hermA D n :=
  ⟨rat u * b.1 * adj (rat u), by
    show adj (rat u * b.1 * adj (rat u)) = _
    have hb : adj b.1 = b.1 := b.2
    rw [adj_mul_sq, adj_mul_sq, adj_adj, hb, mul_assoc]⟩

theorem congH_val (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) :
    (congH u b).1 = rat u * b.1 * adj (rat u) := rfl

theorem congH_cancel {u v : Matrix (Fin n) (Fin n) D.host.E} (h : (rat u * rat v : Mx D n n) = 1) (b : hermA D n) :
    congH u (congH v b) = b := by
  apply Subtype.ext
  have h' : (adj (rat v) * adj (rat u) : Mx D n n) = 1 := by rw [← adj_mul_sq, h, adj_one_sq]
  rw [congH_val, congH_val]
  calc rat u * (rat v * b.1 * adj (rat v)) * adj (rat u)
      = (rat u * rat v) * b.1 * (adj (rat v) * adj (rat u)) := by simp only [mul_assoc]
    _ = b.1 := by rw [h, h', one_mul, mul_one]

theorem continuous_congH (u : Matrix (Fin n) (Fin n) D.host.E) : Continuous (congH (D := D) u) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem congH_rat (u : Matrix (Fin n) (Fin n) D.host.E) {b : hermA D n} (hb : b ∈ ratHerm D n) : congH u b ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ := hb
  have hη' : b.1 = rat η := hη.symm
  refine ⟨u * η * uᴴ, ?_⟩
  show rat (u * η * uᴴ) = rat u * b.1 * adj (rat u)
  rw [rat_mul_sq, rat_mul_sq, rat_conjTranspose, hη']

def tauH (a : GL (Fin n) D.host.E) : hermA D n ≃ₜ+ hermA D n where
  toFun := congH (a⁻¹).1
  invFun := congH a.1
  left_inv := congH_cancel (rat_gl_mul_inv a)
  right_inv := congH_cancel (rat_gl_inv_mul a)
  map_add' b c := by
    apply Subtype.ext
    show rat (a⁻¹).1 * (b.1 + c.1) * adj (rat (a⁻¹).1) = rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1) + rat (a⁻¹).1 * c.1 * adj (rat (a⁻¹).1)
    rw [mul_add, add_mul]
  continuous_toFun := continuous_congH _
  continuous_invFun := continuous_congH _

theorem tauH_apply (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b = congH (a⁻¹).1 b := rfl

theorem tauH_rat (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b ∈ ratHerm D n ↔ b ∈ ratHerm D n := by
  refine ⟨fun h => ?_, fun h => congH_rat _ h⟩
  have := congH_rat a.1 h
  rwa [tauH_apply, congH_cancel (rat_gl_mul_inv a)] at this

theorem exists_levi_rat (a : GL (Fin n) D.host.E) :
    ∃ q : G D n, q ∈ GF D n ∧ mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
  obtain ⟨q, hq⟩ := exists_levi (D := D) (n := n) (Matrix.GeneralLinearGroup.map (incA D) a)
  have hq' : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    rw [hq, ← map_inv]
    rfl
  refine ⟨q, ?_, hq'⟩
  have e1 : a.1 * (a⁻¹).1 = 1 := by simp
  have e2 : (a⁻¹).1 * a.1 = 1 := by simp
  have e3 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e4 : a.1ᴴ * ((a⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  let x : GL (Fin (n + n)) D.host.E := ⟨blk4 a.1 0 0 ((a⁻¹).1)ᴴ, blk4 (a⁻¹).1 0 0 a.1ᴴ,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e3]; exact block_matrix_one,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e2, e4]; exact block_matrix_one⟩
  have hm : x.1.map (incA D) = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    simp only [x, blk4_map_alt]
    rw [Matrix.map_zero _ (map_zero _)]
    rfl
  refine ⟨x, ?_, Units.ext (hm.trans hq'.symm)⟩
  apply rat_injective (D := D)
  have h2 : adj (mat q) * JR (AF D.host.F) (Jst D n) * mat q = JR (AF D.host.F) (Jst D n) := q.2
  rw [hq', ← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

theorem nb_levi {nb : hermA D n → G D n} (hnb : IsNMap nb) (a : GL (Fin n) D.host.E) {q : G D n}
    (hq : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))) (b : hermA D n) : nb b * q = q * nb (tauH a b) := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb b) * mat q = mat q * mat (nb (tauH a b))
  rw [hnb, hnb, hq, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, tauH_apply, congH_val]
  have e : rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = b.1 * adj (rat (a⁻¹).1) := by
    rw [← mul_assoc, ← mul_assoc, rat_gl_mul_inv, one_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e]

theorem trace_cg (a : GL (Fin n) D.host.E) (β : HermE D n) (b : hermA D n) :
    Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) := by
  have h1 : ((cg a β).1.map (incA D) : Mx D n n) = adj (rat a.1) * rat β.1 * rat a.1 := by
    show rat (_ * β.1 * a.1) = _
    rw [rat_mul_sq, rat_mul_sq]
    rfl
  have h2 : (adj (rat (a⁻¹).1) * adj (rat a.1) : Mx D n n) = 1 := by rw [← adj_mul_sq, rat_gl_mul_inv, adj_one_sq]
  show Matrix.trace ((cg a β).1.map (incA D) * (tauH a b).1 : Mx D n n) = Matrix.trace (rat β.1 * b.1 : Mx D n n)
  rw [h1, tauH_apply, congH_val]
  have e : adj (rat a.1) * rat β.1 * rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) =
      adj (rat a.1) * ((rat β.1 * b.1) * adj (rat (a⁻¹).1)) := by
    calc _ = adj (rat a.1) * rat β.1 * (rat a.1 * rat (a⁻¹).1) * b.1 * adj (rat (a⁻¹).1) := by simp only [mul_assoc]
      _ = _ := by rw [rat_gl_mul_inv]; simp only [mul_assoc, mul_one]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h2, mul_one]


set_option synthInstance.maxHeartbeats 400000 in
theorem fc_levi : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F →
    LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 →
    ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  intro D n ψ hψ F _ hinv nb lam 𝓖 hC a β
  obtain ⟨hnb, hlam, hFD, hvol⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨q, hqF, hq⟩ := exists_levi_rat (D := D) a
  refine ⟨q, fun g => ?_⟩
  let f : hermA D n → ℂ := fun c =>
    F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))
  have hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x := by
    intro γ hγ x
    have e1 : F (nb (γ + x) * g) = F (nb x * g) := by
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1) := by
      rw [show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]
    show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)
    rw [e1, e2]
  have key := mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf
  unfold fc
  refine Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key
  show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) =
    F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))
  rw [trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroup
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem rat_maps_mem_GF : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  intro D n ρ p hn M
  refine ⟨fun ξ => GlobalTheory.CompanionTheory.PcB.sh_rat M ξ, fun ξ => GlobalTheory.CompanionTheory.PcB.nzx_rat M 0 (zero_mem _) ξ, fun z hz => ?_⟩
  have h := GlobalTheory.CompanionTheory.PcB.nzx_rat M z hz 0
  rwa [GlobalTheory.CompanionTheory.PcB.rat_zero'] at h

end GlobalTheory.CompanionTheory.FJE
end
end

