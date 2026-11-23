module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductScaling
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem integrable_map_prod_of_compact {A B W : Type} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [T2Space A] [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] [T2Space B] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] (f : A × B → W) (hf : Measurable f) (φ : W → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (C₁ : Set A) (C₂ : Set B)
    (h₁ : IsCompact C₁) (h₂ : IsCompact C₂)
    (hs : ∀ᵐ y ∂μ, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ C₁ ∧ X ∈ C₂) (k : ℝ≥0) :
    Integrable φ (k • (μ.prod ν).map f) ∧
      ∫ v, φ v ∂(k • (μ.prod ν).map f) = (k : ℝ) * ∫ y, ∫ X, φ (f (y, X)) ∂ν ∂μ := by
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hc
  have hmeas : Measurable φ := hφ.measurable
  have hg : Measurable (φ ∘ f) := hmeas.comp hf
  have hPm : MeasurableSet (C₁ ×ˢ C₂) := h₁.measurableSet.prod h₂.measurableSet
  have hPfin : (μ.prod ν) (C₁ ×ˢ C₂) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top h₁.measure_lt_top h₂.measure_lt_top
  have hae : ∀ᵐ p ∂(μ.prod ν), ‖(φ ∘ f) p‖ ≤ (C₁ ×ˢ C₂).indicator (fun _ => |Bd|) p := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs
    filter_upwards [h] with p hp
    by_cases h0 : φ (f p) = 0
    · simp only [Function.comp, h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    · have hmem : p ∈ C₁ ×ˢ C₂ := hp p.2 h0
      rw [Set.indicator_of_mem hmem]
      exact (hBd _).trans (le_abs_self _)
  have hbound : Integrable ((C₁ ×ˢ C₂).indicator (fun _ => |Bd|)) (μ.prod ν) :=
    (integrable_indicator_iff hPm).2 (integrableOn_const hPfin.ne)
  have hI : Integrable (φ ∘ f) (μ.prod ν) := hbound.mono' hg.aestronglyMeasurable hae
  have hI2 : Integrable φ ((μ.prod ν).map f) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hf.aemeasurable).2 hI
  refine ⟨hI2.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_map hf.aemeasurable hmeas.aestronglyMeasurable,
    integral_prod (fun p => φ (f p)) hI]
  simp [NNReal.smul_def]

theorem vec_zero {K : Type} [CommRing K] {M n : ℕ} (u : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    vec u c X 0 = u • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → K) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vec]

theorem continuous_vec {K : Type} [TopologicalSpace K] [Zero K] {M n : ℕ} (u : K) (c : Fin n → K) :
    Continuous (fun X : Fin n → Fin M → K => vec u c X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · simp only [vec, Fin.cons_zero]; exact continuous_const
  · refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]; exact continuous_const
    · simp only [vec, Fin.cons_succ]
      exact continuous_apply_apply a' i'

theorem integrable_fibS_and_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm hD φ hφ hcs S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := hD.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨hKr, hKlc, hKsc, hKt2, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hD.hCM R
  have := hKr
  have := hKlc
  have := hKsc
  have := hKt2
  have hB1 : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := hBor 1 (M + 1)
  have hB2 : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hBor n M
  have hB3 : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hBor (n + 1) (M + 1)
  have hJ₁ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J hD.hJ t hD.ht
  obtain ⟨hTG, -, hHsc, hHt2, hHB, hact⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hD.hCM (M + 1) (blockOne (algebraMap F E t) J) hJ₁ R
  have := hTG
  have := hHsc
  have := hHt2
  have := hHB
  obtain ⟨hcont, hone, hmul, -⟩ := hact (n + 1)
  have k1 := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hD.hCM (M + 1) 1 (blockOne (algebraMap F E t) J) hJ₁ R hD.hR d b lam
    hD.hlam m₁ hD.hm₁
  have k2 := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hD.hCM M n J hD.hJ R hD.hR d b lam hD.hlam m' hD.hm'
  obtain ⟨-, hlf₁, -, -, -, hgram⟩ := k1
  obtain ⟨-, hlf₂, -, -, -, -⟩ := k2
  set α : Rˣ := a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) with hα
  set c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) with hc
  set S' := schur R σ t a S with hS'
  set μ₁ := m₁ (hermScal R σ (algebraMap F R t)) with hμ₁
  set u : R ⊗[F] E := (α : R) ⊗ₜ[F] (1 : E) with hu
  set u' : R ⊗[F] E := ((α⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) with hu'
  have huu : u * u' = 1 := by
    simp [hu, hu', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have := hlf₁ (hermScal R σ (algebraMap F R t))
  have := hlf₂ S'
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec u c p.2)
  have hfm : Measurable f :=
    hcont.measurable.comp ((hD.hs.comp measurable_fst).prodMk
      ((continuous_vec u c).measurable.comp measurable_snd))
  have hfib : fibS σ J t m₁ m' s B₀ a κ₁ cm S = (κ₁ α * cm α ^ n) • (μ₁.prod (m' S')).map f := by
    unfold fibS
    rw [Set.indicator_of_mem hS]
  set C := tsupport φ with hC
  have hCc : IsCompact C := hcs
  let e₁ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin 1 → Fin (M + 1) → R ⊗[F] E :=
    fun Z _ i => Z 0 i * u'
  have he₁ : Continuous e₁ := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact (continuous_apply_apply (0 : Fin (n + 1)) i).mul continuous_const
  have hC₁ : IsCompact (e₁ '' C) := hCc.image he₁
  obtain ⟨C', hC'c, hC'⟩ := hD.hcpt (e₁ '' C) hC₁
  let e₂ : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun q => actW R σ (blockOne (algebraMap F E t) J) q.1⁻¹ q.2
  have he₂ : Continuous e₂ := hcont.comp ((continuous_fst.inv).prodMk continuous_snd)
  let e₃ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E :=
    fun Z j i => Z j.succ i.succ
  have he₃ : Continuous e₃ := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    exact continuous_apply_apply j.succ i.succ
  have hC₂ : IsCompact (e₃ '' (e₂ '' (C' ×ˢ C))) := ((hC'c.prod hCc).image he₂).image he₃
  have hsupp : ∀ᵐ y ∂μ₁, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ e₁ '' C ∧ X ∈ e₃ '' (e₂ '' (C' ×ˢ C)) := by
    filter_upwards [hgram (hermScal R σ (algebraMap F R t))] with y hy X hne
    have hZ : f (y, X) ∈ C := subset_tsupport _ hne
    have hy0 : e₁ (f (y, X)) = y := by
      have h1 := hD.hsec y hy
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have h2 : (f (y, X)) 0 = u • y 0 := by
        conv_rhs => rw [← h1]
        simp only [f, actW, actTup, vec_zero, Matrix.mulVec_smul]
      simp only [e₁, h2, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm u, mul_assoc, huu, mul_one]
    have hy1 : y ∈ e₁ '' C := ⟨_, hZ, hy0⟩
    have hsy : s y ∈ C' := hC' y hy1 hy
    have hv : e₂ (s y, f (y, X)) = vec u c X := by
      simp only [e₂, f]
      rw [← hmul, inv_mul_cancel, hone]
    refine ⟨hy1, vec u c X, ⟨(s y, f (y, X)), ⟨hsy, hZ⟩, hv⟩, ?_⟩
    funext j i
    simp [e₃, vec]
  rw [hfib]
  exact integrable_map_prod_of_compact μ₁ (m' S') f hfm φ hφ hcs _ _ hC₁ hC₂ hsupp _

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUniqueness
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def tl {K : Type} {M n : ℕ} (Y : Fin (n + 1) → Fin (M + 1) → K) : Fin n → Fin M → K :=
  fun j i => Y j.succ i.succ

theorem tl_vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    tl (vec α c X) = X := by
  funext j i
  simp [tl, vec]

theorem continuous_tl {K : Type} [TopologicalSpace K] {M n : ℕ} :
    Continuous (tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  exact (continuous_apply i.succ).comp (continuous_apply j.succ)

theorem continuous_vec {K : Type} [Zero K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => vec p.1 p.2.1 p.2.2) := by
  refine continuous_pi fun a => ?_
  refine Fin.cases ?_ (fun j => ?_) a
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [vec] using continuous_fst
    · simpa [vec] using continuous_const
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.1 j) :=
        (continuous_apply j).comp (continuous_fst.comp continuous_snd)
      simpa [vec] using h
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.2 j k) :=
        (continuous_apply k).comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
      simpa [vec] using h

theorem actW_vec_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {N n : ℕ}
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (J' : Matrix (Fin (N + 1)) (Fin (N + 1)) E)
    (h : HA R σ J') (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin N → R ⊗[F] E) (i : Fin (N + 1)) :
    actW R σ J' h (vec A c X) 0 i =
      actW R σ J' h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) 0 i * A := by
  have hv : (Fin.cons A (fun _ => 0) : Fin (N + 1) → R ⊗[F] E) = A • Fin.cons 1 (fun _ => 0) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  simp only [actW, actTup, vec, Fin.cons_zero]
  rw [hv, Matrix.mulVec_smul]
  simp [mul_comm]

theorem continuous_tmul_one {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun α : R => α ⊗ₜ[F] (1 : E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have h : Continuous (fun α : R => α • (1 : R ⊗[F] E)) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  convert h using 2 with α
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem cont_double : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Unt σ R n)) := by
  open scoped Pointwise in
   intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
   haveI iTR : IsTopologicalRing R := D.hR.1
   haveI iLC : LocallyCompactSpace R := D.hR.2.1
   haveI iSC : SecondCountableTopology R := D.hR.2.2.1
   haveI iT2 : T2Space R := D.hR.2.2.2.1
   have hval : IsOpenEmbedding (Units.val : Rˣ → R) := D.hR.2.2.2.2.2.2.1
   have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
   obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
   haveI := kTR
   haveI := kLC
   haveI := kSC
   haveI := kT2
   haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
   obtain ⟨eLC, eSC, eT2, eB, hlift⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R n
   haveI := eLC
   haveI := eSC
   haveI := eT2
   haveI := eB
   obtain ⟨g, hgc, hg⟩ := hlift M J D.hJ
   obtain ⟨gTG, gLC, gSC, gT2, gB, hactall⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
   haveI := gTG
   haveI := gLC
   haveI := gSC
   haveI := gT2
   haveI := gB
   obtain ⟨hact, hact1, hactm, -⟩ := hactall (n + 1)
   obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ D.hCM R d b lam D.hlam
   haveI := hW n M
   haveI := hH n
   obtain ⟨hUo, -, -, -, hbd', -⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
   obtain ⟨-, hloc₁, -, -, -, hgram₁⟩ :=
     _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
   haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := kB n M
   haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := kB 1 (M + 1)
   have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam n M) (gramR R σ J) Subtype.val
       (g ⁻¹' Unt σ R n) (coordHerm R σ b lam n) (Unt σ R n) m' := by
     have he : g ⁻¹' Unt σ R n = {X | IsUnit (gramR R σ J X).det} := by
       ext X
       simp only [Set.mem_preimage, Unt, Set.mem_setOf_eq, hg X]
     rw [he]
     exact D.hm'

   have hCt : ∀ L : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact L →
       ∃ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C ∧ ∀ h ∈ L, ∀ A c X,
         φ (actW R σ _ h (vec A c X)) ≠ 0 → X ∈ C := by
     intro L hL
     refine ⟨(fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
       tl (actW R σ _ p.1⁻¹ p.2)) '' (L ×ˢ tsupport φ), ?_, ?_⟩
     · refine (hL.prod hφc).image ?_
       exact continuous_tl.comp (hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd))
     · intro h hh A c X hne
       refine ⟨(h, actW R σ _ h (vec A c X)), ⟨hh, subset_tsupport _ hne⟩, ?_⟩
       simp only
       rw [← hactm, inv_mul_cancel, hact1, tl_vec]
   have cT := continuous_tmul_one (F := F) (E := E) R

   let G : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) × HermR R σ n → ℝ :=
     fun q => ∫ X, φ (actW R σ _ q.1.1 (vec (q.1.2.1 ⊗ₜ[F] (1 : E)) q.1.2.2 X)) ∂(m' q.2)
   have hG : ∀ q, q.2 ∈ Unt σ R n → ContinuousAt G q := by
     intro q hq
     obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds q.1.1
     obtain ⟨C, hC, hCv⟩ := hCt L hLc
     have hWo : IsOpen (interior L ×ˢ (Set.univ : Set (R × (Fin n → R ⊗[F] E)))) :=
       isOpen_interior.prod isOpen_univ
     have hcΦ : Continuous (fun p : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) ×
         (Fin n → Fin M → R ⊗[F] E) =>
         φ (actW R σ _ p.1.1 (vec (p.1.2.1 ⊗ₜ[F] (1 : E)) p.1.2.2 p.2))) := by
       refine hφ.comp (hact.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
       exact continuous_vec.comp ((cT.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))).prodMk
         ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
     have hj := GlobalTheory.CompanionTheory.SW.FibreJointCont.continuousOn_fibre_integral (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) _ (coordW R b lam n M)
       (coordHerm R σ b lam n) (gramR R σ J) g Subtype.val Subtype.val_injective hgc hg (Unt σ R n) hUo m' hfam
       (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E))
       (interior L ×ˢ Set.univ)
       (fun p X => φ (actW R σ _ p.1 (vec (p.2.1 ⊗ₜ[F] (1 : E)) p.2.2 X))) hcΦ.continuousOn hWo C hC
       (by
         intro p hp v hv
         by_contra hne
         exact hv (hCv p.1 (interior_subset hp.1) _ _ _ hne))
     have hmem : ((interior L ×ˢ Set.univ) ×ˢ Unt σ R n) ∈ 𝓝 q :=
       (hWo.prod hUo).mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hLn, trivial⟩, hq⟩
     exact hj.continuousAt hmem
   rintro ⟨α₀, c₀, S₀⟩ ⟨hα₀, -, hS₀⟩
   refine ContinuousAt.continuousWithinAt ?_
   obtain ⟨N, hNn, hNs, hNc⟩ := local_compact_nhds (hval.isOpen_range.mem_nhds hα₀)
   have hUc : IsCompact ((Units.val : Rˣ → R) ⁻¹' N) := by
     rw [hval.isInducing.isCompact_iff, Set.image_preimage_eq_of_subset hNs]
     exact hNc
   have hNi : IsCompact ((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) :=
     hUc.inv.image Units.continuous_val
   obtain ⟨Dc, hDn, hDs, hDc⟩ := local_compact_nhds (hUo.mem_nhds hS₀)
   let C₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) :=
     (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
       scl (p.1 ⊗ₜ[F] (1 : E)) (fun _ : Fin 1 => p.2 0)) ''
         (((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) ×ˢ tsupport φ)
   have hC₁c : IsCompact C₁ := by
     refine (hNi.prod hφc).image ?_
     refine continuous_pi fun _ => continuous_pi fun i => ?_
     have h1 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.2 0 i) :=
       (continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)
     have h2 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.1 ⊗ₜ[F] (1 : E)) :=
       cT.comp continuous_fst
     exact h1.mul h2
   obtain ⟨C', hC'c, hC'⟩ := D.hcpt C₁ hC₁c
   obtain ⟨C₂, hC₂c, hC₂⟩ := hCt C' hC'c
   obtain ⟨cD, hcD⟩ := hbd' C₂ Dc hC₂c hDc hDs
   obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hφc
   have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
   haveI := hloc₁ (hermScal R σ (algebraMap F R t))
   have eU : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Unt σ R n :=
     (continuous_snd.comp continuous_snd).continuousAt (hUo.mem_nhds hS₀)
   have eD : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Dc :=
     (continuous_snd.comp continuous_snd).continuousAt hDn
   have eN : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.1 ∈ N :=
     continuous_fst.continuousAt hNn
   have hmeas : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
       AEStronglyMeasurable (fun y₀ => G ((s y₀, z.1, z.2.1), z.2.2))
         (m₁ (hermScal R σ (algebraMap F R t))) := by
     filter_upwards [eU] with z hz
     have hc : Continuous (fun h : HA R σ (blockOne (algebraMap F E t) J) => G ((h, z.1, z.2.1), z.2.2)) := by
       refine continuous_iff_continuousAt.2 fun h => ?_
       refine ContinuousAt.comp (g := G) (f := fun h => ((h, z.1, z.2.1), z.2.2)) (hG _ hz) ?_
       exact (((continuous_id.prodMk continuous_const)).prodMk continuous_const).continuousAt
     exact (hc.measurable.comp D.hs).aestronglyMeasurable
   have hcont : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
       ContinuousAt (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => G ((s y₀, z.1, z.2.1), z.2.2))
         (α₀, c₀, S₀) := by
     refine Filter.Eventually.of_forall fun y₀ => ?_
     refine ContinuousAt.comp (g := G)
       (f := fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => ((s y₀, z.1, z.2.1), z.2.2)) (hG _ hS₀) ?_
     exact ((continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
       (continuous_snd.comp continuous_snd)).continuousAt
   have hbound : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
       ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
         ‖G ((s y₀, z.1, z.2.1), z.2.2)‖ ≤ C₁.indicator (fun _ => Bd * (cD : ℝ)) y₀ := by
     filter_upwards [eN, eD] with z hzN hzD
     filter_upwards [hgram₁ (hermScal R σ (algebraMap F R t))] with y₀ hy₀
     obtain ⟨u, hu⟩ := hNs hzN
     have hsec := D.hsec y₀ hy₀
     have hvan : ∀ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ≠ 0 → y₀ ∈ C₁ := by
       intro X hne
       refine ⟨(((u⁻¹ : Rˣ) : R), actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)),
         ⟨⟨u⁻¹, ?_, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
       · simpa [Set.mem_inv, hu] using hzN
       · funext a i
         have ha : a = 0 := Subsingleton.elim _ _
         subst ha
         simp only [scl]
         rw [actW_vec_zero, hsec, ← hu, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv,
           mul_one, ← Algebra.TensorProduct.one_def, mul_one]
     by_cases hy : y₀ ∈ C₁
     · have h2 : s y₀ ∈ C' := hC' y₀ hy hy₀
       have hvanX : ∀ X, X ∉ C₂ → φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) = 0 :=
         fun X hX => by_contra fun hne => hX (hC₂ _ h2 _ _ _ hne)
       rw [Set.indicator_of_mem hy]
       change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
       rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanX]
       have hfin : m' z.2.2 C₂ < ∞ := (hcD _ hzD).trans_lt ENNReal.coe_lt_top
       refine (norm_setIntegral_le_of_norm_le_const hfin (fun X _ => hBd _)).trans ?_
       refine mul_le_mul_of_nonneg_left ?_ hBd0
       have := ENNReal.toReal_mono ENNReal.coe_ne_top (hcD _ hzD)
       simpa [Measure.real] using this
     · rw [Set.indicator_of_notMem hy]
       have h0 : (fun X => φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X))) = 0 :=
         funext fun X => by_contra fun hne => hy (hvan X hne)
       change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
       rw [h0]
       simp
   have hint : Integrable (C₁.indicator (fun _ => Bd * (cD : ℝ)))
       (m₁ (hermScal R σ (algebraMap F R t))) :=
     (integrable_indicator_iff hC₁c.isClosed.measurableSet).2 (integrableOn_const hC₁c.measure_lt_top.ne)
   exact continuousAt_of_dominated hmeas hbound hint hcont
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresInvariant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreInv

theorem map_actW_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actW R σ J h := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hop := (_root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR).isOpen_range
    have hBe : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext T
      simp [B, IsUnit]
    rw [hBe]
    exact hop.preimage (Continuous.matrix_det continuous_subtype_val)
  have hU : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, hgf]
  have hm' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hU]
    exact hm
  have hgi : ∀ X, g (e X) = (Homeomorph.refl (HermR R σ n)) (g X) := by
    intro X
    apply Subtype.ext
    show (g (actW R σ J h X) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = g X
    rw [← hgf, ← hgf, hgr]
  have ht := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ (HermR R σ n) _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hgf _ (gramR R σ J) g hgc hgf e (Homeomorph.refl _) hgi B hB m hm'
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simpa using Measure.map_id (μ := ν)
  have hμm : μ.map e = μ := _root_.GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq F E σ hσ M J hJ R hR n μ hμ h
  rw [himg, hνm, hμm, ← hU] at ht
  exact (_root_.GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n μ ν _ hμ hν ht m hm S)

end GlobalTheory.CompanionTheory.SW.FibreInv
end
end

