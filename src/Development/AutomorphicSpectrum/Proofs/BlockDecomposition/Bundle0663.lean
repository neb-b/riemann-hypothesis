module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentities
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

open GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

theorem exists_scale_cover {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fin n → Fin M → Fv F v ⊗[F] E)) (hC : IsCompact C) :
    ∃ (c : F) (hc : c ≠ 0), C ⊆ latV (scaleB b c hc) v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := algebraMap F (Fv F v) π with hp
  have hval : Valued.v p = WithZero.exp (-1 : ℤ) := by
    have h0 : Valued.v (algebraMap F (Fv F v) π) = v.valuation F π :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
    rw [hp, h0, hπ]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hlt : Valued.v p < 1 := by
    rw [hval]
    decide
  have hpO : p ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hlt.le
  have hnorm : ‖p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => p ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hmem : ∀ (k : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      X ∈ latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v ↔
        ∀ a i l, p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          v.adicCompletionIntegers F := by
    intro k X
    simp only [latV, Set.mem_setOf_eq, repr_scaleB, map_pow, hp]
  let U : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun k => latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d (scaleB b (π ^ k) (pow_ne_zero k hπ0)) n M).2.2.2.1 v).2)
  have hcov : C ⊆ ⋃ k, U k := by
    intro X _
    have h1 : ∀ a i l, ∀ᶠ k : ℕ in Filter.atTop,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro a i l
      have h2 : Filter.Tendsto
          (fun k : ℕ => p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
          Filter.atTop (𝓝 0) := by
        simpa using hlim.mul_const ((Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
      exact h2 (hOopen.mem_nhds (zero_mem _))
    have h3 : ∀ᶠ k : ℕ in Filter.atTop, ∀ a i l,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun l => h1 a i l
    obtain ⟨k, hk⟩ := h3.exists
    exact Set.mem_iUnion.2 ⟨k, (hmem k X).2 hk⟩
  have hmono : Monotone U := monotone_nat_of_le_succ fun k X hX => by
    refine (hmem (k + 1) X).2 fun a i l => ?_
    have h := (hmem k X).1 hX a i l
    rw [pow_succ', mul_assoc]
    exact mul_mem hpO h
  obtain ⟨k, hk⟩ := hC.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨π ^ k, pow_ne_zero k hπ0, hk⟩

theorem fibre_compact_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT hSW d b laminf lam hinf hv v m hm C hC
  classical
  obtain ⟨c, hc, hCc⟩ := exists_scale_cover σ hcm b n M v C hC
  set b' := scaleB b c hc with hb'
  have hrV : ∀ w, IsLocR (Fv F w) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI : ∀ w, BorelSpace (Fv F w) := fun _ => ⟨rfl⟩
  obtain ⟨k, hk0, hk⟩ := coord_rescale σ hcm J (Fv F v) (hrV v) b b' (lam v) (hv v).1 n m hm
  have hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm (Ainf F) _ b' laminf hinf.1
  obtain ⟨minf, hminf⟩ := _root_.GlobalTheory.ArchGramFibre.exists_fibreFamily F E σ hcm M n J hJ (coordW (Ainf F) b' laminf n M)
    (coordHerm (Ainf F) σ b' laminf n) (hWi n M) (hHi n)
  have hfV : ∀ w : HeightOneSpectrum (𝓞 F), ∃ fib : HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E),
      IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M) (coordHerm (Fv F w) σ b' (lam w) n) fib := fun w => by
    have := PI.VolStabS.secondCountable_Fv F w
    have := PI.VolStabS.locallyCompact_Fv F w
    obtain ⟨-, hWv, hHv⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm (Fv F w) _ b' (lam w) (hv w).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J w n hcm hJ _ _ (hWv n M) (hHv n)
  choose m₀ hm₀ using hfV
  let m₂ : ∀ w : HeightOneSpectrum (𝓞 F), HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E) :=
    Function.update m₀ v (fun S => k • m S)
  have hm₂v : m₂ v = fun S => k • m S := Function.update_self _ _ _
  have hm₂ : ∀ w, IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M)
      (coordHerm (Fv F w) σ b' (lam w) n) (m₂ w) := fun w => by
    by_cases h : w = v
    · subst h
      rw [hm₂v]
      exact hk
    · have : m₂ w = m₀ w := Function.update_of_ne h _ _
      rw [this]
      exact hm₀ w
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := _root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hcm M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE := hSW d b' laminf lam hinf hv μ₁ 𝓕₁ hμ₁ h𝓕₁ minf m₂ hminf hm₂
  have h1 : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) < ⊤ := by
    have h2 : m₂ v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := hE.1 v
    rwa [hm₂v] at h2
  have h3 : m (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
    by_contra hx
    have hs : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) =
        (k : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [Measure.smul_apply]
      rfl
    rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0)] at h1
    exact lt_irrefl _ h1
  exact (measure_mono hCc).trans_lt h3

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_integral_mul_of_bdd {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    {f : X → Y → ℂ} (hf : Continuous fun w : X × Y => f w.1 w.2) {B : ℝ} (hB : ∀ x y, ‖f x y‖ ≤ B)
    {g : Y → ℂ} (hg : Integrable g ν) : Continuous fun x => ∫ y, f x y * g y ∂ν := by
  refine continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_)
    (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)
  · have h1 : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    exact h1.aestronglyMeasurable.mul hg.1
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)
  · have h1 : Continuous fun x => f x y := hf.comp (continuous_id.prodMk continuous_const)
    exact h1.mul continuous_const

theorem integral_integral_mul_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {F : X × Y → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {B : ℝ} (hB : ∀ w, ‖F w‖ ≤ B)
    {a : X → ℂ} {c : Y → ℂ} (ha : Integrable a μ) (hc : Integrable c ν) :
    ∫ x, (∫ z, F (x, z) * c z ∂ν) * a x ∂μ = ∫ w, F w * (a w.1 * c w.2) ∂(μ.prod ν) := by
  have hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν) :=
    (ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)
  rw [integral_prod _ hI]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  refine Matrix.ext fun i j => ?_
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  refine Matrix.ext fun i j => ?_
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  refine Matrix.ext fun i j => ?_
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous fun w : Mx D r p × Mx D s p => rowJ w.1 w.2 := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simp only [rowJ, Fin.addCases_left]
    exact continuous_fst.matrix_elem a j
  | right b =>
    simp only [rowJ, Fin.addCases_right]
    exact continuous_snd.matrix_elem b j

theorem continuous_th_one {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {b₀ : HermE D ρ}
    {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) : Continuous (Ω 1) :=
  hΩ.cont.comp (continuous_const.prodMk continuous_id)

theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf

theorem stepTotal : ProdTh → ProdMeas → StepTotal := by
  intro hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth
  obtain ⟨B, hB⟩ := hbd
  have hμ := hM D r s p μr Fr μs Fs μ F hr hs h
  subst hμ
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1
  haveI : FirstCountableTopology (Mx D r p) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1
  haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1
  haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
  haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  have hcJ := continuous_rowJ (D := D) (r := r) (s := s) (p := p)
  have hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2) := hu.comp hcJ
  have key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0 := by
    intro Ωr Ωs hΩr hΩs
    have hT := hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs
    have h0 := horth _ hT
    have hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y)) :=
      hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul
        ((continuous_th_one hΩs).comp continuous_rowB)))
    rw [integral_map hcJ.aemeasurable hm.aestronglyMeasurable] at h0
    rw [integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2))
      hcF.aestronglyMeasurable (fun w => hB _)
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1)))
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1)))]
    simpa only [rowT_rowJ, rowB_rowJ, map_mul] using h0
  have hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0 := by
    intro Ωs hΩs
    have hi : Integrable (fun z => conj (Ωs 1 z)) μs :=
      integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))
    refine congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)
    · exact continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi
    · refine ⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)
      show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact fun Ωr hΩr => key Ωr Ωs hΩr hΩs
  have hz : ∀ x, (fun z => u (rowJ x z)) = 0 := fun x =>
    Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩
      fun Ωs hΩs => hv Ωs hΩs x
  funext y
  rw [← rowJ_rowT_rowB y]
  exact congrFun (hz (rowT y)) (rowB y)

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.TupCovolume

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SiegelND.DxN PositivityTheory.SiegelWeilFormula.KWhit.MeasP
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → E) : Fin n × (Fin M × Fin d) → F :=
  fun p => b.repr (Y p.1 p.2.1) p.2.2

def ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) : Fin n → Fin M → E :=
  fun a i => ∑ l, c (a, (i, l)) • b l

theorem ratCoord_ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) :
    ratCoord b (ofCoord b c) = c := by
  funext p
  obtain ⟨a, i, l⟩ := p
  simp [ratCoord, ofCoord, Finsupp.single_apply]

theorem ratCoord_injective {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Function.Injective (ratCoord (M := M) (n := n) b) := by
  intro Y Y' h
  funext a i
  refine b.repr.injective (Finsupp.ext fun l => ?_)
  exact congrFun h (a, (i, l))

theorem cvN_incl_add (R : Type) [CommRing R] [Algebra F R] {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Y : Fin n → Fin M → E) (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b ((fun a i => inclR R (Y a i)) + X) p = algebraMap F R (ratCoord b Y p) + cvN R b X p := by
  simp [cvN, GlobalTheory.CompanionTheory.SW.BB.cv, ratCoord, inclR, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

end Coord

section Main

open GroundTheory.Global

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

theorem tupCovol : TupCovol := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n μ hμ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM n M b
  have hdxc := dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ μ hμ e he hB
  have := hB
  have : BorelSpace (AF F) := GroundTheory.Global.borelSpace_adeleRing F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hD : MeasurableSet (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) :=
    MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hem : Measurable e := e.continuous.measurable
  have hmem : ∀ (Y : Fin n → Fin M → E) X,
      e ((fun a i => inclR (AF F) (Y a i)) + X) ∈
          (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) ↔
        ∀ p, algebraMap F (AF F) (ratCoord b Y p) + e X p ∈ fundamentalSet F := by
    intro Y X
    simp only [Set.mem_univ_pi, he, cvN_incl_add]
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => fundamentalSet F), IsAddFundamentalDomain.mk' (hem hD).nullMeasurableSet fun X => ?_, ?_⟩
  · choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e X p)
    refine ⟨⟨_, ofCoord b (-k), rfl⟩, ?_, ?_⟩
    · refine (hmem _ X).2 fun p => ?_
      rw [ratCoord_ofCoord]
      have := hk p
      rwa [Pi.neg_apply, map_neg, neg_add_eq_sub]
    · rintro ⟨_, Y, rfl⟩ h
      have h' := (hmem Y X).1 h
      have hY : ratCoord b Y = -k := by
        funext p
        have e1 := huniq p (-(ratCoord b Y p)) (by
          change e X p - algebraMap F (AF F) (-(ratCoord b Y p)) ∈ fundamentalSet F
          rw [map_neg, sub_neg_eq_add, add_comm]; exact h' p)
        rw [Pi.neg_apply, ← e1, neg_neg]
      have : Y = ofCoord b (-k) := ratCoord_injective b (by rw [hY, ratCoord_ofCoord])
      subst this
      rfl
  · rw [← Measure.map_apply hem hD, hdxc, GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SiegelND.TupCovolume

end
end

