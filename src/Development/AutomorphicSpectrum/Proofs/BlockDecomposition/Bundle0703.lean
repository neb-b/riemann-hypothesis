module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupMulISupMono
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem lintegral_close {R : Type} [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) {S N : Set R}
    (hS : MeasurableSet S) (hfin : ν S ≠ ⊤) (hN : ν N = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ s ∈ S, s ∉ N → G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ) :
    |(∫⁻ s in S, G s ∂ν).toReal - (ν S).toReal| ≤ δ * (ν S).toReal := by
  have hae : ∀ᵐ s ∂(ν.restrict S), G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ := by
    rw [ae_restrict_iff' hS]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with s hs hsS
    exact h s hsS hs
  have hup : ∫⁻ s in S, G s ∂ν ≤ ENNReal.ofReal (1 + δ) * ν S := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).2])
  have hlo : ENNReal.ofReal (1 - δ) * ν S ≤ ∫⁻ s in S, G s ∂ν := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).1])
  have hfinU : ENNReal.ofReal (1 + δ) * ν S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hup' : (∫⁻ s in S, G s ∂ν).toReal ≤ (1 + δ) * (ν S).toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (1 - δ) * (ν S).toReal ≤ (∫⁻ s in S, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [abs_le]
  constructor <;> nlinarith

theorem density_close {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hM : 3 ≤ M) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lv : Measure (Fv F v)) (hlv : IsStdV v lv)
    (mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hmv : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M) (coordHerm (Fv F v) σ b lv 1) mv)
    {x δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      |(mv (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ δ)
    (hav : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U →
      |(coordW (Fv F v) b lv 1 M (latV b v ∩ {X | algebraMap F (Fv F v) (1 / 2) *
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal -
        x * (lv V).toReal| ≤ ε * (lv V).toReal) :
    |x - 1| ≤ δ := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M)
      (lv.map (hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  obtain ⟨hLc, hLo, -, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := (latV b v).indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hLo.frontier_eq, hLc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hLc fun X hX => ?_
    exact Set.indicator_of_notMem hX _
  obtain ⟨hI, -⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hfinG : ∀ s : Fv F v, s ≠ 0 → mv (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro s hs
    have h := hI s (isUnit_iff_ne_zero.2 hs)
    rw [integrable_indicator_iff hLm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨U, hU, hUV⟩ := hav ε hε
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  set S : Set (Fv F v) := interior U ∩ (v.adicCompletionIntegers F : Set (Fv F v)) with hSdef
  have hSo : IsOpen S := isOpen_interior.inter hOo
  have h0S : (0 : Fv F v) ∈ S := ⟨mem_interior_iff_mem_nhds.2 hU, zero_mem _⟩
  have hSfin : lv S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hlv.2]
    exact ENNReal.one_ne_top
  have hSpos : 0 < (lv S).toReal :=
    ENNReal.toReal_pos (hSo.measure_ne_zero lv ⟨0, h0S⟩) hSfin
  have h1 := hUV S hSo.measurableSet (Set.inter_subset_left.trans interior_subset)
  have h2 := lintegral_close lv (fun s => mv (hermScal (Fv F v) σ s) (latV b v)) hSo.measurableSet hSfin
    n1 hδ (fun s hs hs0 => ⟨hfinG s (not_not.1 hs0).ne_zero, hB s hs.2 (not_not.1 hs0).ne_zero⟩)
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.fibre_mass_eq _ lv _ hqc.measurable _ _ FF hLm hSo.measurableSet] at h2
  have h3 : |x - 1| * (lv S).toReal ≤ (δ + ε) * (lv S).toReal := by
    have e : (x - 1) * (lv S).toReal = (x * (lv S).toReal -
        (coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal) +
        ((coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        (lv S).toReal) := by ring
    rw [← abs_of_pos hSpos, ← abs_mul, abs_of_pos hSpos, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm]
    have h1' : |(coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        x * (lv S).toReal| ≤ ε * (lv S).toReal := h1
    linarith
  exact le_of_mul_le_mul_right h3 hSpos

end GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hL := fun v => GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have avg := fun v => _root_.GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (latV b v) (hL v).1 (hL v).2.1
  refine ⟨fun v => (avg v).1, ?_⟩
  refine Summable.of_norm_bounded_eventually
    (g := fun v : HeightOneSpectrum (𝓞 F) => 2 * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
    ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left 2) ?_
  filter_upwards [_root_.GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice F E σ hσ M J hJ hM d b] with v hv
  obtain ⟨m', hm'⟩ := GlobalTheory.CompanionTheory.SW.GoodMass.exists_family hσ hJ b v (lam v) (hlam v) 1
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := GlobalTheory.CompanionTheory.SW.GoodMass.absNorm_one_le v
  have hd := GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.density_close hσ hJ hM b v (lam v) (hlam v) m' hm'
    (x := (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal)
    (δ := 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1)) (by positivity)
    (hv (lam v) (hlam v) m' hm') (avg v).2
  rw [Real.norm_eq_abs, abs_abs]
  refine hd.trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ hq (by omega))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslate
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.TorusDeriv

noncomputable def blockL (E : Type) [Field E] (r s : ℕ) : Lie E (r + s) :=
  ∑ i : Fin r, toL (Matrix.single (Fin.castAdd s i) (Fin.castAdd s i) (1 : Cinf E))

theorem blockL_apply (E : Type) [Field E] (r s : ℕ) (i j : Fin (r + s)) (w : InfinitePlace E) :
    blockL E r s i j w = if i = j then (if (i : ℕ) < r then (1 : ℂ) else 0) else 0 := by
  have e : blockL E r s i j w =
      ∑ k : Fin r, ((Matrix.single (Fin.castAdd s k) (Fin.castAdd s k) (1 : Cinf E)) i j) w := by
    simp only [blockL, Finset.sum_apply]
    rfl
  rw [e]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have : Fin.castAdd s (⟨i, hi⟩ : Fin r) = i := Fin.ext rfl
        simp [this]
      · intro b _ hb
        have : Fin.castAdd s b ≠ i := fun h => hb (Fin.ext (show (b : ℕ) = i from congrArg Fin.val h))
        simp [Matrix.single_apply, this]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : Fin.castAdd s k ≠ i := fun h => hi (by rw [← h]; exact k.2)
      simp [Matrix.single_apply, this]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (Fin.castAdd s k = i ∧ Fin.castAdd s k = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this]

theorem hasDerivAt_entries {ι : Type} [Fintype ι] {a : ℕ} (f : ℝ → Fin a → Fin a → ι → ℂ) (X : Fin a → Fin a → ι → ℂ)
    (h : ∀ i j w, HasDerivAt (fun t => f t i j w) (X i j w) 0) : HasDerivAt f X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => h i j w

theorem hasDerivAt_aInf (E : Type) [Field E] [NumberField E] (r s : ℕ) :
    HasDerivAt (fun t : ℝ => toL (aInf E (r + s) r t).val) (blockL E r s) 0 := by
  refine hasDerivAt_entries _ _ fun i j w => ?_
  rw [blockL_apply]
  have e : (fun t : ℝ => (toL (aInf E (r + s) r t).val) i j w) = fun t : ℝ =>
      if i = j then Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0) else 0 := by
    funext t
    by_cases hij : i = j
    · subst hij
      simp [aInf]
    · simp [aInf, hij]
  rw [e]
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).cexp
    · simp only [if_neg hi]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  · simp only [if_neg hij]
    exact hasDerivAt_const _ _

theorem lie_blockL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    lie E (r + s) (blockL E r s) =
      ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.CapelliTrace.sum_Eop _ _, blockL, map_sum]
  rfl

theorem hasDerivAt_aT_right : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  intro E _ _ _ r s F g t
  have h0 : aInf E (r + s) r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  have h1 := hasDerivAt_curve F (g * aT E (r + s) r t) (aInf E (r + s) r) (blockL E r s) h0
    (hasDerivAt_aInf E r s)
  have h2 : HasDerivAt (fun u : ℝ => F.1 ((g * aT E (r + s) r t) * infGL E (r + s) (aInf E (r + s) r (u - t))))
      (lieD (blockL E r s) F.1 (g * aT E (r + s) r t)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  rw [← lie_blockL]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have e : aT E (r + s) r u = aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r (u - t)) := by
    rw [← aT, ← PExpFin.aT_add]
    congr 1
    ring
  simp only []
  rw [e, mul_assoc]

end GlobalTheory.CompanionTheory.Conc.TorusDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicRankOneGlobalVolume
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne

theorem abs_sub_one_le {P L : ℝ≥0∞} {r A : ℝ} (hr : 0 ≤ r) (hL : L < ⊤) (hPL : P ≤ L)
    (h : L ≤ P + ENNReal.ofReal (2 * r) * L) (hA : |L.toReal - 1| ≤ A) :
    |P.toReal - 1| ≤ |L.toReal - 1| + 2 * (1 + A) * r := by
  have hP : P < ⊤ := lt_of_le_of_lt hPL hL
  have h1 : P.toReal ≤ L.toReal := ENNReal.toReal_mono hL.ne hPL
  have h2 : L.toReal ≤ P.toReal + 2 * r * L.toReal := by
    have hfin : P + ENNReal.ofReal (2 * r) * L ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hP.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne⟩
    have := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_add hP.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have h3 : L.toReal ≤ 1 + A := by
    have := (abs_le.1 hA).2
    linarith
  have h4 : 2 * r * L.toReal ≤ 2 * (1 + A) * r := by
    have : 2 * r * L.toReal ≤ 2 * r * (1 + A) := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h5 : |P.toReal - L.toReal| ≤ 2 * (1 + A) * r := by
    rw [abs_le]
    constructor <;> linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * r) (ENNReal.toReal_nonneg (a := L))]
  calc |P.toReal - 1| = |(P.toReal - L.toReal) + (L.toReal - 1)| := by ring_nf
    _ ≤ |P.toReal - L.toReal| + |L.toReal - 1| := abs_add_le _ _
    _ ≤ |L.toReal - 1| + 2 * (1 + A) * r := by linarith

theorem prim_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)), IsGramFibFree (Ainf F) σ (hypOne J) 1 (coordW (Ainf F) b laminf 1 (M + 2)) (coordHerm (Ainf F) σ b laminf 1) minf → (∀ v, IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b (lam v) 1 (M + 2)) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ I : Measure (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsEulerProd b I 1 (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) → Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v)).toReal - 1|) ∧ ∃ S₃ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₃ ⊆ S → ∀ (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → ∫⁻ y, purePr σ J b S Ψinf Ψ y ∂I = ((∫⁻ y, Ψinf y ∂(minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂))) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v.1)).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b laminf lam hinf hlam h₂ minf m hfinf hfv I hE
  have hND := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hCM M J hJ).1
  have hSF := GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero F E σ hCM (M + 2) (hypOne J) hND (by omega) h₂ d b laminf lam hinf hlam
    minf hfinf m hfv
  have hgood := (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc.prim_local F E σ hCM M J hJ (by omega) d b).and (GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.eventually_measurableSet_primV F E σ hCM M J hJ d b)
  obtain ⟨hfin, hsumL, -⟩ := id hE
  have hsum : Summable (fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (primV σ J b v)).toReal - 1|) := by
    set A : ℝ := ∑' v, |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
      (latV b v)).toReal - 1| with hAdef
    have hb := (hsumL.add (((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left
      (2 * (1 + A)))))
    refine Summable.of_norm_bounded_eventually hb ?_
    filter_upwards [hgood] with v hv
    obtain ⟨⟨hsub, hmass⟩, -⟩ := hv
    have h := hmass (lam v) (hlam v) (m v) (hfv v) h₂
    have hle : |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v)).toReal - 1| ≤ A :=
      hsumL.le_tsum v (fun _ _ => abs_nonneg _)
    have hr : (0 : ℝ) ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by positivity
    have h' := abs_sub_one_le hr (hfin v) (measure_mono hsub) (by
      have e : (2 : ℝ) * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) = 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
        ring
      rw [e]
      exact h) hle
    rw [Real.norm_eq_abs, abs_abs]
    simpa [mul_assoc] using h'
  refine ⟨hsum, ?_⟩
  have hfinS : {v | ¬ ((primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v))}.Finite := by
    have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        (primV σ J b v ⊆ latV b v) ∧ MeasurableSet (primV σ J b v) := by
      filter_upwards [hgood] with v hv
      exact ⟨hv.1.1, hv.2⟩
    exact Filter.eventually_cofinite.1 h
  exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimFormula.prim_formula F E σ hCM M J hJ d b I _ _ hE hSF.1 hSF.2.1 hfinS.toFinset
    (fun v hv => by
      by_contra hc
      exact hv (hfinS.mem_toFinset.2 hc)) hsum

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimOne
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecomposition
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (u : (AF F)ˣ) : IsNm σ (ofF u : (AF F ⊗[F] E)ˣ) (u * u) := by
  unfold IsNm
  have hs : sigR (AF F) σ ((u : AF F) ⊗ₜ[F] (1 : E)) = (u : AF F) ⊗ₜ[F] (1 : E) := by
    simp [sigR]
  have e : ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e, hs, Units.val_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ideleEquiv_ofE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : Eˣ) :
    GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
  apply Units.ext
  rw [GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv]
  exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem exists_unit_decomp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) :
    ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n →
      ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧
        md n = ε ^ (2 * Module.finrank ℚ F) := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  refine ⟨(GroundTheory.BlockD.ThmBHecke.ideleEquiv F E).symm '' D,
    hD.image GroundTheory.BlockD.ThmBHecke.continuous_ideleEquiv_symm, fun y n hyn => ?_⟩
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : 2 * Module.finrank ℚ F ≠ 0 := by omega
  have hn : 0 < md n := (IdeleGroup.ideleModule F n).2
  set m := 2 * Module.finrank ℚ F with hmdef
  set ε : ℝ := md n ^ ((m : ℝ)⁻¹) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hn _
  have hεm : md n = ε ^ m := (Real.rpow_inv_natCast_pow hn.le hm).symm
  have hray : md (r ε * r ε) = ε ^ m := by
    have h1 := ((_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray F hcm.1 θ hθ r hr).2 ε hε)
    have h2 : md (r ε * r ε) = md (r ε) * md (r ε) := by simp [md, map_mul]
    rw [h2, h1, hmdef, two_mul, pow_add]
  have hy := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm F E σ hcm y n hyn
  have hu := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm F E σ hcm (ofF (r ε)) (r ε * r ε) (isNm_ofF σ (r ε))
  set I := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E with hI
  have hker : I (y * (ofF (r ε))⁻¹) ∈ IdeleGroup.normOneSubgroup E := by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    have hpos : (0 : ℝ) < ε ^ m := pow_pos hε m
    rw [map_mul, map_inv, map_mul, map_inv]
    change ((IdeleGroup.ideleModule E (I y) : ℝ)) *
      ((IdeleGroup.ideleModule E (I (ofF (r ε))) : ℝ))⁻¹ = 1
    rw [hy, hu, hray, hεm]
    exact mul_inv_cancel₀ hpos.ne'
  obtain ⟨t, ht⟩ := hxD _ hker
  refine ⟨t⁻¹, I.symm (IdeleGroup.diagonal E t * I (y * (ofF (r ε))⁻¹)), ε, ⟨_, ht, rfl⟩, hε, ?_, hεm⟩
  apply I.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hI, ideleEquiv_ofE, map_inv, ← hI, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSat2InvTConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurablePureAdelicFunctionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_pure_adelic_function : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → (∀ v ∈ S, Continuous (g v)) →
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | exact GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | (intros; apply GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero <;> assumption)
end

