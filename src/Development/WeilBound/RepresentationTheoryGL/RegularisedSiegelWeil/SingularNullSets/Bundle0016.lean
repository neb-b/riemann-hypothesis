module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CharSum
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem transfer {H K ι : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H]
    [BorelSpace H] [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] [Fintype ι]
    (Θ : H ≃ₜ+ (ι → K)) (lam : Measure H) [lam.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : ι → K → ℂ, (∫ x, ∏ i, f i (Θ x i) ∂lam = (c : ℂ) * ∏ i, ∫ y, f i y ∂ν) ∧
      ((∀ i, Integrable (f i) ν) → Integrable (fun x => ∏ i, f i (Θ x i)) lam) := by
  have : (Measure.pi fun _ : ι => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ lam (Measure.pi fun _ : ι => ν)
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  refine ⟨c, hc, fun f => ⟨?_, fun hf => ?_⟩⟩
  · have h1 := hemb.integral_map (μ := lam) (fun v : ι → K => ∏ i, f i (v i))
    rw [← h1, hmap, integral_smul_nnreal_measure, integral_fintype_prod_eq_prod, NNReal.smul_def, Complex.real_smul]
  · have h2 : Integrable (fun v : ι → K => ∏ i, f i (v i)) (lam.map Θ) := by
      rw [hmap]
      exact (Integrable.fintype_prod (μ := fun _ => ν) hf).smul_measure ENNReal.coe_ne_top
    exact hemb.integrable_map_iff.mp h2


open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
theorem hCo_smul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {d n : ℕ} (b : Module.Basis (Fin d) F E) (r : R) (X X' : HermR R σ n)
    (h : X'.1 = algebraMap R (R ⊗[F] E) r • X.1) (i : Idx n d) : hCo R σ b X' i = r * hCo R σ b X i := by
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul]
    exact (mul_smul_comm _ _ _).symm
  · simp only [hCo, Sum.elim_inr, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul,
      Finsupp.smul_apply]

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (a : ι → A) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.KappaReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem kappa_real {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {ε : AF F}
    (ν : Measure (fixE ε)) [SFinite ν] (τ : fixE ε → ℝ) (hτ0 : ∀ h, 0 ≤ τ h) (hτI : Integrable τ ν)
    (hτpos : 0 < ∫ h, τ h ∂ν) (M : ℝ) (hτM : ∀ h, τ h ≤ M) (A : fixE ε → ℂ)
    (hA : ∀ s, A s = ∫ h, (τ h : ℂ) * ψ (h.1 * s.1) ∂ν) (hAI : Integrable A ν) (κ : ℂ)
    (hκ : ∀ s : fixE ε, ∫ h, A h * ψ (h.1 * s.1) ∂ν = κ * τ (-s)) :
    κ.im = 0 ∧ 0 ≤ κ.re := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]
    simp
  have hτC : Integrable (fun h => (τ h : ℂ)) ν := hτI.ofReal

  have hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν := by
    intro h
    rw [hA, ← integral_conj]
    congr 1
    funext h'
    rw [map_mul, Complex.conj_ofReal, hconj]
    congr 2
    change -(h'.1 * h.1) = h.1 * -h'.1
    ring

  set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf
  have hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1) :=
    hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
      (continuous_neg.comp continuous_snd)))
  have hfI : Integrable (Function.uncurry f) (ν.prod ν) := by
    refine Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)
    · simp only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hτ0 _)]
      exact le_rfl
  have hsw := integral_integral_swap hfI
  have hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν := by
    congr 1
    funext h
    rw [hA', ← integral_const_mul]
  have hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext h'
    have h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext h
      dsimp [f]
      ring
    rw [h1, hκ, neg_neg]
    push_cast
    ring

  have hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext h
    exact Complex.mul_conj _
  have hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν := integral_nonneg fun h => Complex.normSq_nonneg _
  have hQI : Integrable (fun h => τ h * τ h) ν := by
    refine Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)
  have hQ0 : 0 < ∫ h, τ h * τ h ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm
    have hz' : τ =ᵐ[ν] 0 := hz.mono fun h hh => by
      simpa using (mul_self_eq_zero.1 hh)
    rw [integral_congr_ae hz'] at hτpos
    simp at hτpos
  have hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    rw [← hLr, hL, hsw, hR, integral_complex_ofReal]
  have hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    have hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
    rw [Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]
  rw [hκe, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_nonneg hL0 hQ0.le⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open scoped RestrictedProduct

theorem rp_nhds {ι : Type} {R : ι → Type} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (hA : ∀ i, IsOpen (A i)) (x : ∀ i, A i) (W : Set (Πʳ i, [R i, A i]))
    (hW : W ∈ 𝓝 (RestrictedProduct.structureMap R A cofinite x)) :
    ∃ V : ∀ i, Set (R i), (∀ i, V i ∈ 𝓝 (x i : R i)) ∧ ∀ z : Πʳ i, [R i, A i], (∀ i, z i ∈ V i) → z ∈ W := by
  rw [RestrictedProduct.nhds_eq_map_structureMap hA, Filter.mem_map, nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  have ht' : ∀ i, ∃ u ∈ 𝓝 (x i : R i), Subtype.val ⁻¹' u ⊆ t i := fun i => mem_nhds_subtype _ _ _ |>.1 (ht i)
  choose u hu hut using ht'
  refine ⟨fun i => u i ∩ A i, fun i => Filter.inter_mem (hu i) ((hA i).mem_nhds (x i).2), fun z hz => ?_⟩
  let y : ∀ i, A i := fun i => ⟨z i, (hz i).2⟩
  have hyz : RestrictedProduct.structureMap R A cofinite y = z := Subtype.ext rfl
  rw [← hyz]
  exact hIt fun i _ => hut i (hz i).1

theorem af_nhds {F : Type} [Field F] [NumberField F] (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ V : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, V v ∈ 𝓝 (0 : Fv F v)) ∧
      ∀ z : Af F, (∀ v, z v ∈ V v) → z ∈ W := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := fun v => Valued.isOpen_valuationSubring _
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite (fun _ => ⟨0, zero_mem _⟩) =
      (0 : Af F) := rfl
  rw [← h0] at hW
  exact rp_nhds hA _ W hW

theorem top1 {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsIdF S ε)
    (A : ℕ → Set (Ainf F)) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hA : Tendsto A atTop (𝓝 0).smallSets) (hU : ∀ v, Tendsto (fun k => U k v) atTop (𝓝 0).smallSets) :
    Tendsto (fun k => {a : AF F | ε * a = a ∧ fstA F a ∈ A k ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}) atTop
      (𝓝 (0 : AF F)).smallSets := by
  rw [Filter.tendsto_smallSets_iff]
  intro W hW
  obtain ⟨W1, hW1, W2, hW2, hsub⟩ := mem_nhds_prod_iff.1 (show W ∈ 𝓝 ((0, 0) : Ainf F × Af F) from hW)
  obtain ⟨V, hV, hVW⟩ := af_nhds W2 hW2
  have e1 := Filter.tendsto_smallSets_iff.1 hA W1 hW1
  have e2 : ∀ᶠ k in atTop, ∀ v ∈ S, U k v ⊆ V v :=
    (Filter.eventually_all_finset S).2 fun v _ => Filter.tendsto_smallSets_iff.1 (hU v) (V v) (hV v)
  filter_upwards [e1, e2] with k h1 h2
  rintro a ⟨hεa, haA, haU⟩
  apply hsub
  refine ⟨h1 haA, hVW (sndA F a) fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact h2 v hv (haU v hv)
  · have h3 : sndA F a = sndA F ε * sndA F a := by rw [← map_mul, hεa]
    have h4 : (sndA F a) v = (sndA F ε) v * (sndA F a) v := congrArg (fun z : Af F => z v) h3
    rw [hε.2 v, if_neg hv, zero_mul] at h4
    rw [h4]
    exact mem_of_mem_nhds (hV v)

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

