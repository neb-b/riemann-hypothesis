module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicAnnihilatorBoxProduct
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

private theorem integral_indicator_mul_char_of_trivial {K : Type} [CommRing K] [MeasurableSpace K]
    (μ : Measure K) (p : K → ℂ) (S : AddSubgroup K) (hSm : MeasurableSet (S : Set K)) (y : K)
    (h : ∀ s ∈ S, p (s * y) = 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = ((μ (S : Set K)).toReal : ℂ) := by
  have hfun : (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) =
      (S : Set K).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ (S : Set K)
    · rw [Set.indicator_of_mem hx, one_mul, h x hx]
    · rw [Set.indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator_const _ hSm, measureReal_def, Complex.real_smul, mul_one]

private theorem integral_indicator_mul_char_eq_zero {K : Type} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) [μ.IsAddLeftInvariant] (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (S : AddSubgroup K) (y : K) (h : ∃ s ∈ S, p (s * y) ≠ 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
  obtain ⟨s, hs, hps⟩ := h
  have hI : ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      p (s * y) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ := by
    rw [← integral_const_mul, ← integral_add_left_eq_self
      (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) s]
    congr 1
    funext x
    beta_reduce
    by_cases hx : x ∈ (S : Set K)
    · have hsx : s + x ∈ (S : Set K) := (S.add_mem_cancel_left hs).mpr hx
      rw [Set.indicator_of_mem hsx, Set.indicator_of_mem hx, add_mul, hadd]
      ring
    · have hsx : s + x ∉ (S : Set K) := fun h' => hx ((S.add_mem_cancel_left hs).mp h')
      rw [Set.indicator_of_notMem hsx, Set.indicator_of_notMem hx]
      ring
  have h1 : (1 - p (s * y)) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hps
  · exact h0

theorem ann_core {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (hSD : SelfDual μ (fun s t => p (s * t)))
    (U A B : AddSubgroup K) (hUc : IsCompact (U : Set K)) (hUo : IsOpen (U : Set K))
    (hUm : MeasurableSet (U : Set K)) (hAm : MeasurableSet (A : Set K)) (hAf : μ (A : Set K) ≠ ⊤)
    (hA : ∀ y, y ∈ A ↔ ∀ s ∈ U, p (s * y) = 1)
    (hB : ∀ z, z ∈ B ↔ ∀ s ∈ A, p (s * z) = 1) :
    B = U ∧ (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by
  obtain ⟨hHaar, hinv⟩ := hSD
  have hp0 : p 0 = 1 := by simpa using (hA 0).mp A.zero_mem 0 U.zero_mem
  have hΦc : Continuous ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hUc.isClosed, hUo⟩ continuous_const
  have hΦs : HasCompactSupport ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hUc (fun x hx => Set.indicator_of_notMem hx _)
  have hFT : ∀ y, ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      (A : Set K).indicator (fun _ => ((μ (U : Set K)).toReal : ℂ)) y := by
    intro y
    by_cases h : ∀ s ∈ U, p (s * y) = 1
    · rw [integral_indicator_mul_char_of_trivial μ p U hUm y h,
        Set.indicator_of_mem (show y ∈ (A : Set K) from (hA y).mpr h)]
    · push_neg at h
      rw [integral_indicator_mul_char_eq_zero μ p hadd U y h,
        Set.indicator_of_notMem (show y ∉ (A : Set K) from fun h' => by
          obtain ⟨s, hs, hps⟩ := h
          exact hps ((hA y).mp h' s hs))]
  have hint : Integrable (fun y => ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x *
      (fun s t => p (s * t)) x y ∂μ) μ := by
    simp only [hFT]
    exact (integrable_indicator_iff hAm).mpr (integrableOn_const hAf)
  have key : ∀ z, ((μ (U : Set K)).toReal : ℂ) *
      ∫ y, (A : Set K).indicator (fun _ => (1 : ℂ)) y * p (y * z) ∂μ =
      (U : Set K).indicator (fun _ => (1 : ℂ)) (-z) := by
    intro z
    rw [← integral_const_mul, ← hinv _ hΦc hΦs hint z]
    congr 1
    funext y
    beta_reduce
    rw [hFT y]
    by_cases hy : y ∈ (A : Set K)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have h0 := key 0
  have hc0 : ∀ s ∈ A, p (s * 0) = 1 := fun s _ => by rw [mul_zero, hp0]
  rw [integral_indicator_mul_char_of_trivial μ p A hAm 0 hc0, neg_zero,
    Set.indicator_of_mem (show (0 : K) ∈ (U : Set K) from U.zero_mem)] at h0
  have hprod : (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by exact_mod_cast h0
  refine ⟨?_, hprod⟩
  ext z
  rw [hB z]
  have hz := key z
  constructor
  · intro h
    rw [integral_indicator_mul_char_of_trivial μ p A hAm z h, h0] at hz
    by_contra hzU
    rw [Set.indicator_of_notMem (show -z ∉ (U : Set K) from fun h' => hzU (by simpa using U.neg_mem h'))] at hz
    exact one_ne_zero hz
  · intro hzU
    by_contra h
    push_neg at h
    rw [integral_indicator_mul_char_eq_zero μ p hadd A z h, mul_zero,
      Set.indicator_of_mem (show -z ∈ (U : Set K) from U.neg_mem hzU)] at hz
    exact zero_ne_one hz

theorem localDual : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (c : ℝ≥0), GlobalTheory.CompanionTheory.SW.IsStdV v lam → SelfDual (c • lam) (fun s t => psiV F ψ v (s * t)) → ∀ U : AddSubgroup (Fv F v), IsCompact (U : Set (Fv F v)) → IsOpen (U : Set (Fv F v)) → annV ψ v (annV ψ v U) = U ∧ IsCompact (annV ψ v U) ∧ IsOpen (annV ψ v U) ∧ (c : ℝ) ^ 2 * (lam U).toReal * (lam (annV ψ v U)).toReal = 1 := by
  intro F _ _ ψ hψ v lam c _ hSD U hUc hUo
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have h0 := psiV_zero ψ v
  have hinv := hSD.1
  have hcomp : IsCompact (annV ψ v U) := GlobalTheory.CompanionTheory.SW.PiV.ann_isCompact hc h0 hy U hUo
  have hnear : {x | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds (by
      change ‖psiV F ψ v 0 - 1‖ < 1 / 2
      rw [h0]
      norm_num)
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hnear
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_of_isCompact _ hUc
  have htriv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) _ h0 ha (fun x hx => hm hx) hx
  have hsub : (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n) : Set (Fv F v)) ⊆ annV ψ v U := by
    intro t ht s hs
    refine htriv _ ?_
    rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
    calc Valued.v s * Valued.v t ≤ WithZero.exp n * WithZero.exp (m - n) :=
          mul_le_mul' (hn hs) ht
      _ = WithZero.exp m := by rw [← WithZero.exp_add, add_sub_cancel]
  have hopen : IsOpen (annV ψ v U) :=
    AddSubgroup.isOpen_of_mem_nhds (annS ψ v U) (g := 0)
      (Filter.mem_of_superset ((GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen (m - n)).mem_nhds
        (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n)).zero_mem) hsub)
  have hcore := ann_core (c • lam) (psiV F ψ v) ha hSD U (annS ψ v U) (annS ψ v (annV ψ v U))
    hUc hUo hUo.measurableSet hopen.measurableSet hcomp.measure_lt_top.ne
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨?_, hcomp, hopen, ?_⟩
  · rw [← coe_annS, hcore.1]
  · have h5 := hcore.2
    rw [coe_annS] at h5
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at h5
    rw [← h5]
    ring

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicIntegrableProductIndicator
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integral_pure_indicator_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : AddSubgroup (Af F)), MeasurableSet (B : Set (Af F)) → lf (B : Set (Af F)) ≠ ⊤ → ∀ b : AF F, ∫ y, (g (fstA F y) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F y)) * ψ (y * b) ∂db = (∫ x, g x * psiInf F ψ (x * fstA F b) ∂laminf) * ((lf (B : Set (Af F))).toReal : ℂ) * (annF ψ (B : Set (Af F))).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
  intro F _ _ ψ _ db laminf lf hl hf e he hmp g B hB hfin b
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.1
  haveI : SecondCountableTopology (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.2.1
  haveI : SecondCountableTopology (Ainf F) := by
    haveI : SecondCountableTopology (Ainf F × Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1.2.1
    exact (Topology.IsEmbedding.of_comp (f := fun x : Ainf F => (x, (0 : Af F))) (g := Prod.fst)
      (by fun_prop) continuous_fst Topology.IsEmbedding.id).secondCountableTopology
  haveI : LocallyCompactSpace (Ainf F) := inferInstance
  haveI : IsLocallyFiniteMeasure laminf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : IsLocallyFiniteMeasure lf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SFinite laminf := inferInstance
  haveI : SFinite lf := inferInstance
  set χ : Af F → ℂ := fun u => psiF ψ (u * sndA F b) with hχ
  have hχadd : ∀ x y, χ (x + y) = χ x * χ y := fun x y => by
    simp only [hχ, add_mul, psiF_add]
  have hpt : ∀ p : Ainf F × Af F,
      (g (fstA F (e p)) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F (e p))) * ψ (e p * b) =
        (g p.1 * psiInf F ψ (p.1 * fstA F b)) * (B : Set (Af F)).indicator χ p.2 := by
    rintro ⟨x, u⟩
    have h1 : e (x, u) * b = pairA F (x * fstA F b) (u * sndA F b) := by
      rw [he]; rfl
    have h2 : fstA F (e (x, u)) = x := by rw [he]; rfl
    have h3 : sndA F (e (x, u)) = u := by rw [he]; rfl
    rw [h1, h2, h3, psi_pairA]
    by_cases hu : u ∈ (B : Set (Af F))
    · simp only [Set.indicator_of_mem hu, hχ]
      ring
    · simp only [Set.indicator_of_notMem hu]
      ring
  rw [← hmp.integral_comp e.measurableEmbedding]
  simp only [hpt]
  rw [integral_prod_mul (fun x => g x * psiInf F ψ (x * fstA F b))
    (fun u => (B : Set (Af F)).indicator χ u), mul_assoc]
  congr 1
  by_cases hb : sndA F b ∈ annF ψ (B : Set (Af F))
  · rw [integral_indicator_char_of_trivial lf B hB χ (fun x hx => hb x hx),
      Set.indicator_of_mem hb, mul_one]
  · obtain ⟨y, hy, hne⟩ : ∃ y ∈ (B : Set (Af F)), psiF ψ (y * sndA F b) ≠ 1 := by
      simpa [annF] using hb
    rw [integral_indicator_char_of_ne lf B χ hχadd hy hne, Set.indicator_of_notMem hb, mul_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFourierApproximateIdentity
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass

theorem boxMass : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ lf : Measure (Af F), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v, MeasurableSet (A v)) → MeasurableSet (Coef.boxA S A) ∧ lf (Coef.boxA S A) = ∏ v ∈ S, lam v (A v) := by
  intro F _ _ lam hlam lf hlf h1 S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Unit → Fv F v) := fun v => {x | x () ∈ A v}
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => measurable_pi_apply () (hA v)
  let T : Set (Unit → Af F) := {x | (∀ v ∈ S, (fun i => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i)) ∈ A' v) ∧
    ∀ v, v ∉ S → ∀ i, HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (x i) ∈ v.adicCompletionIntegers F}
  have hT : T = (GlobalTheory.CompanionTheory.SW.AfBox.offS (F := F) Unit S : Set (Unit → Af F)) ∩
      GlobalTheory.CompanionTheory.SW.AfBox.compS Unit S ⁻¹' (Set.pi Set.univ fun v : S => A' v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  have hTm : MeasurableSet T := by
    rw [hT]
    exact (GlobalTheory.CompanionTheory.SW.AfBox.isOpen_offS Unit S).measurableSet.inter
      ((GlobalTheory.CompanionTheory.SW.AfBox.continuous_compS Unit S).measurable (MeasurableSet.univ_pi fun v => hA' v.1))
  have hbox : Coef.boxA S A = (MeasurableEquiv.funUnique Unit (Af F)).symm ⁻¹' T := by
    ext y
    simp only [Coef.boxA, T, A', Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.funUnique_symm_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv _ => h2 v hv⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun v hv => h1 v hv, fun v hv => h2 v hv ()⟩
  have hmeas : MeasurableSet (Coef.boxA S A) := by
    rw [hbox]
    exact (MeasurableEquiv.funUnique Unit (Af F)).symm.measurable hTm
  refine ⟨hmeas, ?_⟩
  have hpb := GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 Unit S A' hA'
  have hmp := measurePreserving_funUnique lf Unit
  have hT' : T = (MeasurableEquiv.funUnique Unit (Af F)) ⁻¹' Coef.boxA S A := by
    rw [hbox, ← Set.preimage_comp]
    ext x
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show (MeasurableEquiv.funUnique Unit (Af F)).symm ((MeasurableEquiv.funUnique Unit (Af F)) x) = x
      from (MeasurableEquiv.funUnique Unit (Af F)).symm_apply_apply x]
  change (Measure.pi fun _ : Unit => lf) T = _ at hpb
  rw [hT', hmp.measure_preimage hmeas.nullMeasurableSet] at hpb
  rw [hpb]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : A' v = (MeasurableEquiv.funUnique Unit (Fv F v)) ⁻¹' A v := by
    ext x
    rfl
  rw [hv, (measurePreserving_funUnique (lam v) Unit).measure_preimage (hA v).nullMeasurableSet]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.BoxMass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsConjMemMajCptFrame
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodPos

theorem exists_conj_mem_majCpt_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)), (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ k : GlobalTheory.CuspRep.Kinf E d, (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
          (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ ∈ majCpt σ J c := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd hS1 hS2 hS3
  obtain ⟨ρ, hρs, hρlift, hρι⟩ := GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb F E σ hCM n J r Xf Yf l d h ι hι
  have loc := fun w => stab_of_frame F E σ hCM n J hJ r Xf Yf hW w (c w) (hc w) l d h
  choose uw N hN hNX hNv y₀ hy₀ using loc
  set u : GAd σ J := ofInf σ J (embArchPi σ J uw) with hu
  have hu_arch : ∀ w, projArch σ J w u = uw w := fun w => by
    rw [hu, projArch_ofInf, projInfArch_embArchPi]
  have hu_inf : u ∈ infPts σ J := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨y, hy⟩ := hρlift y₀
  obtain ⟨k₀, hk₀S, hk₀⟩ := hS2
  refine ⟨u, mem_unip_of_arch_frame F E σ n J r Xf S u hu_inf fun w => ⟨N w, by rw [hu_arch]; exact hN w, fun i j hij => ?_,
    fun v hv => ?_⟩, hu_inf, y, fun k => ?_⟩
  · rcases hNX w i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hS3 with h0 | ⟨p, hpS, hp⟩
      · omega
      · exact ⟨p, hpS, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
    · exact ⟨k₀, hk₀S, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
  · obtain ⟨a, ha, hav⟩ := hNv w v fun i hi => hv i ⟨k₀, hk₀S, by rw [Fin.le_def]; omega⟩
    exact ⟨a, fun i hi => ⟨k₀, hk₀S, by have := ha i hi; rw [Fin.le_def]; omega⟩, by rw [hu_arch]; exact hav⟩
  · have e : (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
        (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ = u * ι (GlobalTheory.CuspRep.infGL E d (y * Unitary.toUnits k * y⁻¹)) * u⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e, mem_majCpt]
    refine ⟨mul_mem (mul_mem hu_inf (hρι _).1) (inv_mem hu_inf), fun w => ?_⟩
    rw [map_mul, map_mul, map_inv, hu_arch]
    refine hy₀ w (Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)) ?_ _ ?_
    · have hk : star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) = 1 :=
        Unitary.star_mul_self_of_mem k.2
      have e1 : Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)).1) =
          (star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))).map (ρ w) := by
        ext i j
        simp [Formalism.UG.cT, Matrix.star_apply, hρs]
      rw [e1]
      change _ * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)).map (ρ w) = 1
      rw [← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [(hρι _).2 w]
      simp only [map_mul, map_inv, hy w]

end GlobalTheory.CompanionTheory.GoodPos
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsRealApproximateIdentity
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integrable_inf_mul_indicator_finiteMass : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : Set (Af F)), Integrable g laminf → MeasurableSet B → lf B ≠ ⊤ → Integrable (fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) db := by
  intro F _ _ db laminf lf _ _ e he hmp g B hg hB hfin
  have hind : Integrable (B.indicator (fun _ => (1 : ℂ))) lf :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hfin)
  refine (hmp.integrable_comp_emb e.measurableEmbedding).mp ?_
  have hfun : ((fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) ∘ e) =
      fun p : Ainf F × Af F => g p.1 * B.indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp only [Function.comp_apply, he p]
    rfl
  rw [hfun]
  exact hg.mul_prod hind

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteAdeleBoxMeasureProduct
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem eventually_mem_annV_ball : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v), ∀ᶠ k : ℕ in Filter.atTop, t ∈ annV ψ v (GlobalTheory.CompanionTheory.SW.PiV.ball v (-(k : ℤ)) : Set (Fv F v)) := by
  intro F _ _ ψ hψ v t
  obtain ⟨hc, -, -⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have hU : {x : Fv F v | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) := by
    have hcont : Continuous fun x : Fv F v => ‖psiV F ψ v x - 1‖ := (hc.sub continuous_const).norm
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    change ‖psiV F ψ v 0 - 1‖ < 1 / 2
    rw [psiV_zero, sub_self, norm_zero]
    norm_num
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hU
  have triv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) (psiV F ψ v) (psiV_zero ψ v) (psiV_add ψ v)
      (fun z hz => hm hz) hx
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_mem_ball t
  filter_upwards [Filter.eventually_ge_atTop (n - m).toNat] with k hk s hs
  apply triv
  rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
  have hs' : Valued.v s ≤ WithZero.exp (-(k : ℤ)) := (GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hs
  have hn' : Valued.v t ≤ WithZero.exp n := (GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hn
  calc Valued.v s * Valued.v t ≤ WithZero.exp (-(k : ℤ)) * WithZero.exp n := mul_le_mul' hs' hn'
    _ = WithZero.exp (-(k : ℤ) + n) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp m := WithZero.exp_le_exp.2 (by omega)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

