module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M).2.2.2.1 v).2.measurableSet

theorem coordW_latV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v)) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  classical
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  have hm := measurableSet_latV σ hCM b n M
  have e0 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M ∅ (fun w => latV b w) hm
  have e1 := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M {v} (fun w => latV b w) hm
  have hs : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ w ∈ ({v} : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ ({v} : Finset _) → projV w X ∈ latV b w} =
      {X | (∀ w ∈ (∅ : Finset _), projV w X ∈ latV b w) ∧ ∀ w, w ∉ (∅ : Finset _) → projV w X ∈ latV b w} := by
    ext X
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, Finset.notMem_empty, false_imp_iff, implies_true, true_and, not_false_eq_true, forall_true_left]
    constructor
    · rintro ⟨h, h'⟩ w
      by_cases hw : w = v
      · exact h w hw
      · exact h' w hw
    · exact fun h => ⟨fun w _ => h w, fun w _ => h w⟩
  rw [hs, e0] at e1
  simpa using e1.symm

theorem sfinite_coordW (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (n M : ℕ) : SFinite (coordW (Af F) b lf n M) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.1 d b
  haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Af F) hKf lf
  unfold coordW
  infer_instance

theorem lint_fin (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    Measurable (({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      fun Y => ∏ v ∈ S, φ v (projV v Y)) ∧
    ∫⁻ Y, ({Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} : Set (Fin n → Fin M → Af F ⊗[F] E)).indicator
      (fun Y => ∏ v ∈ S, φ v (projV v Y)) Y ∂(coordW (Af F) b lf n M) =
      ∏ v ∈ S, ∫⁻ X, φ v X ∂(coordW (Fv F v) b (lam v) n M) := by
  classical
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  have hSFv : ∀ v, SigmaFinite (coordW (Fv F v) b (lam v) n M) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.1 d b
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) hK (lam v)
    unfold coordW
    infer_instance
  have hcV : ∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    (_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M).2.2.1
  have hpv : ∀ v, Measurable (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) := fun v => by
    haveI := hBv v
    exact (hcV v).measurable
  have hlat := measurableSet_latV σ hCM b n M
  set A : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ v, v ∉ S → projV v Y ∈ latV b v} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ v, ⋂ (_ : v ∉ S), projV v ⁻¹' latV b v := by
      ext Y; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hpv v (hlat v)
  have hfm : Measurable fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ v ∈ S, φ v (projV v Y) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp (hpv v)
  refine ⟨hfm.indicator hAm, ?_⟩
  let ρ : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E) := fun Y v => projV v.1 Y
  have hρ : Measurable ρ := Measurable.of_eval fun v => hpv v.1
  haveI : ∀ v : S, SigmaFinite (coordW (Fv F v.1) b (lam v.1) n M) := fun v => hSFv v.1
  have hmap : ((coordW (Af F) b lf n M).restrict A).map ρ =
      Measure.pi fun v : S => coordW (Fv F v.1) b (lam v.1) n M := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
      fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
    have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
      by_cases h : v ∈ S
      · simp only [A', dif_pos h]; exact hs _
      · simp only [A', dif_neg h]; exact MeasurableSet.univ
    have key := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d b lam hlam lf hlf h1 n M S A' hA'
    have hset : ρ ⁻¹' Set.univ.pi s ∩ A = {X | (∀ v ∈ S, projV v X ∈ A' v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} := by
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, hA, Set.mem_setOf_eq]
      refine and_congr_left fun _ => ⟨fun h v hv => ?_, fun h v => ?_⟩
      · simpa only [A', dif_pos hv] using h ⟨v, hv⟩
      · have := h v.1 v.2
        simpa only [A', dif_pos v.2] using this
    rw [hset, key, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [A', dif_pos v.2]
  rw [lintegral_indicator hAm]
  have hG : Measurable fun y : (∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)) => ∏ v : S, φ v.1 (y v) :=
    Finset.measurable_prod _ fun v _ => (hφ v.1).comp (measurable_pi_apply v)
  have e1 : ∫⁻ Y in A, ∏ v ∈ S, φ v (projV v Y) ∂(coordW (Af F) b lf n M) =
      ∫⁻ y, ∏ v : S, φ v.1 (y v) ∂(((coordW (Af F) b lf n M).restrict A).map ρ) := by
    rw [lintegral_map hG hρ]
    refine lintegral_congr fun Y => ?_
    rw [← Finset.prod_coe_sort S]
  rw [e1, hmap, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (f := fun v : S => φ v.1) fun v => (hφ v.1).aemeasurable,
    ← Finset.prod_coe_sort S]

section Meas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

abbrev intInf (F : Type) [Field F] [NumberField F] : AddSubgroup (Ainf F) :=
  ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range


omit [NumberField E] in
theorem coordW_congr {F : Type} [Field F] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    @coordW F E _ _ _ R _ _ _ m₁ d b l₁ n M = @coordW F E _ _ _ R _ _ _ m₂ d b l₂ n M := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

theorem std_transfer (laminf : @Measure (Ainf F) measAinf) (hinf : IsStdInf laminf)
    [m : MeasurableSpace (Ainf F)] (hm : m = measAinf) :
    ∃ l : Measure (Ainf F), (∀ s, l s = laminf s) ∧ l.IsAddHaarMeasure ∧
      ∃ D : Set (Ainf F), IsAddFundamentalDomain (intInf F) D l ∧ l D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hinf
  exact ⟨laminf, fun _ => rfl, h1, D, h2, h3⟩

theorem isFD_fundamentalSetInfinite (ν : Measure (InfiniteAdeleRing F)) :
    IsAddFundamentalDomain (intInf F) (fundamentalSetInfinite F) ν := by
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · have hmeas := measurableSet_fundamentalSet F
    have hpre : fundamentalSetInfinite F =
        (fun x : InfiniteAdeleRing F => ((x, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) ⁻¹' fundamentalSet F := by
      ext x
      simp [fundamentalSet, Set.mem_prod, Subring.zero_mem]
    rw [hpre]
    exact (measurable_prodMk_right hmeas).nullMeasurableSet
  · obtain ⟨z, hz, hu⟩ := existsUnique_sub_mem_fundamentalSetInfinite F x
    refine ⟨⟨algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z), -z, rfl⟩, ?_, ?_⟩
    · change algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z) + x ∈ fundamentalSetInfinite F
      rwa [map_neg, neg_add_eq_sub]
    · rintro ⟨_, k, rfl⟩ h
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k + x ∈ fundamentalSetInfinite F at h
      have hk : -k = z := hu (-k) (by
        change x - algebraMap (𝓞 F) (InfiniteAdeleRing F) (-k) ∈ fundamentalSetInfinite F
        rwa [map_neg, sub_neg_eq_add, add_comm])
      refine Subtype.ext ?_
      change algebraMap (𝓞 F) (InfiniteAdeleRing F) k = algebraMap (𝓞 F) (InfiniteAdeleRing F) (-z)
      rw [← hk, neg_neg]

theorem adele_eq (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    l.prod lf = adeleMeasure F := by
  haveI : Countable (𝓞 F) := inferInstance
  haveI : Countable (intInf F) := by
    have : Function.Surjective ((((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom).rangeRestrict) :=
      AddMonoidHom.rangeRestrict_surjective _
    exact this.countable
  have h2 : l (fundamentalSetInfinite F) = 1 := ((isFD_fundamentalSetInfinite l).measure_eq hD).trans hD1
  set c : ℝ≥0 := Measure.addHaarScalarFactor l (infiniteAdeleMeasure F) with hc
  have hl : l = c • infiniteAdeleMeasure F := Measure.isAddLeftInvariant_eq_smul l (infiniteAdeleMeasure F)
  set s : ℝ≥0 := NNReal.sqrt ‖discr F‖₊ with hs
  have h3 : (c : ℝ≥0∞) * (s : ℝ≥0∞) = 1 := by
    rw [hl, Measure.smul_apply, infiniteAdeleMeasure_fundamentalSetInfinite] at h2
    simpa [ENNReal.smul_def] using h2
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (integralFiniteAdelesPositiveCompacts F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  have hlf2 : lf = Measure.addHaarMeasure (integralFiniteAdelesPositiveCompacts F) := by
    have := Measure.addHaarMeasure_unique lf (integralFiniteAdelesPositiveCompacts F)
    rw [← hset, h1, one_smul] at this
    exact this
  have hf : ∀ t, lf t = (s : ℝ≥0∞) * finiteAdeleMeasure F t := by
    intro t
    have hs0 : (s : ℝ≥0∞) ≠ 0 := by
      simpa [hs] using sqrt_discr_ne_zero F
    rw [finiteAdeleMeasure, Measure.smul_apply, ← hlf2, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (sqrt_discr_ne_zero F), ← mul_assoc,
      ENNReal.mul_inv_cancel hs0 ENNReal.coe_ne_top, one_mul]
  haveI : SigmaFinite l := by rw [hl]; infer_instance
  haveI : SigmaFinite lf := by rw [hlf2]; infer_instance
  symm
  refine Measure.prod_eq fun A B _ _ => ?_
  rw [Measure.prod_prod, hf B]
  have hA : l A = (c : ℝ≥0∞) * infiniteAdeleMeasure F A := by
    conv_lhs => rw [hl]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hA]
  calc (c : ℝ≥0∞) * infiniteAdeleMeasure F A * ((s : ℝ≥0∞) * finiteAdeleMeasure F B)
      = ((c : ℝ≥0∞) * s) * (infiniteAdeleMeasure F A * finiteAdeleMeasure F B) := by ring
    _ = _ := by rw [h3, one_mul]

end Meas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsBlockPoint
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.GoodPos

theorem goodPos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ g : GAd σ J, ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ (y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E)) (g₀ : GAd σ J),
        g = u * ι (GlobalTheory.CuspRep.infGL E d y) * g₀ ∧
        ∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW K hK S l d h ι hι hd h1 h2 h3 g
  have hconj : ∀ a : GAd σ J, Continuous fun x : GAd σ J => a * x * a⁻¹ := fun a =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hnorm : ∀ a x : GAd σ J, x ∈ infPts σ J → a * x * a⁻¹ ∈ infPts σ J := fun a x hx => by
    rw [mem_infPts_iff_forall] at hx ⊢
    intro v
    simp [map_mul, map_inv, hx v]
  set K1 : Subgroup (GAd σ J) := K.map (MulAut.conj g).toMonoidHom with hK1
  have hK1le : K1 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g x (hK.1.1 hx)
  have hK1c : IsCompact (K1 : Set (GAd σ J)) := by
    have : (K1 : Set (GAd σ J)) = (fun x => g * x * g⁻¹) '' (K : Set (GAd σ J)) := by
      ext x; simp [hK1, MulAut.conj_apply]
    rw [this]; exact hK.1.2.image (hconj g)
  obtain ⟨c, hc, hle⟩ := _root_.GlobalTheory.CptMajorant.exists_frame_le_majCpt F E σ hCM n J hJ K1 hK1le hK1c
  set K2 : Subgroup (GAd σ J) := (majCpt σ J c).map (MulAut.conj g⁻¹).toMonoidHom with hK2
  have hmc := (isMaxCpt_majCpt hCM hc).1
  have hK2le : K2 ≤ infPts σ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm g⁻¹ x (hmc.1 hx)
  have hK2c : IsCompact (K2 : Set (GAd σ J)) := by
    have : (K2 : Set (GAd σ J)) = (fun x => g⁻¹ * x * g⁻¹⁻¹) '' (majCpt σ J c : Set (GAd σ J)) := by
      ext x; simp [hK2, MulAut.conj_apply]
    rw [this]; exact hmc.2.image (hconj g⁻¹)
  have hKK2 : K ≤ K2 := fun x hx => ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hK2K : K2 ≤ K := hK.2 ⟨hK2le, hK2c⟩ hKK2
  obtain ⟨u, hu, hui, y, hy⟩ := exists_conj_mem_majCpt_frame F E σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd h1 h2 h3
  refine ⟨u, hu, hui, y, (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ * g, by group, fun k => hK2K ?_⟩
  refine ⟨_, hy k, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, _root_.mul_inv_rev]
  group

end GlobalTheory.CompanionTheory.GoodPos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtension
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis

theorem exists_basis_of_duality {E : Type} [Field E] {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) E)
    (A B : Matrix (Fin m) (Fin n) E) (hAX : A * X = 1) (hAY : A * Y = 0) (hBX : B * X = 0) (hBY : B * Y = 1) :
    2 * m ≤ n ∧ ∃ C : GL (Fin n) E,
      (∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, C.1 k i = X k j) ∧
      (∀ (i : Fin n) (j : Fin m), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j) ∧
      (∀ i : Fin n, m ≤ i.val → i.val + m < n →
        A *ᵥ (fun k => C.1 k i) = 0 ∧ B *ᵥ (fun k => C.1 k i) = 0) := by
  classical
  set P : Matrix (Fin m ⊕ Fin m) (Fin n) E := Matrix.fromRows A B with hP
  have hPQ : P * Matrix.fromCols X Y = 1 := by
    rw [hP, Matrix.fromRows_mul_fromCols, hAX, hAY, hBX, hBY, Matrix.fromBlocks_one]
  have hsurj : Function.Surjective P.mulVecLin := fun u => ⟨Matrix.fromCols X Y *ᵥ u, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrk
  have hmem : ∀ k, k ∈ LinearMap.ker P.mulVecLin ↔ A *ᵥ k = 0 ∧ B *ᵥ k = 0 := by
    intro k
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, Matrix.fromRows_mulVec]
    constructor
    · intro h
      exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
    · rintro ⟨h1, h2⟩
      funext i
      cases i <;> simp [h1, h2]
  set K := LinearMap.ker P.mulVecLin with hK
  let b := Module.finBasis E K
  have hle : 2 * m ≤ n := by omega
  refine ⟨hle, ?_⟩
  let col : Fin n → Fin n → E := fun i =>
    if h1 : i.val < m then fun k => X k ⟨i.val, h1⟩
    else if h2 : i.val + m < n then (b ⟨i.val - m, by have := i.2; omega⟩ : K).1
    else fun k => Y k ⟨n - 1 - i.val, by have := i.2; omega⟩
  let C0 : Matrix (Fin n) (Fin n) E := Matrix.of fun k i => col i k
  have hcol : ∀ i, col i ∈ LinearMap.range C0.mulVecLin := fun i =>
    ⟨Pi.single i 1, by
      funext k
      simp [Matrix.mulVecLin_apply, C0]⟩
  have hX : ∀ (j : Fin m), (fun k => X k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hi : j.val < n := by have := j.2; omega
    have := hcol ⟨j.val, hi⟩
    simpa [col] using this
  have hY : ∀ (j : Fin m), (fun k => Y k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hj := j.2
    have hi : n - 1 - j.val < n := by omega
    have := hcol ⟨n - 1 - j.val, hi⟩
    have e1 : ¬ (n - 1 - j.val < m) := by omega
    have e2 : ¬ (n - 1 - j.val + m < n) := by omega
    have e3 : n - 1 - (n - 1 - j.val) = j.val := by omega
    simpa [col, e1, e2, e3] using this
  have hb : ∀ (t : Fin (Module.finrank E K)), (b t : K).1 ∈ LinearMap.range C0.mulVecLin := by
    intro t
    have ht := t.2
    have hi : t.val + m < n := by omega
    have := hcol ⟨t.val + m, hi⟩
    have e1 : ¬ (t.val + m < m) := by omega
    have e2 : t.val + m + m < n := by omega
    simpa [col, e1, e2] using this
  have hKr : ∀ k : K, k.1 ∈ LinearMap.range C0.mulVecLin := by
    intro k
    rw [← b.sum_repr k]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hb t)
  have hmv : ∀ (Z : Matrix (Fin n) (Fin m) E), (∀ j : Fin m, (fun k => Z k j) ∈ LinearMap.range C0.mulVecLin) →
      ∀ u, Z *ᵥ u ∈ LinearMap.range C0.mulVecLin := by
    intro Z hZ u
    have : Z *ᵥ u = ∑ j, u j • (fun k => Z k j) := by
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t)
  have hs : Function.Surjective C0.mulVec := by
    intro v
    have hk : v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v) ∈ K := by
      have eAX : ∀ w, A *ᵥ (X *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hAX, Matrix.one_mulVec]
      have eAY : ∀ w, A *ᵥ (Y *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hAY, Matrix.zero_mulVec]
      have eBX : ∀ w, B *ᵥ (X *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hBX, Matrix.zero_mulVec]
      have eBY : ∀ w, B *ᵥ (Y *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hBY, Matrix.one_mulVec]
      rw [hK, hmem]
      constructor
      · simp only [Matrix.mulVec_sub, eAX, eAY, sub_self, sub_zero]
      · simp only [Matrix.mulVec_sub, eBX, eBY, sub_self, sub_zero]
    have h3 := hKr ⟨_, hk⟩
    have h1 := hmv X hX (A *ᵥ v)
    have h2 := hmv Y hY (B *ᵥ v)
    have : v = (v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v)) + X *ᵥ (A *ᵥ v) + Y *ᵥ (B *ᵥ v) := by abel
    have h4 := Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2
    simp only at h4
    rw [← this] at h4
    exact h4
  have hu : IsUnit C0 := Matrix.mulVec_surjective_iff_isUnit.1 hs
  obtain ⟨C, hC⟩ := hu
  have hCk : ∀ k i, C.1 k i = col i k := fun k i => by rw [hC]; rfl
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i j h k
    have h1 : i.val < m := h ▸ j.2
    rw [hCk]
    simp only [col, dif_pos h1]
    congr 1
    exact Fin.ext h
  · intro i j h k
    have hj := j.2
    have e1 : ¬ (i.val < m) := by omega
    have e2 : ¬ (i.val + m < n) := by omega
    rw [hCk]
    simp only [col, dif_neg e1, dif_neg e2]
    congr 1
    exact Fin.ext (by simp; omega)
  · intro i h1 h2
    have e1 : ¬ (i.val < m) := by omega
    have : (fun k => C.1 k i) = (b ⟨i.val - m, by have := i.2; omega⟩ : K).1 := by
      funext k
      rw [hCk]
      simp only [col, dif_neg e1, dif_pos h2]
    rw [this]
    exact (hmem _).1 (b _).2

theorem exists_isAdapted : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∃ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C := by
  intro D V m X Y hW
  have hyx := GlobalTheory.WittFrame.yx_eq_one D V m X Y hW
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  obtain ⟨hle, C, h1, h2, h3⟩ := exists_basis_of_duality X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) hyx hyy hxx hxy
  exact ⟨C, ⟨hle, h1, h2, fun i a b => (h3 i a b).2, fun i a b => (h3 i a b).1⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis
end

