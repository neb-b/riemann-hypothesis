module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBase
section
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreShift

theorem comp_shift_props {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by
  have hC : IsCompact (T' '' tsupport φ) := hc.isCompact.image_of_continuousOn (hT'.mono hs)
  have hCW : T' '' tsupport φ ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmem' w).2 (hs hw)
  have hsup : ∀ v, v ∉ T' '' tsupport φ → φ (T v) = 0 := by
    intro v hv
    by_contra h
    have h1 : T v ∈ tsupport φ := subset_tsupport _ h
    exact hv ⟨T v, h1, hinv v ((hmem v).1 (hs h1))⟩
  have hts : tsupport (fun v => φ (T v)) ⊆ T' '' tsupport φ := by
    refine closure_minimal ?_ hC.isClosed
    intro v hv
    by_contra h
    exact hv (hsup v h)
  refine ⟨continuous_of_tsupport fun v hv => ?_, HasCompactSupport.intro hC hsup, hts.trans hCW⟩
  exact ContinuousAt.comp (g := φ) hφ.continuousAt (hT.continuousAt (hW.mem_nhds (hCW (hts hv))))

theorem continuous_lintegral {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {ι : X → Y} {U : Set V} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {φ : V → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc hs
  have hcont : Continuous fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
    ENNReal.continuous_ofReal.comp (continuousOn_univ.1 hc1)
  exact hcont.congr fun b =>
    ofReal_integral_eq_lintegral_ofReal (hi b (Set.mem_univ b)) (Filter.Eventually.of_forall h0)

theorem setLIntegral_eq_lintegral {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by
  rw [← lintegral_indicator hW]
  congr 1
  funext v
  by_cases hv : v ∈ W
  · rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, ha v hv]

theorem lintegral_shift {V X Y : Type} [TopologicalSpace V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure V} {ν : Measure X} [ν.IsAddHaarMeasure] {f : V → Y} {g : V → X}
    {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {U W : Set V} (hW : IsOpen W) (hWU : W ⊆ U) {fib : X → Measure V}
    (hF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {T : X → V → V}
    (hTm : ∀ s, Measurable (T s)) (hTμ : ∀ s, μ.map (T s) = μ)
    (hTc : ∀ s, ContinuousOn (T s) W) (hTW : ∀ s v, T s v ∈ W ↔ v ∈ W)
    (hinv : ∀ s, ∀ v ∈ W, T (-s) (T s v) = v) (hgT : ∀ s, ∀ v ∈ W, g (T s v) = g v + s)
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ W)
    (h0 : ∀ v, 0 ≤ φ v) (s c : X) :
    ∫⁻ v, ENNReal.ofReal (φ (T s v)) ∂(fib c) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (c + s)) := by
  obtain ⟨hφs, hcs, hss⟩ :=
    comp_shift_props hW (hTc s) (hTc (-s)) (hTW s) (hTW (-s)) (hinv s) hφ hc hs
  have hψm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hψ0 : ∀ v, v ∉ W → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hψs0 : ∀ v, v ∉ W → ENNReal.ofReal (φ (T s v)) = 0 :=
    fun v hv => hψ0 _ fun h => hv ((hTW s v).1 h)
  have hD := continuous_lintegral hF hφ hc (hs.trans hWU) h0
  have hD' := continuous_lintegral hF hφs hcs (hss.trans hWU) (fun v => h0 _)
  have hDs : Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (b + s)) :=
    hD.comp (continuous_add_const s)
  refine _root_.GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq X ν Set.univ isOpen_univ _ _ hD'.continuousOn hDs.continuousOn
    (fun S hS _ => ?_) c (Set.mem_univ c)
  have hSm := hS.measurableSet
  have hS'm : MeasurableSet ((fun x : X => x - s) ⁻¹' S) :=
    (continuous_sub_right s).measurable hSm
  have e1 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ (T s v))) (hψm.comp (hTm s)) hψs0 S hSm
  have e2 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'm
  have hAm : Measurable ((g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      fun v => ENNReal.ofReal (φ v)) := hψm.indicator (hg.measurable hS'm)
  have hA0 : ∀ v, v ∉ W → (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      (fun v => ENNReal.ofReal (φ v)) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψ0 v hv
  have hB0 : ∀ v, v ∉ W → (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψs0 v hv
  have hcomp : ∀ v, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v =
      (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator (fun v => ENNReal.ofReal (φ v)) (T s v) := by
    intro v
    by_cases hv : v ∈ W
    · have hiff : T s v ∈ g ⁻¹' ((fun x : X => x - s) ⁻¹' S) ↔ v ∈ g ⁻¹' S := by
        simp only [Set.mem_preimage, hgT s v hv, add_sub_cancel_right]
      by_cases hvS : v ∈ g ⁻¹' S
      · rw [Set.indicator_of_mem hvS, Set.indicator_of_mem (hiff.2 hvS)]
      · rw [Set.indicator_of_notMem hvS, Set.indicator_of_notMem (fun h => hvS (hiff.1 h))]
    · rw [hB0 v hv, hA0 _ fun h => hv ((hTW s v).1 h)]
  have hmid : ∫⁻ v in W, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v ∂μ =
      ∫⁻ v in W, (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
        (fun v => ENNReal.ofReal (φ v)) v ∂μ := by
    rw [setLIntegral_eq_lintegral hW.measurableSet hB0,
      setLIntegral_eq_lintegral hW.measurableSet hA0]
    simp only [hcomp]
    rw [← lintegral_map hAm (hTm s), hTμ s]
  have hpre : (fun x : X => x + s) ⁻¹' ((fun x : X => x - s) ⁻¹' S) = S := by
    ext x
    simp
  have htr := (measurePreserving_add_right ν s).setLIntegral_comp_preimage hS'm hD.measurable
  rw [hpre] at htr
  rw [← e1, hmid, e2, ← htr]

theorem fib_ne_zero : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf U W hW hWU hne fib hF T hTm hTμ
    hTc hTW hinv hgT b hb
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨φ, hφ, hc, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
    (isCompact_singleton (x := v₀)) hW (Set.singleton_subset_iff.2 hv₀)
  have hzero : ∀ c, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = 0 := by
    intro c
    have key := lintegral_shift hι hg hf hW hWU hF hTm hTμ hTc hTW hinv hgT hφ hc hs h0 (c - b) b
    rw [add_sub_cancel] at key
    rw [← key, hb]
    simp
  have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have h2 := hF.2.1 _ hm
  simp only [hzero, lintegral_zero] at h2
  have h3 : ∫⁻ v in W, ENNReal.ofReal (φ v) ∂μ = 0 :=
    le_antisymm (h2 ▸ lintegral_mono_set hWU) bot_le
  have hae := (ae_restrict_iff' hW.measurableSet).1 ((lintegral_eq_zero_iff hm).1 h3)
  have hOpen : IsOpen ({v | 0 < φ v} ∩ W) := (isOpen_lt continuous_const hφ).inter hW
  have hpos : 0 < μ ({v | 0 < φ v} ∩ W) :=
    hOpen.measure_pos μ ⟨v₀, by simp [h1 v₀ rfl], hv₀⟩
  have hnull := ae_iff.1 hae
  refine hpos.ne' (measure_mono_null ?_ hnull)
  intro v hv
  rw [Set.mem_setOf_eq]
  intro hcon
  have h4 := hcon hv.2
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact absurd hv.1 (not_lt.2 h4)

end GlobalTheory.CompanionTheory.SW.FibreShift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSection
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSections

theorem exists_algHom_away_of_etale {S : Type} [CommRing S]
    (hA : Aic (S := S)) (hL : Loc (S := S))
    (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [hQ : Q.IsPrime]
    (hm : (Q.comap (algebraMap S B)).IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hQ' : (Q.map (algebraMap B Bg)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : (Q.map (algebraMap B Bg)).comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hc : (Q.map (algebraMap B Bg)).comap (algebraMap S Bg) = Q.comap (algebraMap S B) := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap]
  let q := Q.map (algebraMap B Bg)
  have hqm : (q.comap (algebraMap S Bg)).IsMaximal := hc ▸ hm
  have hsection : ∃ e : S, IsIdempotentElem e ∧ e ∉ q.comap (algebraMap S Bg) ∧
      Nonempty (Bg →ₐ[S] Localization.Away e) := by
    obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
    obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f

    have hprod : (s.map fun b => P.x - algebraMap S Bg b).prod ∈ q := by
      have h0 : Polynomial.aeval P.x P.f = 0 := P.hasMap.1
      rw [hs, map_multiset_prod, Multiset.map_map] at h0
      have : (s.map fun b => P.x - algebraMap S Bg b).prod = 0 := by
        rw [← h0]
        congr 1
        apply Multiset.map_congr rfl
        intro b _
        simp
      rw [this]
      exact q.zero_mem
    obtain ⟨b, hbs, hbQ⟩ :=
      GlobalTheory.CompanionTheory.EtaleSection.exists_sub_mem_of_prod_mem q hQ' P.x s hprod
    have hroot : Polynomial.eval b P.f = 0 := by
      have hd : (Polynomial.X - Polynomial.C b) ∣ P.f := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact Polynomial.dvd_iff_isRoot.1 hd

    set c : S := Polynomial.eval b P.g with hc
    have hcm : c ∉ q.comap (algebraMap S Bg) := by
      intro hcQ
      have hcQ' : algebraMap S Bg c ∈ q := hcQ
      have hd : P.x - algebraMap S Bg b ∣
          Polynomial.aeval P.x P.g - algebraMap S Bg c := by
        have := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
        rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
          Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at this
      have hgQ : Polynomial.aeval P.x P.g ∈ q := by
        have h1 := Ideal.mem_of_dvd q hd hbQ
        simpa using q.add_mem h1 hcQ'
      exact hQ'.ne_top (Ideal.eq_top_of_isUnit_mem q hgQ P.hasMap.2)

    obtain ⟨a, μ, hμ, haμ⟩ := hqm.exists_inv hcm
    obtain ⟨e, he, hec, he1⟩ := hL (a * c)
    have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
    have he1m : 1 - e ∈ q.comap (algebraMap S Bg) := by
      rw [h1ac] at he1
      exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
    have hem : e ∉ q.comap (algebraMap S Bg) := by
      intro hem
      have : (1 : S) ∈ q.comap (algebraMap S Bg) := by
        simpa using Ideal.add_mem _ hem he1m
      exact hqm.ne_top ((Ideal.eq_top_iff_one _).2 this)
    refine ⟨e, he, hem, ?_⟩

    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
    have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
      IsLocalization.Away.algebraMap_isUnit e
    have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
      have : algebraMap S (Localization.Away e) e =
          algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
        rw [← map_mul, ← hr]; ring_nf
      rw [this] at heu
      exact isUnit_of_mul_isUnit_right heu
    have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
      refine ⟨?_, ?_⟩
      · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]
      · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
        exact hcu
    exact ⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := hsection
  exact ⟨e, he, hc ▸ hem, ⟨ψ.comp (IsScalarTower.toAlgHom S B Bg)⟩⟩

theorem exists_secOn_of_etale_surjective : ∀ {S : Type} [CommRing S],
    Aic (S := S) → Loc (S := S) →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.Etale S Γ(Y, V) := RingHom.etale_algebraMap.1 hφe
  have hyr : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨z, hz⟩ := hyr
  have hcm : z.asIdeal.comap (algebraMap S Γ(Y, V)) = m := by
    have h1 : (Spec.map φ) z = x := by
      rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal h1
  have : z.asIdeal.IsPrime := z.2
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := exists_algHom_away_of_etale hA hL Γ(Y, V) z.asIdeal (by rw [hcm]; exact hm)
  refine ⟨e, he, hcm ▸ hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

end GlobalTheory.CompanionTheory.EtaleSections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
section
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi

noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩

theorem fourier_sub_translate_eq_zero [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (μ : Measure (Fin n → k)) [μ.IsAddHaarMeasure]
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k)))
    (hAo : IsOpen (A : Set (Fin n → k))) (x : Fin n → k)
    (hx : ∀ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) → ψ (η ⬝ᵥ x) = 1) (y : Fin n → k) :
    ∫ z, ((A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) z -
        (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hc : Continuous fun z : Fin n → k => (ψ (z ⬝ᵥ y) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  have hi1 : Integrable (fun z => g z * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    (hg.1.continuous.mul hc).integrable_of_hasCompactSupport hg.2.mul_right
  have hgx : HasCompactSupport fun z => g (z + x) := hg.2.comp_homeomorph (Homeomorph.addRight x)
  have hi2 : Integrable (fun z => g (z + x) * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    ((hg.1.continuous.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport
      hgx.mul_right
  have e1 : ∫ z, g (z + x) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ =
      (ψ (-(x ⬝ᵥ y)) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
    have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ ((w - x) ⬝ᵥ y) : ℂ)) x
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hwx : (w - x) ⬝ᵥ y = w ⬝ᵥ y + -(x ⬝ᵥ y) := by rw [sub_dotProduct, sub_eq_add_neg]
    beta_reduce
    rw [hwx, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, e1]
  by_cases hy : ∀ a ∈ A, ψ (y ⬝ᵥ a) = 1
  · have h1 : ψ (x ⬝ᵥ y) = 1 := by rw [dotProduct_comm]; exact hx y hy
    have h2 : ψ (-(x ⬝ᵥ y)) = 1 := by rw [AddChar.map_neg_eq_inv, h1, inv_one]
    simp [h2]
  · push Not at hy
    obtain ⟨a, haA, hne⟩ := hy
    have h0 : ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
      have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ (w ⬝ᵥ y) : ℂ)) a
      have h3 : ∫ z, g (z + a) * (ψ ((z + a) ⬝ᵥ y) : ℂ) ∂μ =
          (ψ (y ⬝ᵥ a) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        have hga : g (w + a) = g w := by
          by_cases hw : w ∈ A
          · simp [hgdef, Set.indicator, hw, A.add_mem hw haA]
          · have : w + a ∉ A := fun h => hw (by simpa using A.sub_mem h haA)
            simp [hgdef, Set.indicator, hw, this]
        simp only [hga, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm a y]
        ring
      rw [h3] at h
      have h4 : (1 - (ψ (y ⬝ᵥ a) : ℂ)) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, h, sub_self]
      refine (mul_eq_zero.1 h4).resolve_left fun h5 => hne (Circle.ext ?_)
      simpa using (sub_eq_zero.1 h5).symm
    simp [h0]

theorem exists_annihilator_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0

end GlobalTheory.CompanionTheory.CharacterBiduality
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemInfConjOfIsDom
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirst
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLen

theorem isFiniteLength_of_ker_le_range {W : Type} [CommRing W] {A B C : Type 1}
    [AddCommGroup A] [Module W A] [AddCommGroup B] [Module W B] [AddCommGroup C] [Module W C]
    (v : A →ₗ[W] B) (f : B →ₗ[W] C) (h : LinearMap.ker f ≤ LinearMap.range v)
    (hA : IsFiniteLength W A) (hC : IsFiniteLength W C) : IsFiniteLength W B := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA hC ⊢
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  have n1 : IsNoetherian W (LinearMap.range v) :=
    isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)
  have a1 : IsArtinian W (LinearMap.range v) :=
    isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict
  have n2 : IsNoetherian W (LinearMap.ker f) :=
    isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have a2 : IsArtinian W (LinearMap.ker f) :=
    isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict := by
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact ⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩

theorem isFiniteLength_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  intro W _ l S S' L h1 n
  induction n with
  | zero =>
    have : Subsingleton (S.M 0) := ⟨fun x y => by
      have hx := L.kill 0 x
      have hy := L.kill 0 y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    refine isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih
    intro x hx
    obtain ⟨y, hy⟩ := L.ex₁ 1 n (n + 1) (by omega) x hx
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.TowerLen
end

