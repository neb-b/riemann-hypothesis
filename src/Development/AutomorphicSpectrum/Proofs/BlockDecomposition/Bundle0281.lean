module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.LocTors

theorem chartIn_map {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) {N M : Type} [AddCommGroup N]
    [Module Γ(X, V) N] [AddCommGroup M] [Module Γ(X, V) M] (g : N →ₗ[Γ(X, V)] M)
    {T : Submodule Γ(X, V) N} {T' : Submodule Γ(X, V) M} (hT : T.map g ≤ T') {x : N}
    (hx : ChartIn φ V T x) : ChartIn φ V T' (g x) := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  obtain ⟨y, hy⟩ := hx U hU h
  let g' : T →ₗ[Γ(X, V)] T' := (g.comp T.subtype).codRestrict T' (fun t => hT ⟨t, t.2, rfl⟩)
  refine ⟨g'.rTensor Γ(Z, U) y, ?_⟩
  have hc : T'.subtype.comp g' = g.comp T.subtype := rfl
  change (T'.subtype.rTensor Γ(Z, U)) (g'.rTensor Γ(Z, U) y) = g x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U))
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hy, LinearMap.rTensor_tmul]

theorem eq_zero_of_mem_pow {B R M : Type} [CommRing B] [CommRing R] [IsNoetherianRing R]
    [Algebra B R] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] (I : Ideal B) (hjac : I.map (algebraMap B R) ≤ Ideal.jacobson ⊥) (m : M)
    (hm : ∀ n, m ∈ (I ^ (n + 1) • ⊤ : Submodule B M)) : m = 0 := by
  set IR : Ideal R := I.map (algebraMap B R)
  have key : ∀ n, m ∈ (IR ^ n • ⊤ : Submodule R M) := by
    intro n
    have h1 : (I ^ (n + 1) • ⊤ : Submodule B M) ≤ (IR ^ (n + 1) • ⊤ : Submodule R M).restrictScalars B := by
      rw [Submodule.smul_le]
      intro a ha u _
      rw [Submodule.restrictScalars_mem, algebraMap_smul R a u |>.symm]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h2 : algebraMap B R a ∈ (I ^ (n + 1)).map (algebraMap B R) := Ideal.mem_map_of_mem _ ha
      rwa [Ideal.map_pow] at h2
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (h1 (hm n))
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) IR (by simpa only [Ideal.jacobson_bot] using hjac)
  have : m ∈ (⨅ n : ℕ, IR ^ n • (⊤ : Submodule R M)) := Submodule.mem_iInf _ |>.2 key
  rw [hK] at this
  exact (Submodule.mem_bot R).1 this

theorem adjKer_pow_smul_mem_secs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme) (hψ : IsProper ψ)
    (hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    (W : J.subscheme.Opens) (hW : IsIso (ψ ∣_ W)) {E : X.Modules} (hE : IsCoherent E)
    {S : ℕ → Subobject E} (hS : ClosedSys I E S) (hK : ∀ e, Killed J (S e))
    (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E))
    (hB : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e)
    (V : X.affineOpens) (f : Γ(X, V)) (hf : J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W)
    (x : Γ(E, V)) (hx : x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V) :
    ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V) Γ(E, V) := hE.2 V V.2
  haveI : E.IsQuasicoherent := hE.1
  set IB : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) (V : X.Opens)) I with hIB
  have hpow : ∀ n, Ideal.map (toFunctions (A := A) (V : X.Opens)) (I ^ n) = IB ^ n :=
    fun n => Ideal.map_pow _ _ _
  let T : ℕ → Submodule Γ(X, V) Γ(E, V) := fun n => secsSub (S n) V
  have hpowsecs : ∀ n, secs (powSub I E n) (V : X.Opens) =
      ((IB ^ n • ⊤ : Submodule Γ(X, (V : X.Opens)) Γ(E, (V : X.Opens))) : Set Γ(E, (V : X.Opens))) := by
    intro n
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 n V V.2, hpow]
  have h1 : ∀ n, IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ≤ T n := by
    intro n y hy
    have hy' : y ∈ secs (powSub I E (n + 1)) V := by rw [hpowsecs]; exact hy
    exact (_root_.GlobalTheory.CompanionTheory.GE.le_iff_secs_subset _ _).1 (hS.pow_le n) V hy'
  have h2 : ∀ n, T n = T (n + 1) ⊔ IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    intro n
    have hq : (powSub I E (n + 1) : X.Modules).IsQuasicoherent := (closedSys_pow I E).qcoh n
    obtain ⟨_, hsum⟩ := GlobalTheory.T.quasicoherent_sup_sections hE.1 (S (n + 1)) (powSub I E (n + 1)) (hS.qcoh (n + 1)) hq
    ext y
    change y ∈ secs (S n) V ↔ _
    rw [hS.succ n, hsum V V.2, Submodule.mem_sup]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      have ht' : t ∈ ((IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
        rw [← hpowsecs]; exact ht
      exact ht'
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      rw [hpowsecs]
      exact ht
  obtain ⟨R, firstRealIndex, secondRealIndex, iR3, M, familyMassRatio, familyMassSecondLine, iM3, iM4, iM5, μ, hjac, hspan, hiff⟩ :=
    _root_.GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower IB T h1 h2
  have hJ : ∀ a ∈ J.ideal ⟨(V : X.Opens), V.2⟩, ∀ m : M, a • m = 0 := by
    intro a ha m
    have hm : m ∈ Submodule.span R (Set.range μ) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun m _ => a • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨e, rfl⟩
      apply eq_zero_of_mem_pow IB hjac
      intro n
      rw [← map_smul]
      exact (hiff n (a • e)).1 (hK n V a ha e)
    · exact smul_zero a
    · intro u v _ _ hu hv
      rw [smul_add, hu, hv, add_zero]
    · intro r u _ hu
      rw [smul_comm a r u, hu, smul_zero]
  have hIso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) :=
    GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le ψ hf
  have hch := _root_.GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer I (ψ ≫ J.subschemeι) hover hE hS B hB (V : X.Opens) V.2 x hx
  have hch' : ∀ n, ChartIn (ψ ≫ J.subschemeι) (V : X.Opens)
      (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) (μ x) := by
    intro n
    refine chartIn_map _ _ μ ?_ (hch n)
    rintro _ ⟨e, he, rfl⟩
    exact (hiff n e).1 he
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn J ψ hψ (V : X.Opens) V.2 IB hjac hJ f hIso (μ x) hch'
  refine ⟨k, fun n => ?_⟩
  have hμ : μ (f ^ k • x) ∈ (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) := by
    rw [map_smul, hk]
    exact Submodule.zero_mem _
  exact (hiff n _).2 hμ

end GlobalTheory.CompanionTheory.GE.LocTors
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHaarMeasure
section
open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FactS.OpenFactor

section Generic

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) : (μ.comap e).map e = μ := by
  rw [he.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hμ)

theorem comap_invariant {e : Y → X} (he : MeasurableEmbedding e) {a : X → X} {a' : Y → Y}
    (ha : Measurable a) (ha' : Measurable a') (hcomm : ∀ y, e (a' y) = a (e y)) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (hinv : μ.map a = μ) : (μ.comap e).map a' = μ.comap e := by
  have hν := map_comap_of_carried he hμ
  have h2 : ((μ.comap e).map a').map e = μ := by
    rw [Measure.map_map he.measurable ha']
    have h3 : e ∘ a' = a ∘ e := funext hcomm
    rw [h3, ← Measure.map_map ha he.measurable, hν, hinv]
  have h4 := he.comap_map ((μ.comap e).map a')
  rw [h2] at h4
  exact h4.symm

theorem lintegral_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (G : X → ℝ≥0∞) :
    ∫⁻ y, G (e y) ∂(μ.comap e) = ∫⁻ x, G x ∂μ := by
  rw [← he.lintegral_map, map_comap_of_carried he hμ]

theorem comap_ne_zero_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (h0 : μ ≠ 0) : μ.comap e ≠ 0 := by
  intro h
  have h1 := map_comap_of_carried he hμ
  rw [h, Measure.map_zero] at h1
  exact h0 h1.symm

theorem comap_finite_compacts [TopologicalSpace X] [TopologicalSpace Y] {e : Y → X}
    (he : MeasurableEmbedding e) (hc : Continuous e) {S : Set X} (hS : ∀ y, e y ∈ S)
    {μ : Measure X} (hfin : ∀ K, IsCompact K → K ⊆ S → μ K < ⊤) :
    IsFiniteMeasureOnCompacts (μ.comap e) :=
  ⟨fun K hK => by
    rw [he.comap_apply]
    exact hfin _ (hK.image hc) (by rintro _ ⟨y, -, rfl⟩; exact hS y)⟩

end Generic

theorem prod_factor_open : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  intro ι _ G₀ _ _ _ _ _ _ G _ _ _ _ _ _ W₀ _ _ _ _ _ _ W _ _ _ _ _ _
    a₀ a hc₀ h1₀ hm₀ hc h1 hm U₀ U hU₀ hU hsU₀ hsU Z₀ Z hZ₀ hZ hs₀ hs ht₀ ht m₀ m hfin₀ hfin
    hi₀ hi hz₀ hz hn₀ hn P hPc hP hPZ
  classical
  haveI : LocallyCompactSpace ↥U₀ := hU₀.locallyCompactSpace
  haveI : ∀ i, LocallyCompactSpace ↥(U i) := fun i => (hU i).locallyCompactSpace
  have hmeas₀ : ∀ g, Measurable (a₀ g) := fun g =>
    (hc₀.comp (Continuous.prodMk_right g)).measurable
  have hmeas : ∀ i g, Measurable (a i g) := fun i g =>
    ((hc i).comp (Continuous.prodMk_right g)).measurable
  let b₀ : G₀ → ↥U₀ → ↥U₀ := fun g x => ⟨a₀ g x.1, hsU₀ g x.1 x.2⟩
  let b : ∀ i, G i → ↥(U i) → ↥(U i) := fun i g x => ⟨a i g x.1, hsU i g x.1 x.2⟩
  let E : (↥U₀ × ∀ i, ↥(U i)) → W₀ × ∀ i, W i := Prod.map Subtype.val fun z i => (z i).1
  have he₀ : MeasurableEmbedding (Subtype.val : ↥U₀ → W₀) :=
    MeasurableEmbedding.subtype_coe hU₀.measurableSet
  have he : ∀ i, MeasurableEmbedding (Subtype.val : ↥(U i) → W i) := fun i =>
    MeasurableEmbedding.subtype_coe (hU i).measurableSet
  have hEo : IsOpenEmbedding E :=
    hU₀.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.piMap fun i => (hU i).isOpenEmbedding_subtypeVal)
  have hE : MeasurableEmbedding E := hEo.measurableEmbedding
  have hcar₀ : m₀ (Set.range (Subtype.val : ↥U₀ → W₀))ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hz₀
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcar : ∀ i, m i (Set.range (Subtype.val : ↥(U i) → W i))ᶜ = 0 := fun i => by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hz i)
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcarP : P (Set.range E)ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hPZ
    rintro ⟨x, z⟩ ⟨h₀, hz'⟩
    exact ⟨(⟨x, h₀.2⟩, fun i => ⟨z i, (hz' i (Set.mem_univ i)).2⟩), rfl⟩
  haveI : IsFiniteMeasureOnCompacts (m₀.comap (Subtype.val : ↥U₀ → W₀)) :=
    comap_finite_compacts he₀ continuous_subtype_val (fun y => y.2) (hfin₀)
  haveI : ∀ i, IsFiniteMeasureOnCompacts ((m i).comap (Subtype.val : ↥(U i) → W i)) := fun i =>
    comap_finite_compacts (he i) continuous_subtype_val (fun y => y.2) (hfin i)
  haveI : IsFiniteMeasureOnCompacts (P.comap E) :=
    comap_finite_compacts hE hEo.continuous (S := Set.univ) (fun _ => Set.mem_univ _)
      (fun K hK _ => hK.measure_lt_top)
  have hcb₀ : Continuous fun p : G₀ × ↥U₀ => b₀ p.1 p.2 :=
    Continuous.subtype_mk (hc₀.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hcb : ∀ i, Continuous fun p : G i × ↥(U i) => b i p.1 p.2 := fun i =>
    Continuous.subtype_mk ((hc i).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hmb₀ : ∀ g, Measurable (b₀ g) := fun g =>
    (hcb₀.comp (Continuous.prodMk_right g)).measurable
  have hmb : ∀ i g, Measurable (b i g) := fun i g =>
    ((hcb i).comp (Continuous.prodMk_right g)).measurable
  obtain ⟨c, hcf⟩ := prod_factor (G₀ := G₀) (G := G) (W₀ := ↥U₀) (W := fun i => ↥(U i)) b₀ b
    hcb₀ (fun x => Subtype.ext (h1₀ x.1)) (fun g h x => Subtype.ext (hm₀ g h x.1))
    hcb (fun i x => Subtype.ext (h1 i x.1)) (fun i g h x => Subtype.ext (hm i g h x.1))
    (Subtype.val ⁻¹' Z₀) (fun i => Subtype.val ⁻¹' Z i)
    (hZ₀.preimage continuous_subtype_val) (fun i => (hZ i).preimage continuous_subtype_val)
    (fun g x hx => hs₀ g x.1 hx) (fun i g x hx => hs i g x.1 hx)
    (fun x hx y hy => by
      obtain ⟨g, hg⟩ := ht₀ x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (fun i x hx y hy => by
      obtain ⟨g, hg⟩ := ht i x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (m₀.comap Subtype.val) (fun i => (m i).comap Subtype.val)
    (fun g => comap_invariant he₀ (hmeas₀ g) (hmb₀ g) (fun _ => rfl) hcar₀ (hi₀ g))
    (fun i g => comap_invariant (he i) (hmeas i g) (hmb i g) (fun _ => rfl) (hcar i) (hi i g))
    (by
      rw [he₀.comap_apply]
      refine measure_mono_null ?_ hz₀
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun i => by
      rw [(he i).comap_apply]
      refine measure_mono_null ?_ (hz i)
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun ⟨x, hx⟩ => comap_ne_zero_of_carried he₀ hcar₀ (hn₀ ⟨x.1, hx, x.2⟩))
    (fun i ⟨x, hx⟩ => comap_ne_zero_of_carried (he i) (hcar i) (hn i ⟨x.1, hx, x.2⟩))
    (P.comap E)
    (fun g₀ g => comap_invariant hE
      (a := fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i)))
      ((hmeas₀ g₀).comp measurable_fst |>.prodMk (Measurable.of_eval fun i =>
        (hmeas i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      ((hmb₀ g₀).comp measurable_fst |>.prodMk (Measurable.of_eval fun i =>
        (hmb i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      (fun _ => rfl) hcarP (hP g₀ g))
    (by
      rw [hE.comap_apply]
      refine measure_mono_null ?_ hPZ
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy ⟨hmem.1.1, fun i _ => (hmem.2 i (Set.mem_univ i)).1⟩)
  refine ⟨c, fun f₀ f hf₀ hf => ?_⟩
  have h := hcf (fun x => f₀ x.1) (fun i x => f i x.1) (hf₀.comp measurable_subtype_coe)
    (fun i => (hf i).comp measurable_subtype_coe)
  have hL := lintegral_comap_of_carried hE hcarP fun x => f₀ x.1 * ∏ i, f i (x.2 i)
  have hL₀ := lintegral_comap_of_carried he₀ hcar₀ f₀
  have hLi := fun i => lintegral_comap_of_carried (he i) (hcar i) (f i)
  rw [← hL, ← hL₀]
  simp only [← hLi]
  exact h

end GlobalTheory.CompanionTheory.SW.FactS.OpenFactor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotent
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

end GlobalTheory.CompanionTheory.HeckeSub
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoSetLIntegralDiffCompactCovering
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.MeasureTails

theorem tendsto_setLIntegral_diff_compactCovering
    {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    [SigmaCompactSpace α] (μ : Measure α) (F : Set α) (h : α → ℝ≥0∞)
    (hfin : ∫⁻ x in F, h x ∂μ < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x in F \ compactCovering α k, h x ∂μ) atTop (𝓝 0) := by
  set m : Measure α := (μ.restrict F).withDensity h with hm
  have hmeas : ∀ k : ℕ, MeasurableSet (compactCovering α k)ᶜ := fun k =>
    ((isCompact_compactCovering α k).isClosed.measurableSet).compl
  have hrew : ∀ k : ℕ, ∫⁻ x in F \ compactCovering α k, h x ∂μ = m (compactCovering α k)ᶜ := by
    intro k
    rw [hm, withDensity_apply h (hmeas k), Measure.restrict_restrict (hmeas k), Set.diff_eq,
      Set.inter_comm]
  have huniv : m Set.univ < ⊤ := by
    rw [hm, withDensity_apply h MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hanti : Antitone (fun k : ℕ => (compactCovering α k)ᶜ) := fun i j hij =>
    Set.compl_subset_compl.mpr (compactCovering_subset α hij)
  have hinter : ⋂ k : ℕ, (compactCovering α k)ᶜ = ∅ := by
    rw [← Set.compl_iUnion, iUnion_compactCovering, Set.compl_univ]
  have hne : ∃ k : ℕ, m (compactCovering α k)ᶜ ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top huniv.ne (measure_mono (Set.subset_univ _))⟩
  have key := tendsto_measure_iInter_atTop (μ := m)
    (fun k => (hmeas k).nullMeasurableSet) hanti hne
  rw [hinter, measure_empty] at key
  simp only [hrew]
  exact key

end GlobalTheory.CompanionTheory.MeasureTails
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
section
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
end
end

