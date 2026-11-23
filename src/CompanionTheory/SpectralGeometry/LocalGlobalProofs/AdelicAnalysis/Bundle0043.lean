module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0005
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarInvariantUnitaryAction
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarInv

def tupEquiv {K A : Type} [AddCommGroup K] [TopologicalSpace K] [AddCommGroup A] [TopologicalSpace A]
    {M d : ℕ} (Φ : K ≃ₜ (Fin d → A)) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y) :
    (Fin 1 → Fin M → K) ≃ₜ+ (Fin M × Fin d → A) where
  toFun X p := Φ (X 0 p.1) p.2
  invFun Y _ i := Φ.symm fun k => Y (i, k)
  left_inv X := by
    funext a i
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp
  right_inv Y := by
    funext p
    simp
  map_add' X Y := by
    funext p
    simp [hadd]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (Φ.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  continuous_invFun := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact Φ.symm.continuous.comp (continuous_pi fun k => continuous_apply (i, k))

theorem map_eq_of_conj {V W : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ W) (μ : Measure V)
    (T : V → V) (G : W → W) (hG : Measurable G) (hc : ∀ x, e (T x) = G (e x))
    (hinv : (μ.map e).map G = μ.map e) : μ.map T = μ := by
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hT : T = e.symm ∘ G ∘ e := by
    funext x
    simp [← hc x]
  calc μ.map T = ((μ.map e).map G).map e.symm := by
        rw [Measure.map_map hG he, Measure.map_map hes (hG.comp he), hT]
    _ = (μ.map e).map e.symm := by rw [hinv]
    _ = μ := by
        rw [Measure.map_map hes he]
        simp

end GlobalTheory.CompanionTheory.SW.HaarInv

open GlobalTheory.CompanionTheory.SW.HaarInv in
theorem GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ μ _ h
  obtain ⟨⟨i3, i4, i5⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  letI : MeasurableSpace (AF F) := borel (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨iR, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hBor 1 M
  let b := Module.finBasis F E
  obtain ⟨B, -, hBdet, hB⟩ := GlobalTheory.CompanionTheory.SW.CoordMat.coord_orthogonal F E σ hσ M J hJ _ b
  obtain ⟨g, hg, hconj⟩ := hB (AF F) h
  let Φ := GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (AF F) b
  have hadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by
    funext k
    simp [Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo]
  let e := tupEquiv (M := M) Φ hadd
  have hcomm : ∀ X, e.toHomeomorph (actW (AF F) σ J h X) = (fun x => g *ᵥ x) (e.toHomeomorph X) := by
    intro X
    have := hconj X
    funext p
    have hp := congrFun this p
    simpa [e, tupEquiv, Φ, GlobalTheory.CompanionTheory.SW.TopK.coordHomeo] using hp
  have hdet : IsUnit (B.map (algebraMap F (AF F))).det := by
    have : (B.map (algebraMap F (AF F))).det = algebraMap F (AF F) B.det := by
      rw [RingHom.map_det]
      rfl
    rw [this]
    exact (Ne.isUnit hBdet).map _
  haveI : (μ.map e.toHomeomorph).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hinv : (μ.map e.toHomeomorph).map (fun x => g *ᵥ x) = μ.map e.toHomeomorph :=
    GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq (AF F) (GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one F) _ (μ.map e.toHomeomorph) (B.map (algebraMap F (AF F))) g hdet hg
  exact map_eq_of_conj e.toHomeomorph μ (actW (AF F) σ J h) (fun x => g *ᵥ x)
    (continuous_const.matrix_mulVec continuous_id).measurable hcomm hinv
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdele
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicFlow

theorem map_eq_smul_of_scale {V W G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G]
    (Φ : G ≃ₜ+ V × W) (φ : G → G) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ x, Φ (φ x) = (t • (Φ x).1, (Φ x).2))
    (μ : Measure G) [μ.IsAddHaarMeasure] :
    μ.map φ = ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| • μ := by
  set k := ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| with hk
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  let ν : Measure V := Measure.addHaar
  let ρ : Measure W := Measure.addHaar
  let ψ : V × W → V × W := Prod.map (fun v => t • v) id
  have hψ : Measurable ψ := (measurable_const_smul t).prodMap measurable_id
  haveI : (μ.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) (ν.prod ρ)
  set c := Measure.addHaarScalarFactor (μ.map Φ) (ν.prod ρ) with hcdef
  have hπ : (μ.map Φ).map ψ = k • μ.map Φ := by
    have h1 : (ν.prod ρ).map ψ = k • ν.prod ρ := by
      have := Measure.map_prod_map ν ρ (f := fun v : V => t • v) (g := (id : W → W))
        (measurable_const_smul t) measurable_id
      rw [show (ν.prod ρ).map ψ = (ν.map fun v => t • v).prod (ρ.map id) from this.symm,
        Measure.map_addHaar_smul ν ht, Measure.map_id, Measure.prod_smul_left]
    rw [hc, Measure.map_smul c hψ.aemeasurable, h1, smul_comm]
  have hφ : φ = Φ.symm ∘ ψ ∘ Φ := by
    funext x
    apply Φ.injective
    simp [h]
    rfl
  have hμ : (μ.map Φ).map Φ.symm = μ := by
    rw [Measure.map_map hΦs hΦ]
    simp
  calc μ.map φ = ((μ.map Φ).map ψ).map Φ.symm := by
        rw [Measure.map_map hΦs hψ, Measure.map_map (hΦs.comp hψ) hΦ, hφ]; rfl
    _ = k • μ := by rw [hπ, Measure.map_smul k hΦs.aemeasurable, hμ]

section Adelic

variable (F : Type) [Field F] [NumberField F]

noncomputable def coords [IsTotallyReal F] (ι : Type) :
    (ι → AdeleRing (𝓞 F) F) ≃ₜ+
      (ι → InfinitePlace F → ℝ) × (ι → FiniteAdeleRing (𝓞 F) F) where
  toFun x := (fun i w => InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w) ((x i).1 w), fun i => (x i).2)
  invFun p := fun i => (show AdeleRing (𝓞 F) F from
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w)).symm (p.1 i w), p.2 i))
  left_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    funext w
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i w
    exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i w
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) _ _
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun w => ?_)
      (continuous_pi fun i => ?_)
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))
    · exact continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk (continuous_pi fun w => ?_) ?_
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).symm.continuous.comp
        ((continuous_apply w).comp ((continuous_apply i).comp continuous_fst))
    · exact (continuous_apply i).comp continuous_snd

theorem coord_theta [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (t : ℝ)
    (w : InfinitePlace F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) (θ t w) = t := by
  have h : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) :
      w.Completion →+* ℝ).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ))
      = RingHom.id ℝ := Subsingleton.elim _ _
  exact DFunLike.congr_fun h t

theorem card_places [IsTotallyReal F] :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

end Adelic

theorem map_scalar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
    ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type)
      [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t →
      μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) =
        ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  intro F _ _ hF θ _ _ _ ι _ μ _ t ht
  haveI := hF
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have key := map_eq_smul_of_scale (coords F ι)
    (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) t ht.ne' ?_ μ
  · have hd : Module.finrank ℝ (ι → InfinitePlace F → ℝ) =
        Module.finrank ℚ F * Fintype.card ι := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, card_places F, mul_comm]
    rw [key, hd, abs_of_pos (inv_pos.2 (pow_pos ht _))]
  · intro x
    refine Prod.ext ?_ ?_
    · funext i w
      show InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
        (θ t w * (x i).1 w) = t * _
      rw [map_mul, coord_theta]
      rfl
    · funext i
      exact one_mul _

end GlobalTheory.CompanionTheory.AdelicFlow
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerZero

theorem exists_tail_pos {ι : Type} {a : ι → ℝ} (h : Summable (fun v => |a v - 1|)) (S₀ : Finset ι) :
    ∃ S : Finset ι, S₀ ⊆ S ∧ 0 < ∏' v : {v // v ∉ S}, a v.1 := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hfin : {v | ¬ |a v - 1| < 1}.Finite := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hs : Summable (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => |a v.1 - 1|) :=
    h.comp_injective Subtype.val_injective
  refine (AbsTprod.abs_tprod _ (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => a v.1) hs).2.2.1 ?_
  rintro ⟨v, hv⟩
  have hv' : |a v - 1| < 1 := by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  have := (abs_lt.1 hv').1
  show 0 < a v
  linarith

theorem countable_places (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
    fun a b h => HeightOneSpectrum.ext h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_measure_intOff {d M n : ℕ} {b : Module.Basis (Fin d) F E}
    {I : Measure (Fin n → Fin M → AF F ⊗[F] E)} {c : ℝ≥0}
    {minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsEulerProd b I c minf m)
    (hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      I (intOff b S) = (c : ℝ≥0∞) * (minf Set.univ * ∏ v ∈ S, m v Set.univ) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) := by
  obtain ⟨-, -, S₀, hS₀⟩ := h
  refine ⟨S₀, fun S hS => ?_⟩
  have key := hS₀ S hS (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
  have hp : pureL b S (fun _ => 1) (fun _ _ => 1) = (intOff (n := n) (M := M) b S).indicator 1 := by
    funext X
    simp [pureL, Set.indicator]
  rw [hp, lintegral_indicator_one (hmeas S)] at key
  simpa using key

end GlobalTheory.CompanionTheory.SW.EulerZero


open GlobalTheory.CompanionTheory.SW.EulerZero in
theorem GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m
  obtain ⟨-, -, -, -, hopen, hcof, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨-, -, -, -, -, -, -, hborel, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hborel n M
  have hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S) := fun S => (hopen S).measurableSet
  refine ⟨fun h hI => ?_, fun h hz => ?_, fun hfin hsum hz => ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hc, hminf, hm⟩ := hcon
    obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    obtain ⟨S, hS, hpos⟩ := exists_tail_pos h.2.1 S₀
    have key := hS₀ S hS
    rw [hI] at key
    have h1 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have h2 : minf Set.univ ≠ 0 := by simpa using hminf
    have h3 : ∏ v ∈ S, m v Set.univ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hm v
    have h4 : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) ≠ 0 := by
      simpa using hpos
    exact (mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) h4) (by simpa using key.symm)
  · obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    classical
    obtain ⟨S₁, hS₁, hzero⟩ : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧
        ∀ S, S₁ ⊆ S → minf Set.univ * ∏ v ∈ S, m v Set.univ = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨S₀, subset_rfl, fun S _ => by simp [hz]⟩
      · refine ⟨insert v S₀, Finset.subset_insert _ _, fun S hS => ?_⟩
        rw [Finset.prod_eq_zero (hS (Finset.mem_insert_self v S₀)) (by simp [hv]), mul_zero]
    haveI := countable_places F
    have hcover : (Set.univ : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆
        ⋃ T : Finset (HeightOneSpectrum (𝓞 F)), intOff b (S₁ ∪ T) := by
      intro X _
      have hT := Filter.eventually_cofinite.1 (hcof (projFin X))
      refine Set.mem_iUnion.2 ⟨hT.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv (Finset.mem_union_right _ (hT.mem_toFinset.2 hc))
    have hnull : I Set.univ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun T => ?_)
      rw [hS₀ _ (hS₁.trans Finset.subset_union_left), hzero _ Finset.subset_union_left]
      simp
    exact Measure.measure_univ_eq_zero.1 hnull
  · refine ⟨hfin, hsum, ?_⟩
    classical
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), minf = 0 ∨ ∃ v ∈ S₀, m v = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨∅, Or.inl hz⟩
      · exact ⟨{v}, Or.inr ⟨v, by simp, hv⟩⟩
    refine ⟨S₀, fun S hS φinf φ _ _ => ?_⟩
    rcases hS₀ with hz | ⟨v, hv, hmv⟩
    · simp [hz]
    · rw [Finset.prod_eq_zero (hS hv) (by simp [hmv])]
      simp
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinates
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

theorem finDensity_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b B hB lf hlf a U
  obtain ⟨-, h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨-, hme, hmap⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.coordMap_one F E σ hCM (Af F) d b lf hlf M
  rw [← hmap, hme.map_apply]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hl := _root_.GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff F E d M b a X
  have ht : gramR (Af F) σ J X 0 0 = hR (Af F) σ J (X 0) (X 0) := rfl
  rw [ht, hB, ← hl]

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurable
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB

theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  have hact := ((_root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ R).2.2.2.2.2 1).1
  have hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k :=
    (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R).2.2.2.2.2.2.1 d b
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  have h1 : Continuous fun h : HA R σ J => actW R σ J h X :=
    hact.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1 :=
    (continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)
  have h3 : Continuous fun h : HA R σ J =>
      (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2 :=
    (continuous_apply p.2).comp (hco.continuous.comp h2)
  refine h3.congr fun h => ?_
  simp [gmat, actW, actTup, X, Matrix.mulVec_single]

theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (AF F)
  have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q =>
    (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  refine ⟨fun w p q => ?_, fun p q => ?_⟩
  · have hf : Continuous fun t : AF F => e (fstA F t) w :=
      (continuous_apply w).comp (he.continuous.comp continuous_fst)
    exact (hf.comp (hinv p q)).measurable
  · have hf : Continuous fun t : AF F => sndA F t := continuous_snd
    exact (hf.comp (hinv p q)).measurable

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

theorem modulus_matrix : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  intro F _ _ ι _ _ A hA
  obtain ⟨cinf, c, hU, hinf, hv⟩ := _root_.GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar F A.det hA
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact _root_.GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul F (Ainf F) ι A hA Measure.addHaar inferInstance cinf
      (hinf Measure.addHaar inferInstance) μ hμ
  · intro v μ hμ
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fv F v) := (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v).2.2.1
    exact _root_.GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul F (Fv F v) ι A hA Measure.addHaar inferInstance (c v)
      (hv v Measure.addHaar inferInstance) μ hμ

end GlobalTheory.CompanionTheory.SW.ProdFormula
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_compact_open_unit_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV (M := M) (n := n) b v) ∧ IsOpen (latV (M := M) (n := n) b v) ∧ (0 : Fin n → Fin M → Fv F v ⊗[F] E) ∈ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → coordW (Fv F v) b lam n M (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | exact GlobalTheory.CompanionTheory.SW.latV_compact_open_mass | (intros; apply GlobalTheory.CompanionTheory.SW.latV_compact_open_mass <;> assumption)
end

