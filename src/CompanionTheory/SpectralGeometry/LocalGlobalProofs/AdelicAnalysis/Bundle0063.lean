module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProduct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SwEmpty

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem thetaMeas_of_empty (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (hS : S = ∅) : thetaMeas σ J μ 𝓕 S = 0 := by
  subst hS
  have : IsEmpty ((∅ : Set (Fin n → Fin M → E))) := by simp
  unfold thetaMeas
  rw [Measure.sum_of_isEmpty, smul_zero]

theorem fibre_zero_of_one (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hLoc : IsLocR R)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (t : F) (ht : t ≠ 0) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b)
    (T1 : Matrix (Fin 1) (Fin 1) E) (hT1e : T1 = fun _ _ => algebraMap F E t)
    (hT1 : ∀ a b, σ (T1 b a) = T1 a b)
    (m1 : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (m : HermR R σ (n + 1) → Measure (Fin (n + 1) → Fin M → R ⊗[F] E))
    (hm1 : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m1)
    (hm : IsGramFib R σ J (n + 1) (coordW R b lam (n + 1) M) (coordHerm R σ b lam (n + 1)) m)
    (h0 : m1 (hermOf R σ T1 hT1) = 0) :
    m (hermOf R σ (blockOne (algebraMap F E t) T) hT') = 0 := by
  have hLoc' := hLoc
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := hLoc'
  have hH := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have hempty : (gramR R σ J ⁻¹' {(hermOf R σ (blockOne (algebraMap F E t) T) hT').1} ∩
      {X | IsUnit (gramR R σ J X).det}) = ∅ := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hY _
    have h00 : hR R σ J (Y 0) (Y 0) = inclR R (algebraMap F E t) := by
      have := congrFun (congrFun hY 0) 0
      simpa [gramR, hermOf, blockOne] using this
    let x : Fin 1 → Fin M → R ⊗[F] E := fun _ => Y 0
    have hx : gramR R σ J x = (hermOf R σ T1 hT1).1 := by
      funext a c
      subst hT1e
      exact h00
    have hu : IsUnit (gramR R σ J x).det := by
      rw [hx]
      subst hT1e
      simp only [hermOf, Matrix.det_fin_one, Matrix.map_apply]
      exact (IsUnit.mk0 _ ((map_ne_zero _).2 ht)).map (inclR R)
    have := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hCM M J hJ R hLoc 1 _ _ m1 (hH.2.1 1 M) (hH.2.2 1) hm1
      (hermOf R σ T1 hT1)).2 Set.univ isOpen_univ ⟨x, trivial, hx, hu⟩
    exact this (by rw [h0]; rfl)
  have h1 := hm.1 (hermOf R σ (blockOne (algebraMap F E t) T) hT')
  rw [hempty, Set.compl_empty] at h1
  exact Measure.measure_univ_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SW.SwEmpty

namespace GlobalTheory.CompanionTheory.SW

theorem swMeas_of_not_represented : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, n + 3 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (∀ x : Fin M → E, hE σ J x x ≠ algebraMap F E t) → SWMeas σ J (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hdet hT' hne
  intro d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLinf : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
      [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure →
      (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧
        ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure := by
    intro R _ _ _ _ _ hLoc lam' hl
    obtain ⟨_, _, _, _, -⟩ := hLoc
    exact (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun _ _ => σ.commutes t
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet1 : T1.det ≠ 0 := by
    rw [Matrix.det_fin_one]; exact htE
  have hsw := _root_.GlobalTheory.CompanionTheory.SW.OneVector.siegel_one_vector F E σ hCM M J hJ (by omega) T1 hT1 hdet1
  obtain ⟨minf1, hminf1⟩ := _root_.GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib F E σ hCM M J hJ (Ainf F) hLinf 1 _ _
    ((haarOf _ hLinf laminf hinf.1).1 1 M) ((haarOf _ hLinf laminf hinf.1).2 1)
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) m' :=
    fun v => _root_.GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib F E σ hCM M J hJ (Fv F v) (hLv v) 1 _ _
      ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 M) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)
  choose m1 hm1 using hex
  have hEul := hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1
  have hS1 : {X : Fin 1 → Fin M → E | gramE σ J X = T1} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    exact hne (X 0) (congrFun (congrFun hX 0) 0)
  have hS : {X : Fin (n + 1) → Fin M → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hne (X 0)
    simpa [gramE, blockOne] using congrFun (congrFun hX 0) 0
  have hz := ((_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hCM d b 1 M _ 1 _ _).1 hEul
    (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))
  have hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨
      ∃ v, m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0 := by
    rcases hz with h | h | ⟨v, h⟩
    · exact absurd h one_ne_zero
    · exact Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1
        minf1 minf hminf1 hminf h)
    · exact Or.inr ⟨v, SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1
        (m1 v) (m v) (hm1 v) (hm v) h⟩
  have hdetB : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM n T t).1)]
    exact mul_ne_zero htE hdet
  obtain ⟨hfin, hsum⟩ := _root_.GlobalTheory.CompanionTheory.SW.mass_fibre_summable F E σ hCM M J hJ (n + 1) (Or.inr (by omega))
    (blockOne (algebraMap F E t) T) hT' hdetB d b lam (fun v => hv v) m hm
  rw [SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]
  exact (_root_.GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero F E σ hCM d b (n + 1) M 0 1 _ _).2.2 hfin hsum hvan

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Step

theorem of_cofinite {α : Type} {p : α → Prop} (h : ∀ᶠ v in Filter.cofinite, p v) {S : Finset α}
    (hS : (Filter.eventually_cofinite.1 h).toFinset ⊆ S) {v : α} (hv : v ∉ S) : p v := by
  by_contra hx
  exact hv (hS (by simpa using hx))

theorem lattice_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact (((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M).2.2.2.1 v).2).measurableSet

theorem theta_hypothesis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (blockOne (algebraMap F E t) J), Ψinf (actW (Ainf F) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φinf (actW (Ainf F) σ _ g (consTup X)) ∂minf) → (∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), Ψ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(m v)) → (∀ v, v ∉ S → ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m v {X | actW (Fv F v) σ _ g (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m v (latV b v)) (actW (Fv F v) σ _ g (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) → ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) * pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) ∂I := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n d b I minf m hE
  classical
  have hLi : IsLocR (Ainf F) := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hfin, hsum, S₀, hS₀⟩ := hE
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.CompanionTheory.SW.PureH.pure_h F E σ hCM M J hJ t ht d b
  refine ⟨S₀ ∪ S₁, fun S hS φinf φ Ψinf Ψ hφinf hφ hΨinf hΨ hG h => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  obtain ⟨ginf, g, Sh, hh⟩ := hS₁ h
  obtain ⟨hi, hii⟩ := hh S hS1
  have hmi : Measurable fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      actW (Ainf F) σ _ ginf (consTup Y) := _root_.GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup F E σ hCM (Ainf F) hLi n M _ ginf
  have hmv : ∀ v, Measurable fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      actW (Fv F v) σ _ (g v) (consTup Y) := fun v => _root_.GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup F E σ hCM (Fv F v) (hLv v) n M _ (g v)
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E)) := fun v => lattice_measurable σ hCM b (n + 1) (M + 1) v
  simp_rw [hi]
  have hmψ : ∀ v, Measurable (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) := fun v => by
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact (hφ v).comp (hmv v)
    · simp only [hv, if_false]; exact (measurable_one.indicator (hlatm v)).comp (hmv v)
  have hsplit : ∏ v ∈ S ∪ Sh, ∫⁻ X, (if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup X)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X))) ∂(m v) =
      (∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ((∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, m v (latV b v)) := by
    rw [Finset.union_comm, ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hv, if_true]; exact (hΨ v (g v)).symm
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvS : v ∉ S := (Finset.mem_sdiff.1 hv).2
      simp only [hvS, if_false]
      have e1 : ∫⁻ X, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X)) ∂(m v) =
          m v {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v} := by
        have : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ (g v) (consTup X))) =
            {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}.indicator 1 := by
          funext X; simp [Set.indicator]
        rw [this]; exact lintegral_indicator_one ((hmv v) (hlatm v))
      rw [e1, hG v hvS (g v)]
      simp [Set.indicator]
  have hmφ : Measurable (fun Y : Fin n → Fin M → Ainf F ⊗[F] E => φinf (actW (Ainf F) σ _ ginf (consTup Y))) := hφinf.comp hmi
  have htail := _root_.GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut (HeightOneSpectrum (𝓞 F)) (fun v => (m v (latV b v)).toReal) S (S ∪ Sh) hsum Finset.subset_union_left
  rw [Finset.union_sdiff_left] at htail
  have hτ : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) = (∏ v ∈ Sh \ S, m v (latV b v)) *
      ENNReal.ofReal (∏' v : {v // v ∉ S ∪ Sh}, (m v.1 (latV b v.1)).toReal) := by
    rw [htail, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    congr 1
    exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hfin v).ne
  rw [hS₀ (S ∪ Sh) (hS0.trans Finset.subset_union_left) _ _ hmφ hmψ, hii, hsplit, hτ, hΨinf ginf]
  simp only [ENNReal.coe_one, one_mul]
  ring

theorem loc_families {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, -⟩ := hR'
  have hh := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  exact _root_.GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib F E σ hCM M J hJ R hR n _ _ (hh.2.1 n M) (hh.2.2 n)

theorem blockOne_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), SWMeas σ J T hT → SWMeas σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(_root_.GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM n T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨m₁inf, hm₁inf⟩ := loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 n
  choose m₁ hm₁ using fun v => loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := _root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := _root_.GlobalTheory.CompanionTheory.SW.map_inclR_prodFormula F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (_root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := _root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := _root_.GlobalTheory.CompanionTheory.SW.OneVector.siegel_one_vector F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := _root_.GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hgood := _root_.GlobalTheory.CompanionTheory.SW.mass_fibre_summable F E σ hCM (M + 1) _ hJ' (n + 1) (Or.inr (by omega)) _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hG := _root_.GlobalTheory.CompanionTheory.SW.GoodMass.good_mass F E σ hCM M J hJ t ht n T hT hdet hT' d b
  have hSG := _root_.GlobalTheory.CompanionTheory.SW.StageGood.stage_good F E σ hCM M J hJ t ht n T hT hdet d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := _root_.GlobalTheory.CompanionTheory.SW.fibre_block_stages F E σ hCM M J hJ t ht n T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => _root_.GlobalTheory.CompanionTheory.SW.fibre_block_stages F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := _root_.GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := _root_.GlobalTheory.CompanionTheory.SW.ThetaStage.theta_stage F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (_root_.GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := _root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := _root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.SW.Step
end
end

