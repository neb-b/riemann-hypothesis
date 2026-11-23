module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalConditionsOfEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.TransportLoc

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_iff (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d x : G) :
    x ∈ twCent θ d ↔ e x ∈ twCent θ' (e d) := by
  show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)
  rw [← h, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem map_twConj (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d y : G) :
    e (y⁻¹ * d * θ y) = (e y)⁻¹ * e d * θ' (e y) := by
  simp only [map_mul, map_inv, h]

theorem twConj_mul (θ : G →* G) (d t w : G) (ht : t ∈ twCent θ d) :
    (t * w)⁻¹ * d * θ (t * w) = w⁻¹ * d * θ w := by
  have ht' : t * d = d * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc w⁻¹ * t⁻¹ * d * (θ t * θ w) = w⁻¹ * t⁻¹ * (d * θ t) * θ w := by group
    _ = w⁻¹ * d * θ w := by rw [← ht']; group

theorem finite_support (e : G ≃* G') (θ : G →* G) (θ' : G' →* G')
    (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ)
    (hθ : ∀ x, e (θ x) = θ' (e x)) (hK : ∀ x, x ∈ K ↔ e x ∈ K') (hf : ∀ x, f x = f' (e x))
    (hfin : {q : DoubleCoset.Quotient (twCent θ' (e d) : Set G') (K' : Set G') |
      ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * e d * θ' (Quotient.out q * k)) ≠ 0}.Finite) :
    {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
      ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) =>
      DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin
  · rintro q ⟨k, hk, hne⟩
    obtain ⟨t, ht₀, k₁, hk₁, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))
    refine ⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩
    have hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) *
        (k₁⁻¹ * e k) = t * e (Quotient.out q * k) := by
      rw [hout, map_mul]; group
    simp only []
    rw [hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]
    exact hne
  · intro q₁ _ q₂ _ heq
    obtain ⟨t', ht', k', hk', hy⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 heq
    have h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k' := by
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact hy
    have ht : e.symm t' ∈ twCent θ d := by
      rw [mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]; exact ht'
    have hk : e.symm k' ∈ K := by
      rw [hK, e.apply_symm_apply]; exact hk'
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩

theorem index_ne_zero (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K')
    (u : K → ℂ) (u' : K' → ℂ) (hu : ∀ k : K, u k = u' ⟨e k, (hK k).1 k.2⟩)
    (h : (rStab u').index ≠ 0) : (rStab u).index ≠ 0 := by
  let φ : K →* K' :=
    { toFun := fun k => ⟨e k, (hK k).1 k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := fun k' =>
    ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩
  have hu' : ∀ k : K, u k = u' (φ k) := hu
  have hstab : rStab u = (rStab u').comap φ := by
    ext k
    constructor
    · intro hk x'
      obtain ⟨x, rfl⟩ := hφ x'
      show u' (φ x * φ k) = u' (φ x)
      rw [← map_mul, ← hu', ← hu']
      exact hk x
    · intro hk x
      show u (x * k) = u x
      rw [hu', hu', map_mul]
      exact hk (φ x)
  rw [hstab, Subgroup.index_comap_of_surjective _ hφ]
  exact h

theorem mem_conj_iff (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K') (y x : G) :
    x ∈ K.map (MulAut.conj y).toMonoidHom ↔ e x ∈ K'.map (MulAut.conj (e y)).toMonoidHom := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k', hk', h⟩
    refine ⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩
    apply e.injective
    rw [← h]
    simp [MulAut.conj_apply]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_iff (e : G ≃ₜ* G') (t : G) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
  have h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t
    exact (congrArg (fun S : Subgroup G' => (S : Set G')) this).symm
  rw [h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]

theorem map_cptPart (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G') (hT : ∀ x, x ∈ T ↔ e x ∈ T') :
    (cptPart T).map e.toMulEquiv.toMonoidHom = cptPart T' := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext t'
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩
  · rintro ⟨ht', hc⟩
    refine ⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩
    · rw [hT]; simpa using ht'
    · rw [isCompact_closure_zpowers_iff e]; simpa using hc

theorem locConds_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x) := hθ
  have hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K' := hK
  have hfm : ∀ x, f x = f' (e.toMulEquiv x) := hf
  have hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d) :=
    mem_twCent_iff e.toMulEquiv θ θ' hθm d
  refine ⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩
  · intro x hx y hy
    apply e.toMulEquiv.injective
    rw [map_mul, map_mul]
    exact h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)
  · intro y
    refine index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))
    intro k
    have := map_twConj e.toMulEquiv θ θ' hθm d (y * k)
    rw [hfm, this, map_mul]
    rfl
  · intro y
    obtain ⟨ha, hb⟩ := h₄ (e y)
    have hB := map_cptPart e (twCent θ d) (twCent θ' (e d)) hT
    have hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom =
        (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)
    constructor
    · rw [hA]
      intro x hx
      have hx' := ha hx
      rw [← hB] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← e.toMulEquiv.injective hzx]
    · rw [hA, Subgroup.relIndex_comap, hB]
      exact hb

end GlobalTheory.CompanionTheory.TransportLoc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormula
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem sig_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem gram_mem {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
    [Algebra F R] (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a c
  have hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y) := fun y => by simp [sigR, inclR]
  change sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := hmv
  have hinv : ∀ e, σ (σ e) = e := GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ
  have hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _) := a10 n M J

  let q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩
  have hqc : Continuous q := hgc.subtype_mk _
  have hTm : MeasurableSet Tt := hTo.measurableSet

  have hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y := fun y => by
    refine measure_mono_null ?_ (h1 y)
    intro x hx hx'
    exact hx (Subtype.ext hx'.1)

  let φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ := Tt.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hTo.frontier_eq, hTc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    refine subset_trans (closure_minimal ?_ hTc.isClosed) hTf
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h3 φ hφc hφs hφt
  have hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal := fun y => by
    simp [φ, integral_indicator hTm, Measure.real]
  have hfin : ∀ y, mv y Tt ≠ ⊤ := fun y => by
    have h := hI y (Set.mem_univ y)
    rw [integrable_indicator_iff hTm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : Continuous fun y => (mv y Tt).toReal := by
    have h := continuousOn_univ.1 hC
    simpa only [hint] using h
  refine ⟨fun Y hY => ?_, hcont, hfin, ?_⟩
  · have hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y := by
      ext X
      constructor
      · rintro ⟨y, hy, e⟩
        have : q X = y := Subtype.ext e
        show q X ∈ Y
        rwa [this]
      · intro hX
        exact ⟨q X, hX, rfl⟩
    rw [hG]
    have hqY : MeasurableSet (q ⁻¹' Y) := hqc.measurable hY
    have hT : MeasurableSet (Tt ∩ q ⁻¹' Y) := hTm.inter hqY
    have e := h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)
    rw [lintegral_indicator_one hT, Measure.restrict_apply hT,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)] at e
    rw [e, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    rw [lintegral_indicator_one hT]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      refine measure_congr ?_
      filter_upwards [hae y] with x hx
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      show q x ∈ Y
      rwa [hx]
    · rw [Set.indicator_of_notMem hy]
      refine measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)
      intro x hx hxy
      apply hy
      rw [← hxy]
      exact hx.2
  · obtain ⟨C, hC'⟩ := (hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Real.toNNReal C, fun y => ?_⟩
    by_cases hy : y ∈ q '' Tt
    · have h := hC' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h
      show mv y Tt ≤ ENNReal.ofReal C
      exact (ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h
    · have h0 : mv y Tt = 0 := by
        refine measure_mono_null ?_ (h1 y)
        intro x hx hx'
        exact hy ⟨x, hx, Subtype.ext hx'.1⟩
      rw [h0]
      exact bot_le
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimate
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem pow_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) (k : ℕ) {x : R ⊗[F] E} (hx : x ∈ L) : t ^ k * x ∈ L := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact L.smul_mem (⟨t, ht⟩ : O) ih

theorem sum_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E)) {n : ℕ}
    (x a : Fin n → R ⊗[F] E) (hx : ∀ i, x i ∈ L) (ha : ∀ i, a i ∈ O) : ∑ i, x i * a i ∈ L := by
  refine L.sum_mem fun i _ => ?_
  rw [mul_comm]
  exact L.smul_mem (⟨a i, ha i⟩ : O) (hx i)

theorem nearNF_anti (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) {M n : ℕ} {j j' : ℕ} (h : j ≤ j') :
    nearNF (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j' ⊆
      nearNF R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j := by
  rintro X ⟨hX, l, a, ha, hl, hk⟩
  refine ⟨hX, l, a, ha, hl, fun k => ?_⟩
  obtain ⟨y, hy, hyk⟩ := hk k
  refine ⟨t ^ (j' - j) * y, pow_mul_mem_submodule R O L ht _ hy, ?_⟩
  rw [← hyk]
  change t ^ j * (t ^ (j' - j) * y) = t ^ j' * y
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem goodT_mono (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (hS : ∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O) (M n : ℕ) :
    Monotone (fun j => goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j) := by
  intro j j' h X hX
  refine ⟨hX.1, fun hmem => hX.2 ?_⟩
  simp only [Set.mem_iUnion] at hmem ⊢
  obtain ⟨p, hp, hXp⟩ := hmem
  exact ⟨p, hp, nearNF_anti R O L (hS p hp) h hXp⟩

theorem goodT_free (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E)))
    (hfix : ∀ p ∈ S, ∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) {M n : ℕ}
    (hdet : ∀ X : Fin n → Fin M → R ⊗[F] E, ¬ LinearIndependent (R ⊗[F] E) X →
      ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
        ∀ k, p.2 * ∑ i, X i k * a i = 0) (j : ℕ) :
    goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j ⊆
      {X | LinearIndependent (R ⊗[F] E) X} := by
  intro X hX
  by_contra hli
  obtain ⟨p, hp, l, a, ha, hl, hk⟩ := hdet X hli
  refine hX.2 ?_
  simp only [Set.mem_iUnion]
  refine ⟨p, hp, hX.1, l, a, ha, hl, fun k => ?_⟩
  have hxL : ∑ i, X i k * a i ∈ L :=
    sum_mul_mem_submodule R O L (fun i => X i k) a (fun i => hX.1 i k) ha
  refine ⟨_, hxL, ?_⟩
  have hfx := hfix p hp _ (hk k)
  have hpow : ∀ m : ℕ, (p.1 : R ⊗[F] E) ^ m * ∑ i, X i k * a i = ∑ i, X i k * a i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hfx, ih]
  exact hpow j

end Gen

theorem goodT_mono_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), Monotone (fun j => (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∧ ∀ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ d b v lv _ O S hO L _ _ n M
  obtain ⟨-, -, -, hS, hdet⟩ := hO
  exact ⟨goodT_mono (Fv F v) O L S (fun p hp => (hS p hp).1) M n,
    fun j => goodT_free (Fv F v) O L S (fun p hp => (hS p hp).2.2.1) (hdet n M) j⟩

end GlobalTheory.CompanionTheory.AvgFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

def chartHom (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : Γ(PSpace ℤ N, chart ℤ N c) →+* ℂ :=
  (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c)).comp
    (chartAlgEquiv ℤ N c).symm.toRingEquiv.toRingHom

def ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : CxPts (PSpace.str ℤ N) σ₀ :=
  CxPts.ofHom (isAffineOpen_chart ℤ N c) (chartHom N c w)
    (fun a => RingHom.congr_fun (RingHom.ext_int ((chartHom N c w).comp (DVR.FlatBC.algX _ _)) σ₀) a)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def multiprojectivePoint (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) : CxPts (mpStr ℤ m n) σ₀ :=
  ⟨GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (spMap σ₀)
      (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).1) (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).2),
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ _ _ _ _⟩

theorem map_prB_ptMP (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) :
    (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ (multiprojectivePoint c z)) =
      ptP (n k) (c k) (fun i => z ⟨k, i⟩) :=
  Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ k)

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem mem_ptIdeal_iff_aeval_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (f : Geo.MRing (Bk n)) (a : Fin (m + 1) → ℕ), Geo.IsMultiHomog f a → (f ∈ ptIdeal x ↔ aeval (ptCoord x) f = 0) := by
  intro m n x f a hf
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff (ptCoord x) hf

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdInj

theorem prod₂_map_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (f : σ.IntertwiningMap σ'), Function.Injective f → ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ), Function.Injective F := by
  intro k _ _ _ _ r t U U' W _ _ _ _ _ _ σ σ' ρ f hf
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.ProdInj
end

