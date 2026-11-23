module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SetIntegralPeriodLatticeEqVolumeMulCube
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem setIntegral_periodic_eq_measure_mul_cube {E I : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
    (ν : Measure E) [ν.IsAddHaarMeasure] (T : (I → ℝ) ≃L[ℝ] E) (Λ : Submodule ℤ E)
    (hΛ : ∀ p, T p ∈ Λ ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = p i)
    (Fd : Set E) (hFd : IsAddFundamentalDomain Λ Fd ν)
    (F : E → ℝ) (hF : ∀ (l : Λ) z, F (z + l) = F z) :
    ∫ z in Fd, F z ∂ν = (ν Fd).toReal *
      ∫ p in Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1), F (T p) := by
  classical
  set b : Module.Basis I ℝ E := (Pi.basisFun ℝ I).map T.toLinearEquiv with hb
  have hrepr : ∀ p i, b.repr (T p) i = p i := by
    intro p i
    simp [hb]
  have hspan : Λ = Submodule.span ℤ (Set.range b) := by
    ext z
    obtain ⟨p, rfl⟩ := T.surjective z
    rw [hΛ, Module.Basis.mem_span_iff_repr_mem]
    simp [hrepr]
  subst hspan
  have hcell := ZSpan.isAddFundamentalDomain b ν
  have hpre : T ⁻¹' ZSpan.fundamentalDomain b
      = Set.pi Set.univ (fun _ : I => Set.Ico (0 : ℝ) 1) := by
    ext p
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, hrepr, Set.mem_pi, Set.mem_univ,
      true_imp_iff]
  have hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E ν :=
    ⟨fun c s _ => measure_preimage_add ν (c : E) s⟩
  have h1 : ∫ z in Fd, F z ∂ν = ∫ z in ZSpan.fundamentalDomain b, F z ∂ν :=
    hFd.setIntegral_eq hcell (fun l z => by
      have := hF l z
      rw [add_comm] at this
      exact this)
  have h2 : ν Fd = ν (ZSpan.fundamentalDomain b) := hFd.measure_eq hcell
  let e : (I → ℝ) ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have he : (e : (I → ℝ) → E) = T := rfl
  haveI : (Measure.map T (volume : Measure (I → ℝ))).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • Measure.map e (volume : Measure (I → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν (Measure.map T volume)⟩
  have h3 : ν (ZSpan.fundamentalDomain b) = c := by
    rw [hc, Measure.smul_apply, e.map_apply, he, hpre, Real.volume_pi_Ico]
    simp
  rw [h1, h2, h3, hc, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_map_equiv,
    he, hpre]
  simp [NNReal.smul_def]

theorem setIntegral_periodLattice_eq_volume_mul_cube :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    ∀ F : (Fin g → ℂ) → ℝ, (∀ (l : Λ) z, F (z + l) = F z) →
    ∫ z in Fd, F z = (volume Fd).toReal * ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
      F (φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))) := by
  intro g Λ φ τ hτ hΛ Fd hFd F hF
  let L : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun p => φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))
      map_add' := fun p q => by
        rw [← map_add (f := _)]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        have : ∀ v : Fin g → ℂ, c • v = (c : ℂ) • v := fun v => by ext i; simp
        rw [RingHom.id_apply, this, ← map_smul]
        congr 1
        ext i
        simp [Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum, mul_left_comm] }
  have hL : ∀ p, L p = φ ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ))) :=
    fun _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL, LinearEquiv.map_eq_zero_iff] at hp
    have him : (τ.map Complex.im).mulVec (fun i => p (.inr i)) = 0 := by
      ext i
      have := congrArg Complex.im (congrFun hp i)
      simpa [Matrix.mulVec, dotProduct] using this
    have hr : (fun i => p (.inr i)) = 0 :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hτ.isUnit) (by rw [him, Matrix.mulVec_zero])
    have hr' : ∀ i, p (.inr i) = 0 := fun i => congrFun hr i
    ext (i | i)
    · have := congrFun hp i
      simpa [Matrix.mulVec, dotProduct, hr'] using this
    · exact hr' i
  have hdim : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  let T : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hT : ∀ p, T p = L p := fun _ => rfl
  refine setIntegral_periodic_eq_measure_mul_cube volume T Λ (fun p => ?_) Fd hFd F hF
  rw [hT, hL, hΛ]
  constructor
  · rintro ⟨m, n, h⟩
    have : L p = L (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) := by
      rw [hL, hL, h]
      simp
    have hp := hinj this
    rintro (i | i)
    · exact ⟨m i, by simp [hp]⟩
    · exact ⟨n i, by simp [hp]⟩
  · intro h
    choose k hk using h
    refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
    simp [← hk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VolumeFundamentalDomainPeriodLattice
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodVol

def reImCoord (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g ⊕ Fin g → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun p := fun i => ⟨p (Sum.inl i), p (Sum.inr i)⟩
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp
  left_inv z := rfl
  right_inv p := by ext (i | i) <;> rfl

theorem volume_fundamentalDomain_reImCoord (g : ℕ) :
    volume (ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g))) = 1 := by
  have h : ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g)) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, forall_and]
    tauto
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  ((reImCoord g).symm : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ)) ∘ₗ
    Matrix.toLin' (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)) ∘ₗ
      ((reImCoord g).symm.symm : (Fin g → ℂ) →ₗ[ℝ] (Fin g ⊕ Fin g → ℝ))

theorem det_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.det (periodMap τ) = (τ.map Complex.im).det := by
  rw [periodMap, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.one_mul]

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    periodMap τ z = (fun i => ((z i).re : ℂ)) + τ.mulVec (fun i => ((z i).im : ℂ)) := by
  ext i
  apply Complex.ext
  · change (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)).mulVec
      (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) (Sum.inl i) = _
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  · change (Matrix.fromBlocks 1 (τ.map Complex.re) 0 (τ.map Complex.im)).mulVec
      (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) (Sum.inr i) = _
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

end GlobalTheory.PeriodVol

namespace GlobalTheory

open PeriodVol

theorem volume_fundamentalDomain_periodLattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
    (τ.map Complex.im).PosDef →
    (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    (volume Fd).toReal = ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
  intro g Λ φ τ hτ hΛ Fd hFd
  have hpos := hτ.det_pos
  let S : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearMap.equivOfDetNeZero (periodMap τ) (by rw [det_periodMap]; exact hpos.ne')
  have hS : ∀ z, S z = periodMap τ z := fun z => rfl
  let T : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := S.trans (φ.restrictScalars ℝ)
  let b₀ := Module.Basis.ofEquivFun (reImCoord g)
  have hspan : Λ = Submodule.span ℤ (Set.range (b₀.map T)) := by
    ext w
    obtain ⟨z, rfl⟩ := T.surjective w
    rw [Module.Basis.mem_span_iff_repr_mem]
    change φ (S z) ∈ Λ ↔ _
    rw [hΛ]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, b₀,
      Module.Basis.ofEquivFun_repr_apply]
    constructor
    · rintro ⟨m, n, h⟩
      have : z = fun i => ⟨m i, n i⟩ := S.injective (by rw [h, hS, periodMap_apply]; simp)
      subst this
      rintro (i | i)
      · exact ⟨m i, rfl⟩
      · exact ⟨n i, rfl⟩
    · intro h
      choose k hk using h
      refine ⟨fun i => k (Sum.inl i), fun i => k (Sum.inr i), ?_⟩
      have h1 : ∀ i, (z i).re = k (Sum.inl i) := fun i => (hk (Sum.inl i)).symm
      have h2 : ∀ i, (z i).im = k (Sum.inr i) := fun i => (hk (Sum.inr i)).symm
      rw [hS, periodMap_apply]
      simp [h1, h2]
  subst hspan
  have hdet : b₀.det (b₀.map T) =
      ‖LinearMap.det (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))‖ ^ 2 * (τ.map Complex.im).det := by
    have hT : (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) =
        (φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℝ ∘ₗ periodMap τ := rfl
    have : ⇑(b₀.map T) = (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) ∘ b₀ := by
      ext1 i; simp
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, _root_.mul_one, hT, LinearMap.det_comp,
      det_periodMap, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range (b₀.map T))) (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hFd.measure_eq (ZSpan.isAddFundamentalDomain (b₀.map T) volume),
    ZSpan.measure_fundamentalDomain _ volume b₀, volume_fundamentalDomain_reImCoord, _root_.mul_one, hdet,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity)]

end GlobalTheory
end
end

