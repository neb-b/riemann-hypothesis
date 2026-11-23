module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0009
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis
section
open Matrix Topology

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_pi_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Fin n → Fin n → L)} {x : Fin n → Fin n → L} (hA : A ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin n → Fin n → L, (∀ i j, ‖y i j - x i j‖ ≤ ε) → y ∈ A := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
  have hd : dist y x ≤ ε / 2 := by
    rw [dist_pi_le_iff (half_pos hε).le]
    intro i
    rw [dist_pi_le_iff (half_pos hε).le]
    intro j
    rw [dist_eq_norm]
    exact hy i j
  rw [Metric.mem_ball]
  linarith

theorem exists_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Matrix (Fin n) (Fin n) L)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ i j, ‖(M - 1) i j‖ ≤ ε) → M ∈ A := by
  obtain ⟨ε, hε, h⟩ := exists_pi_entry_box (x := (1 : Matrix (Fin n) (Fin n) L)) hA
  refine ⟨ε, hε, fun M hM => h M fun i j => ?_⟩
  have := hM i j
  rwa [Matrix.sub_apply] at this

theorem congK_cofinal (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1U : (1 : GL (Fin n) L) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε →
      (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  have hU1 : U ∈ 𝓝 (1 : GL (Fin n) L) := hU.mem_nhds h1U
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap, map_one] at hU1
  obtain ⟨V, hV, hVU⟩ := hU1
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (x := (1 : Matrix (Fin n) (Fin n) L)) (y := MulOpposite.op 1)).1 hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_entry_box hA
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_entry_box hB'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r h0 h1 hr k hk => hVU (hAB ⟨?_, ?_⟩)⟩
  · exact h₁ _ fun i j => ((hk i j).1.trans hr).trans (min_le_left _ _)
  · exact h₂ _ fun i j => ((hk i j).2.trans hr).trans (min_le_right _ _)

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousDiag
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.NullSets

theorem null_of_lines {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (φ : ℝ → G) (hφ : Measurable φ) {S : Set G}
    (hS : MeasurableSet S) (h : ∀ x, (volume : Measure ℝ) {t | φ t + x ∈ S} = 0) : μ S = 0 := by
  have hT : MeasurableSet {p : G × ℝ | φ p.2 + p.1 ∈ S} :=
    ((hφ.comp measurable_snd).add measurable_fst) hS
  have h1 : (μ.prod (volume : Measure ℝ)) {p : G × ℝ | φ p.2 + p.1 ∈ S} = 0 := by
    rw [Measure.prod_apply hT]
    have : ∀ x, (volume : Measure ℝ) (Prod.mk x ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = 0 := h
    exact (lintegral_congr (g := fun _ => 0) this).trans (by simp)
  rw [Measure.prod_apply_symm hT] at h1
  have h2 : ∀ t : ℝ, μ ((fun x => (x, t)) ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = μ S :=
    fun t => measure_preimage_add μ (φ t) S
  simp only [h2, lintegral_const, measure_univ, Real.volume_univ] at h1
  by_contra hne
  simp [hne] at h1

section Line

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem q_line (hσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y0 : Fin M → E) (a : F)
    (hy0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0 = algebraMap F E a) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R]
    (x : Fin M → R ⊗[F] E) :
    ∃ c : R, ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (x + t • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i)) =
      algebraMap F R a * t ^ 2 + c * t + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set y : Fin M → R ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i) with hy
  have hs : ∀ e : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (σ e) := fun e => rfl
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, y, hs, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply,
        RingHom.coe_coe]
    rw [this, hy0, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have hrk : Module.finrank R (R ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hσ.2.2.1]
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y = algebraMap F R a := by
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, hyy, Algebra.trace_algebraMap, hrk, ← map_nsmul, ← map_mul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hst : ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl
  refine ⟨algebraMap F R (1 / 2) *
    Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x), fun t => ?_⟩
  have e : t • y = algebraMap R (R ⊗[F] E) t • y := by
    rw [algebraMap_smul]
  rw [← hq]
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR
  generalize algebraMap F R (1 / 2) = u
  rw [e, GlobalTheory.HermLineZeros.hform_expand, hst, mul_assoc (algebraMap R (R ⊗[F] E) t)]
  simp only [← Algebra.smul_def, map_add (f := _), map_smul, smul_eq_mul]
  ring

end Line

section Coord

open GlobalTheory.CompanionTheory.SW.RealCoord

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def diag (t : ℝ) : Ainf F := (coordHomeo F).symm fun _ => t

theorem continuous_diag : Continuous (diag F) :=
  (coordHomeo F).symm.continuous.comp (continuous_pi fun _ => continuous_id)

theorem coord_diag (t : ℝ) (w : InfinitePlace F) : coord F (diag F t) w = t := by
  have h : coordHomeo F (diag F t) = fun _ => t := (coordHomeo F).apply_symm_apply _
  rw [coordHomeo_coe] at h
  exact congrFun h w

theorem continuous_coord (w : InfinitePlace F) : Continuous fun c : Ainf F => coord F c w := by
  have h : Continuous (coord F) := (isHomeomorph_coord F).continuous
  exact (continuous_apply w).comp h

theorem null_nonunit {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (f : G → Ainf F)
    (hf : ∀ w, Measurable fun X => coord F (f X) w) (φ : ℝ → G) (hφ : Measurable φ)
    (h : ∀ x w, {t : ℝ | coord F (f (φ t + x)) w = 0}.Finite) : μ {X | ¬ IsUnit (f X)} = 0 := by
  have sub : {X | ¬ IsUnit (f X)} ⊆ ⋃ w, {X | coord F (f X) w = 0} := by
    intro X hX
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hc
    apply hX
    have h1 : IsUnit (coord F (f X)) := Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (hc w)
    exact (isUnit_map_iff (coord F) _).1 h1
  refine measure_mono_null sub (measure_iUnion_null fun w => ?_)
  exact null_of_lines μ φ hφ (hf w (measurableSet_singleton 0)) fun x => (h x w).measure_zero _

end Coord

theorem null_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0)) X)} = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ ν hμ hν
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨hR1, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI := hR1
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨p1, p2, p3, p4, -, p6, -, p8, -, p10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := p1
  haveI := p2
  haveI := p3
  haveI := p4
  haveI hB2 := p8 1 M
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Ainf F)
  haveI : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul (Ainf F) _
  have hc := fun w => GlobalTheory.CompanionTheory.SW.NullSets.continuous_coord F w
  refine ⟨?_, ?_⟩
  · refine null_nonunit F ν id (fun w => (hc w).measurable) (diag F) (continuous_diag F).measurable ?_
    intro x w
    refine (Set.finite_singleton (-RealCoord.coord F x w)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, id, map_add (f := _), Pi.add_apply, coord_diag] at ht
    simp only [Set.mem_singleton_iff]
    linarith
  · obtain ⟨y0, a, ha, hy0⟩ := GlobalTheory.HermLineZeros.exists_anisotropic hσ hM hJ
    set y : Fin M → Ainf F ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf F) (y0 i) with hy
    have hcont : Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0) :=
      continuous_const.mul (p6.comp ((p10 1 M J).matrix_elem 0 0))
    refine null_nonunit F μ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0))
      (fun w => ((hc w).comp hcont).measurable) (fun t _ => diag F t • y) ?_ ?_
    · refine Continuous.measurable (continuous_pi fun _ => continuous_pi fun i => ?_)
      exact (continuous_diag F).smul continuous_const
    · intro x w
      obtain ⟨c, hc'⟩ := q_line hσ J y0 a hy0 (Ainf F) (x 0)
      set C := RealCoord.coord F c w
      set Q := RealCoord.coord F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (x 0)) w
      have hne : (Polynomial.C (RealCoord.rho F w a) * Polynomial.X ^ 2 + Polynomial.C C * Polynomial.X
          + Polynomial.C Q : Polynomial ℝ) ≠ 0 := by
        intro h0
        have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 2) h0
        simp [Polynomial.coeff_X, Polynomial.coeff_C] at this
        exact ha this
      refine (Polynomial.finite_setOf_isRoot hne).subset fun t ht => ?_
      simp only [Set.mem_setOf_eq] at ht
      have e : (diag F t • y + x 0) = x 0 + diag F t • y := add_comm _ _
      have e2 : (fun _ : Fin 1 => diag F t • y) + x = fun i => (fun _ : Fin 1 => diag F t • y) i + x i := rfl
      rw [e2] at ht
      simp only [e] at ht
      rw [hc' (diag F t)] at ht
      simp only [map_add (f := _), map_mul, map_pow, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        coord_diag, RealCoord.coord_algebraMap] at ht
      simpa [Polynomial.IsRoot] using ht

end GlobalTheory.CompanionTheory.SW.NullSets
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Lower

theorem conj_entry {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by
  have h : (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  rw [Units.val_mul, Units.val_mul, h, GlobalTheory.CompanionTheory.CartGL.dPow_val, mul_diagonal, diagonal_mul]

theorem norm_conj_le {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < ‖(p : L)‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c = b + m := ⟨(c - b).toNat, by omega⟩
  have e : ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ = ‖x‖ * ‖(p : L)‖ ^ m := by
    rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow,
      norm_zpow, hm, zpow_add₀ hp0.ne', _root_.zpow_neg, zpow_natCast]
    have : ‖(p : L)‖ ^ b ≠ 0 := (zpow_pos hp0 b).ne'
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hp0.le hp.le)

theorem conj_lower_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r w hl hr i j
  rw [Matrix.sub_apply, conj_entry]
  rcases lt_trichotomy i j with h | h | h
  · have h0 := hr i j
    rw [Matrix.sub_apply, hl i j h, Matrix.one_apply_ne h.ne] at h0
    rw [hl i j h, Matrix.one_apply_ne h.ne]
    simpa using h0
  · subst h
    have hne : ((p ^ (-a i) : Lˣ) : L) * ((p ^ a i : Lˣ) : L) = 1 := by
      rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]
    have e : ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i i * ((p ^ a i : Lˣ) : L) =
        (w : Matrix (Fin n) (Fin n) L) i i := by
      rw [mul_right_comm, hne, one_mul]
    rw [e]
    simpa [Matrix.sub_apply] using hr i i
  · have h0 := hr i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero] at h0
    rw [Matrix.one_apply_ne h.ne', sub_zero]
    exact (norm_conj_le p hp (ha h.le) _).trans h0

end GlobalTheory.CompanionTheory.CartGL.Lower
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  have hyn : 0 < ‖p‖⁻¹ ^ n := zpow_pos (inv_pos.mpr hp0) n
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithfulStatement
section
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operators_span_and_faithful : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | exact GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | (intros; apply GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}





theorem factor (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1

theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
section
namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    refine ⟨0, ?_, by simp⟩
    funext a
    change χ a = χ a + (↑(0 : ℕ) : ℂ)
    simp
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · change pathEnd (χ + Pi.single s 1) ss = _
      rw [h]
      funext a
      by_cases e : a = s
      · subst a
        simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
        ac_rfl
      · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha
      · subst a
        simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_succ (Nat.zero_le (m' s))
      · exact (hm a ha).trans (Nat.le_add_right _ _)

theorem pathEndNat (n : ℕ) (χ : _root_.Fin n → ℂ) (ss : List (_root_.Fin n)) :
    ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a :=
  pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
end

