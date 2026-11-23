module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

theorem tsum_orbit_eq_tsum_quotient {G X : Type*} [Group G] [MulAction G X] (b : X) (o : Set X)
    (ho : MulAction.orbit G b = o) (K : Subgroup G) (hK : MulAction.stabilizer G b = K)
    (f : X → ℝ≥0∞) : ∑' p : o, f p = ∑' q : G ⧸ K, f ((Quotient.out q : G) • b) := by
  subst ho hK
  rw [← (MulAction.orbitEquivQuotientStabilizer G b).symm.tsum_eq]
  refine tsum_congr fun q => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.orbitEquivQuotientStabilizer_symm_apply]

section Action

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

@[reducible] def archMulAction (h : HermitianForm F E W) (v : Basis ι E W) :
    MulAction (archUnitary h v) (InfinitePlace E → ι → ℂ) where
  smul g y w := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w
  one_smul y := by
    funext w
    change (((1 : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w = y w
    simp
  mul_smul g k y := by
    funext w
    change (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w)
    simp [Matrix.mulVec_mulVec]

attribute [local instance] archMulAction

theorem archSmul_apply {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    (g • y) w = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w := rfl

theorem continuous_len_inv_smul {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (g⁻¹ • y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => (g⁻¹ • y) w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  unfold Majorant.len
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => ?_)
  exact Complex.continuous_re.comp
    (((continuous_star.comp (hw w))).dotProduct (continuous_const.matrix_mulVec (hw w)))

def belowIndicator {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (t : ℝ) : archUnitary h v → ℝ≥0∞ :=
  {g | M.len (g⁻¹ • y) < t}.indicator 1

theorem measurableSet_below {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    MeasurableSet {g : archUnitary h v | M.len (g⁻¹ • y) < t} :=
  (isOpen_lt (continuous_len_inv_smul M y) continuous_const).measurableSet

theorem measurable_belowIndicator {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    Measurable (belowIndicator M y t) :=
  measurable_one.indicator (measurableSet_below M y t)


omit [Fintype ι] [DecidableEq ι] in
theorem vecAt_injective (v : Basis ι E W) : Function.Injective (vecAt v) := by
  intro x y hxy
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply v.repr.injective
  ext i
  exact w.embedding.injective (congrFun (congrFun hxy w) i)

variable [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem archEmbed_smul_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (x : W) : archEmbed h v γ • vecAt v x = vecAt v (γ • x) := by
  funext w i
  rw [archSmul_apply]
  have hm : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  rw [hm]
  change _ = w.embedding (v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

theorem stabilizer_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (y : W) : MulAction.stabilizer (archLatticeGroup h v La) (vecAt v y) =
      (vecStabGroup h v La y).subgroupOf (archLatticeGroup h v La) := by
  ext ⟨γ, hγ⟩
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
  change archEmbed h v δ • vecAt v y = vecAt v y ↔ _
  constructor
  · intro he
    rw [archEmbed_smul_vecAt] at he
    exact Subgroup.mem_map.2 ⟨⟨δ, hδ⟩, MulAction.mem_stabilizer_iff.2 (vecAt_injective v he), rfl⟩
  · rintro ⟨ε, hε, he⟩
    have he' : archEmbed h v (ε : h.unitaryGroup) = archEmbed h v δ := he
    rw [← he', archEmbed_smul_vecAt]
    exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)

theorem ScalingLaw.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : UnfoldingIntegral.Statement h v) (h₂ : VectorOrbitsFinite.Statement h)
    (h₃ : UnfoldOrbit.Statement (archUnitary h v))
    (h₄ : DiscreteFundamentalDomain.Statement (archUnitary h v))
    (h₅ : ArchLatticeDiscrete.Statement h v) : ScalingLaw.Statement h v := by
  classical
  intro M μ _ D La VV hLa hVV hiso hstab hC
  set Γ := archLatticeGroup h v La with hΓ
  have : DiscreteTopology Γ := h₅ La hLa.isLattice
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hQc : ∀ K : Subgroup Γ, Countable (Γ ⧸ K) := fun K => QuotientGroup.mk_surjective.countable
  obtain ⟨FD, -, hFD⟩ := h₄ μ Γ inferInstance

  have key : ∀ y ∈ VV, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫⁻ g in FD, ∑' q : Γ ⧸ (vecStabGroup h v La y).subgroupOf Γ,
        belowIndicator M (vecAt v y) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) ∂μ =
        C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro y hy
    obtain ⟨FD₀, hFD₀, C, -, hCtop, hCt⟩ :=
      h₁ M μ D La y hLa (hVV hy) (hiso y hy).1 (hiso y hy).2
    refine ⟨C, hCtop, fun t ht => ?_⟩
    have hle : vecStabGroup h v La y ≤ Γ := by
      rintro _ ⟨ε, -, rfl⟩
      exact Subgroup.mem_map.2 ⟨ε.1, ε.2, rfl⟩
    have hinv : ∀ γ ∈ vecStabGroup h v La y, ∀ g,
        belowIndicator M (vecAt v y) t (γ * g) = belowIndicator M (vecAt v y) t g := by
      intro γ hγ g
      obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 hγ
      have hb : ((archEmbed h v).comp (latticeStab h La).subtype ε) • vecAt v y = vecAt v y := by
        change archEmbed h v (ε : h.unitaryGroup) • vecAt v y = vecAt v y
        rw [archEmbed_smul_vecAt]
        exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)
      have hb' := (inv_smul_eq_iff.2 hb.symm).symm
      simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, mul_smul,
        ← hb', Pi.one_apply]
    rw [h₃ μ Γ _ hle FD FD₀ hFD hFD₀ _ (measurable_belowIndicator M (vecAt v y) t) hinv,
      belowIndicator, lintegral_indicator_one (measurableSet_below M _ t),
      Measure.restrict_apply (measurableSet_below M _ t), Set.inter_comm]
    exact hCt t ht
  choose! Cf hCf hCeq using key

  obtain ⟨S, hSV, hScov⟩ := h₂ D La VV hLa hVV hiso hstab hC
  let T : Finset (Set (InfinitePlace E → ι → ℂ)) :=
    S.image fun y => MulAction.orbit Γ (vecAt v y)
  have hT : ∀ o ∈ T, ∃ y, y ∈ S ∧ MulAction.orbit Γ (vecAt v y) = o := fun o ho => by
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 ho
    exact ⟨y, hy, e⟩
  choose! Y hYS hYo using hT
  have hP : vecAt v '' VV = ⋃ o ∈ (T : Set (Set (InfinitePlace E → ι → ℂ))), o := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hyS, γ, hγ, rfl⟩ := hScov x hx
      refine ⟨MulAction.orbit Γ (vecAt v y), Finset.mem_image.2 ⟨y, hyS, rfl⟩, ?_⟩
      rw [← archEmbed_smul_vecAt]
      exact ⟨⟨archEmbed h v γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩⟩, rfl⟩
    · rintro ⟨o, ho, hp⟩
      rw [← hYo o ho] at hp
      obtain ⟨⟨γ', hγ'⟩, rfl⟩ := hp
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
      exact ⟨γ • Y o, hstab γ hγ _ (hSV (hYS o ho)), (archEmbed_smul_vecAt h v γ (Y o)).symm⟩
  have hdisj : (T : Set (Set (InfinitePlace E → ι → ℂ))).PairwiseDisjoint fun o => o := by
    intro o₁ h₁' o₂ h₂' hne
    refine Set.disjoint_left.2 fun p hp1 hp2 => hne ?_
    rw [← hYo o₁ h₁'] at hp1 ⊢
    rw [← hYo o₂ h₂'] at hp2 ⊢
    exact (MulAction.orbit_eq_iff.2 hp1).symm.trans (MulAction.orbit_eq_iff.2 hp2)

  have hcount : ∀ g t, countBelow M VV g t = ∑ o ∈ T,
      ∑' q : Γ ⧸ (vecStabGroup h v La (Y o)).subgroupOf Γ,
        belowIndicator M (vecAt v (Y o)) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) := by
    intro g t
    have hPA : vecAt v '' {x ∈ VV | M.len (invApply g (vecAt v x)) < t} =
        vecAt v '' VV ∩ {p | M.len (g⁻¹ • p) < t} := by
      ext p
      constructor
      · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxt⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
        exact ⟨x, ⟨hx, hxt⟩, rfl⟩
    have h1 : countBelow M VV g t =
        ∑' p : (vecAt v '' VV : Set _), {p | M.len (g⁻¹ • p) < t}.indicator 1 (p : _) := by
      rw [countBelow, ← (vecAt_injective v).encard_image, hPA, ← ENNReal.tsum_set_one,
        tsum_subtype (vecAt v '' VV), Set.indicator_indicator, ← tsum_subtype]
      rfl
    rw [h1, hP, ENNReal.tsum_biUnion' hdisj]
    refine (Finset.tsum_subtype' T fun o : Set (InfinitePlace E → ι → ℂ) =>
      ∑' p : o, {p | M.len (g⁻¹ • p) < t}.indicator (1 : (InfinitePlace E → ι → ℂ) → ℝ≥0∞) (p : InfinitePlace E → ι → ℂ)).trans ?_
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [tsum_orbit_eq_tsum_quotient (vecAt v (Y o)) o (hYo o ho) _ (stabilizer_vecAt h v La (Y o))]
    refine tsum_congr fun q => ?_
    simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv,
      mul_smul]
    rfl
  have hm : ∀ t : ℝ, 0 < t → massBelow M μ FD VV t =
      ∑ o ∈ T, Cf (Y o) * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro t ht
    rw [massBelow, lintegral_congr fun g => hcount g t, MeasureTheory.lintegral_finsetSum]
    · exact Finset.sum_congr rfl fun o ho => hCeq (Y o) (hSV (hYS o ho)) t ht
    · intro o ho
      letI := hQc ((vecStabGroup h v La (Y o)).subgroupOf Γ)
      exact Measurable.tsum fun q =>
        (measurable_belowIndicator M _ t).comp (measurable_const_mul _)
  refine ⟨FD, hFD, fun t ht => ⟨?_, fun θ hθ => ?_⟩⟩
  · rw [hm t ht]
    exact ENNReal.sum_lt_top.2 fun o ho =>
      ENNReal.mul_lt_top (hCf _ (hSV (hYS o ho))) ENNReal.ofReal_lt_top
  · rw [hm (θ * t) (mul_pos hθ ht), hm t ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hθ.le _)]
    ring

end Action

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVolumeFormIntComb
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem VolumeFormIntComb.proof : VolumeFormIntComb.Statement V d := by
  intro o b T
  have hd : finrank ℝ V = d := Fact.out
  let e : Basis (Fin d) ℝ V := Module.finBasisOfFinrankEq ℝ V hd
  have key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]
    rfl
  have hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) =
      e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext k i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply,
      mul_comm]
  rw [key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose,
    Int.cast_det T]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightPos
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix
open scoped ComplexOrder

section Steps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem WeightPos.proof (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by
  intro M g x hx w
  set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk
  have hne : invApply g (vecAt v x) w ≠ 0 := by
    intro hz
    have hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0 := hz
    have h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0 := by
      rw [hz', mulVec_zero]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at h2
    exact h₁ x hx w h2
  have hpos := (M.posDef w).dotProduct_mulVec_pos hne
  exact (Complex.pos_iff.mp hpos).1

end Steps

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedIndexBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem WeightedIndexBound.proof (E : Type*) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₅ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      MinkowskiVolumeForm.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E)) :
    WeightedIndexBound.Statement E := by
  intro c hc A hOA hFG hmin r ⟨a, ha, hr⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
  obtain ⟨e⟩ := h₁ A hOA hFG
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hOA ⟨a i, rfl⟩
  set T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ := fun i j => e.repr ⟨(a i : E), hmem i⟩ j with hT
  have hcoe : ∀ z : Fin (finrank ℚ E) → ℤ, ((∑ j, z j • e j : A) : E) = ∑ j, z j • (e j : E) := by
    intro z
    change A.subtype _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
    rfl
  have haT : ∀ i, (a i : E) = ∑ j, T i j • (e j : E) := by
    intro i
    rw [← hcoe]
    exact (congrArg Subtype.val (e.sum_repr ⟨(a i : E), hmem i⟩)).symm
  have hidx := h₂ A hOA e a T ha haT

  set Φ := weightedEmbed c with hΦ
  have hc0 : ∀ w, 0 ≤ c w := fun w => (hc w).le
  have hS : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  set lam := Real.sqrt (∑ w, c w) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hS
  have hlam2 : lam ^ 2 = ∑ w, c w := Real.sq_sqrt hS.le
  have hdpos : 0 < finrank ℚ E := Module.finrank_pos
  have hsd : 0 < Real.sqrt (finrank ℚ E) := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  set o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)) :=
    (Module.finBasisOfFinrankEq ℝ _ h₄).orientation
  set b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2) := fun i => Φ (e i : E)

  have hmink : (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤ |o.volumeForm b| := by
    refine h₅ o b lam hlam0 fun z hz => ?_
    have hsum : ∑ i, (z i : ℝ) • b i = Φ ((∑ i, z i • e i : A) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcoe, map_sum]
      simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
    rw [hsum]
    set x : A := ∑ i, z i • e i
    have hx : (x : E) ≠ 0 := by
      intro h0
      have hx0 : x = 0 := Subtype.ext h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
      exact hi (Fintype.linearIndependent_iff.1 e.linearIndependent z hx0 i)
    have hq := hmin x x.2 hx
    rw [hlam, ← Real.sqrt_sq (norm_nonneg (Φ x)), h₃ c hc0]
    exact Real.sqrt_le_sqrt hq

  have hab : (fun i => Φ (a i : E)) = fun i => ∑ j, (T i j : ℝ) • b j := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [haT i, map_sum]
    simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
  have hvol : o.volumeForm (fun i => Φ (a i : E)) = (T.det : ℝ) * o.volumeForm b := by
    rw [hab]; exact h₆ o b T

  have hr0 : 0 ≤ r := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (norm_nonneg _).trans (hr ⟨0, hdpos⟩ w.embedding)
  have hnorm : ∀ i, ‖Φ (a i : E)‖ ≤ r * lam := by
    intro i
    have h2 : ‖Φ (a i : E)‖ ^ 2 ≤ (r * lam) ^ 2 := by
      rw [h₃ c hc0, mul_pow, hlam2, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hr i w.embedding) 2
      nlinarith [hc0 w]
    nlinarith [norm_nonneg (Φ (a i : E)), mul_nonneg hr0 hlam0.le]
  have hhad : |o.volumeForm (fun i => Φ (a i : E))| ≤ (r * lam) ^ finrank ℚ E := by
    refine (o.abs_volumeForm_apply_le _).trans ?_
    calc ∏ i, ‖Φ (a i : E)‖ ≤ ∏ _i : Fin (finrank ℚ E), r * lam :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i)
      _ = (r * lam) ^ finrank ℚ E := by simp

  have hpos : 0 < (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := pow_pos (div_pos hlam0 hsd) _
  have hkey : |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤
      (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
    calc |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E
        ≤ |(T.det : ℝ)| * |o.volumeForm b| :=
          mul_le_mul_of_nonneg_left hmink (abs_nonneg _)
      _ = |o.volumeForm (fun i => Φ (a i : E))| := by rw [hvol, abs_mul]
      _ ≤ (r * lam) ^ finrank ℚ E := hhad
      _ = (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
          rw [← mul_pow]; congr 1; field_simp
  exact hidx.trans (le_of_mul_le_mul_right hkey hpos)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedLenSmul
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem WeightedLenSmul.vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i
  simp [vecAt, map_mul]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.invApply_vecAt_smul {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) (a : E) (x : W) (w : InfinitePlace E) :
    invApply g (vecAt v (a • x)) w = w.embedding a • invApply g (vecAt v x) w := by
  simp only [invApply, WeightedLenSmul.vecAt_smul, Matrix.mulVec_smul]


omit [DecidableEq ι] in
theorem WeightedLenSmul.star_smul_dotProduct_mulVec_smul (P : Matrix ι ι ℂ) (c : ℂ)
    (z : ι → ℂ) :
    star (c • z) ⬝ᵥ (P *ᵥ (c • z)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (P *ᵥ z)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, mul_comm c, Complex.star_def, Complex.conj_mul']
  push_cast
  ring


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by
  intro M g x a
  rw [(h₁ M _).2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [WeightedLenSmul.invApply_vecAt_smul, WeightedLenSmul.star_smul_dotProduct_mulVec_smul,
    Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

