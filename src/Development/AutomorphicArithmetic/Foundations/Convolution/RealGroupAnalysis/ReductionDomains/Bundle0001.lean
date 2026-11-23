module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import GroundTheory.AutomorphicForms.RealIwasawaIntegration
public import GroundTheory.AutomorphicForms.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem mem_bor_iff {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g ∈ M.Bor F ↔ g 1 0 = 0 := by
  constructor
  · intro h
    exact h (show (id (0 : Fin 2)) < id (1 : Fin 2) by decide)
  · intro h i j hij
    have hij' : j < i := hij
    have hi : i = 1 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    exact h

private theorem nm_val {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (b : A F) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [M.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriangular_diagonal_product {F : Type} [Field F] [NumberField F] (g : G1 F) (h : g 1 0 = 0) :
    g 0 0 * g 1 1 = 1 := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have h' : g.1 1 0 = 0 := h
  rw [h', mul_zero, sub_zero] at hd
  exact hd

private def dg {F : Type} [Field F] [NumberField F] (g : M.Bor F) : IdeleGroup F :=
  ⟨g.1 0 0, g.1 1 1, upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2),
    (mul_comm _ _).trans (upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2))⟩

theorem UpperTheory.ConvolutionTheory.R2.M.borHomeo :
    ∀ (F : Type) [Field F] [NumberField F], IsClosed (M.Bor F : Set (G1 F)) ∧ ∃ e : IdeleGroup F × A F ≃ₜ M.Bor F, ∀ p, (e p : G1 F) = nU p.2 * mD p.1 := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have : (M.Bor F : Set (G1 F)) = {g | g 1 0 = 0} := Set.ext mem_bor_iff
    rw [this]
    exact isClosed_eq (M.continuous_entry 1 0) continuous_const
  · have hmem : ∀ p : IdeleGroup F × A F, nU p.2 * mD p.1 ∈ M.Bor F := fun p => by
      rw [mem_bor_iff]
      show (nU p.2 * mD p.1).1 1 0 = 0
      rw [nm_val]
      simp
    refine ⟨{ toFun := fun p => ⟨nU p.2 * mD p.1, hmem p⟩
              invFun := fun g => (dg g, g.1 0 1 * g.1 0 0)
              left_inv := ?_
              right_inv := ?_
              continuous_toFun := ?_
              continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨a, b⟩
      have e00 : (nU b * mD a) 0 0 = (a : A F) := by
        show (nU b * mD a).1 0 0 = _
        rw [nm_val]; simp
      have e01 : (nU b * mD a) 0 1 = b * ((a⁻¹ : (A F)ˣ) : A F) := by
        show (nU b * mD a).1 0 1 = _
        rw [nm_val]; simp
      refine Prod.ext (Units.ext e00) ?_
      show (nU b * mD a) 0 1 * (nU b * mD a) 0 0 = b
      rw [e00, e01, mul_assoc, Units.inv_mul, mul_one]
    · rintro ⟨g, hg⟩
      have h10 := (mem_bor_iff g).1 hg
      have hd := upperTriangular_diagonal_product g h10
      refine Subtype.ext (Subtype.ext ?_)
      show (nU (g 0 1 * g 0 0) * mD (dg ⟨g, hg⟩)).1 = g.1
      rw [nm_val]
      have hinv : (((dg ⟨g, hg⟩)⁻¹ : (A F)ˣ) : A F) = g 1 1 := rfl
      have hval : ((dg ⟨g, hg⟩ : (A F)ˣ) : A F) = g 0 0 := rfl
      rw [hinv, hval]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · show g 0 1 * g 0 0 * g 1 1 = g 0 1
        rw [mul_assoc, hd, mul_one]
      · exact h10.symm
      · rfl
    · exact Continuous.subtype_mk
        ((M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)) _
    · have c : ∀ i j, Continuous fun g : M.Bor F => g.1 i j := fun i j =>
        (M.continuous_entry i j).comp continuous_subtype_val
      exact (Units.continuous_iff.2 ⟨c 0 0, c 1 1⟩).prodMk ((c 0 1).mul (c 0 0))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorLeft
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem lintegral_mul_left_adele {F : Type} [Field F] [NumberField F] (c : (A F)ˣ) (g : A F → ℝ≥0∞) :
    ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) = ENNReal.ofReal (ab c)⁻¹ * ∫⁻ s, g s ∂(adeleMeasure F) := by
  have he : MeasurableEmbedding (fun x : A F => c • x) := (Homeomorph.smul c).measurableEmbedding
  have h1 : ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) =
      ∫⁻ s, g s ∂((adeleMeasure F).map (fun x : A F => c • x)) :=
    (he.lintegral_map g).symm
  rw [h1, map_smul_adeleMeasure, lintegral_smul_measure]
  rfl

private theorem wt_mul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : M.wt (s * t) = M.wt s * M.wt t := by
  have hs : 0 ≤ ((ab s)⁻¹ ^ 2 : ℝ) := by positivity
  simp only [M.wt]
  rw [← ENNReal.ofReal_mul hs, M.ab_mul, mul_inv, mul_pow]

theorem UpperTheory.ConvolutionTheory.R2.M.borLeft :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∀ (b₀ : A F) (a₀ : (A F)ˣ), ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _ f _ b₀ a₀
  have key : ∀ (a : (A F)ˣ) (b : A F), nU b₀ * mD a₀ * (nU b * mD a) =
      nU (b₀ + ((a₀ * a₀ : (A F)ˣ) : A F) * b) * mD (a₀ * a) := by
    intro a b
    rw [M.nU_add, M.mD_mul, mul_assoc (nU b₀), ← mul_assoc (mD a₀), M.mD_mul_nU]
    simp [pow_two, mul_assoc]
  have hc : ENNReal.ofReal (ab (a₀ * a₀))⁻¹ = M.wt a₀ := by
    simp only [M.wt]
    rw [M.ab_mul, mul_inv, pow_two]
  have inner : ∀ a : IdeleGroup F,
      ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) =
        ∫⁻ b, f (nU b * mD (a₀ * a)) * M.wt (a₀ * a) ∂(adeleMeasure F) := by
    intro a
    have hwa : M.wt a ≠ ∞ := ENNReal.ofReal_ne_top
    have hwb : M.wt (a₀ * a) ≠ ∞ := ENNReal.ofReal_ne_top
    simp only [key]
    rw [lintegral_mul_const' _ _ hwa, lintegral_mul_const' _ _ hwb,
      lintegral_mul_left_adele (a₀ * a₀) (fun s => f (nU (b₀ + s) * mD (a₀ * a))),
      lintegral_add_left_eq_self (fun s => f (nU s * mD (a₀ * a))) b₀, hc, wt_mul]
    ring
  simp only [inner]
  exact lintegral_mul_left_eq_self
    (fun x : IdeleGroup F => ∫⁻ b, f (nU b * mD x) * M.wt x ∂(adeleMeasure F)) a₀
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cdMeas :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (t : (A F)ˣ), MeasurePreserving (cD t) M₀.μ M₀.μ := by
  intro F _ _ M₀ t
  haveI := M₀.haar
  haveI := M₀.right
  have hm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  let e : G1 F ≃ₜ* G1 F :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (M₀.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map M₀.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, M₀.μ.map (cD t) = c • M₀.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (M₀.μ.map (cD t)) M₀.μ⟩
  have h2 : M₀.μ.map (cD (t * t)) = M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : M₀.μ.map (cD (t * t)) = (c * c) • M₀.μ := by
    have : (cD (t * t) : G1 F → G1 F) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc,
      Measure.map_smul c (hm t).aemeasurable, hc, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 F)
  have hpos : M₀.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds M₀.μ hK1).ne'
  have hfin : M₀.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = M₀.μ K := by
    have := congrArg (fun m : Measure (G1 F) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * M₀.μ K = 1 * M₀.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CptMeas
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cptMeas :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ μK : Measure K, μK.IsHaarMeasure ∧ IsProbabilityMeasure μK ∧ (μK.map Subtype.val) (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, (μK.map Subtype.val).map (k * ·) = μK.map Subtype.val) ∧ ∀ k ∈ K, (μK.map Subtype.val).map (· * k) = μK.map Subtype.val := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  have hval : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  let μ : Measure K := Measure.haarMeasure ⊤
  haveI hH : μ.IsHaarMeasure := inferInstance
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using this
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.isMulRightInvariant_of_compactSpace μ
  refine ⟨μ, hH, hprob, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hval hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    simp [this]
  · intro k hk
    have hcomp : (fun x : G => k * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => (⟨k, hk⟩ : K) * x) := by
      ext x; simp
    rw [Measure.map_map (measurable_const_mul k) hval, hcomp,
      ← Measure.map_map hval (measurable_const_mul _), map_mul_left_eq_self]
  · intro k hk
    have hcomp : (fun x : G => x * k) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => x * (⟨k, hk⟩ : K)) := by
      ext x; simp
    rw [Measure.map_map (measurable_mul_const k) hval, hcomp,
      ← Measure.map_map hval (measurable_mul_const _), map_mul_right_eq_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.EntryMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem real_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M * Mᵀ = 1 := by
  constructor
  · intro h
    have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
      intro z
      have h2 := congrArg (· ^ 2) (h z)
      simp only [Reduction.euclidNorm_sq, Real.norm_eq_abs, sq_abs] at h2
      simpa only [dotProduct, sq] using h2
    have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
      intro x z
      have h1 := hq (x + z)
      rw [add_vecMul] at h1
      simp only [add_dotProduct, dotProduct_add, hq] at h1
      rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
      linarith
    ext i j
    have h3 := hb (Pi.single i 1) (Pi.single j 1)
    rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [transpose_apply]
    refine Eq.trans h3 ?_
    simp [Pi.single_apply]
  · intro h z
    refine Reduction.euclidNorm_vecMul_unitary ?_ z
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact h

private theorem entry_mul {F : Type} [Field F] [NumberField F] (k : G1 F) (w : InfinitePlace F) (i j : Fin 2) :
    ((k.1 * k.1ᵀ) i j).1 w = ∑ l, (k i l).1 w * (k j l).1 w := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

private theorem entry_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem place_iff {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (w : InfinitePlace F) :
    Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ i j, ((k.1 * k.1ᵀ) i j).1 w = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w := by
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ψ ((k i j).1 w)
  have e : ∀ z : Fin 2 → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (gl k) : Matrix (Fin 2) (Fin 2) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* M := by
    intro z
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecMul, dotProduct, map_sum, map_mul]
    rfl
  have key : ∀ i j, (M * Mᵀ) i j = ψ (((k.1 * k.1ᵀ) i j).1 w) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [entry_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  have key1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = ψ (((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w) := by
    intro i j
    rw [entry_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ z : Fin 2 → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z := by
    rw [Reduction.mem_archCompact]
    constructor
    · intro h z
      have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
      rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
    · intro h z
      rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
  rw [h1, real_iff]
  constructor
  · intro h i j
    apply ψ.injective
    rw [← key, ← key1, h]
  · intro h
    ext i j
    rw [key, key1, h i j]

theorem UpperTheory.ConvolutionTheory.R2.M.kkInf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ k : G1 F, InfOrth k ↔ ∀ w, Reduction.infAt w (gl k) ∈ Reduction.archCompact w := by
  intro F _ _ _ k
  simp only [place_iff, InfOrth]
  exact ⟨fun h w i j => congrFun (h i j) w, fun h i j => funext fun w => h w i j⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IdeleCover
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.ideleCover :
    ∀ (F : Type) [Field F] [NumberField F] (c : ℝ), 0 < c → ∃ (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C ∧ 1 < ab ρ ∧ ∀ a : IdeleGroup F, c ≤ ab a → ∃ (t : Fˣ) (n : ℕ), ∃ x ∈ C, IdeleGroup.diagonal F t * a = ρ ^ n * x := by
  intro F _ _ c hc
  set ρ : IdeleGroup F := Reduction.posIdele (K := F) 2 two_pos with hρ
  have hr : ab ρ = 2 ^ Module.finrank ℚ F := Reduction.ideleModule_posIdele (K := F) 2 two_pos
  have h1 : 1 < ab ρ := by
    rw [hr]
    exact one_lt_pow₀ one_lt_two Module.finrank_pos.ne'
  have hr0 : 0 < ab ρ := one_pos.trans h1
  obtain ⟨S, hS, hSm⟩ := Reduction.exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc (c * ab ρ)
  refine ⟨S, ρ, hS, h1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx h1
  have hp : 0 < ab ρ ^ n := pow_pos hr0 n
  have hm : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ) = ab a / ab ρ ^ n := by
    have : (IdeleGroup.ideleModule F ((ρ ^ n)⁻¹ * a) : ℝ)
        = ((IdeleGroup.ideleModule F ρ : ℝ) ^ n)⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv, map_pow]
    rw [this, div_eq_inv_mul]
    rfl
  obtain ⟨t, ht⟩ := hSm ((ρ ^ n)⁻¹ * a)
    (by
      rw [hm, le_div_iff₀ hp]
      have := (le_div_iff₀ hc).1 hn1
      linarith)
    (by
      rw [hm, div_le_iff₀ hp]
      have h2 := (div_lt_iff₀ hc).1 hn2
      rw [pow_succ] at h2
      nlinarith)
  refine ⟨t, n, _, ht, ?_⟩
  rw [mul_left_comm, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IdeleSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem ab_pow' {F : Type} [Field F] [NumberField F] (ρ : IdeleGroup F) (n : ℕ) :
    ab (ρ ^ n) = ab ρ ^ n := by
  induction n with
  | zero => simpa using M.ab_one (F := F)
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; exact M.ab_mul _ _

theorem UpperTheory.ConvolutionTheory.R2.M.ideleSum :
    ∀ (F : Type) [Field F] [NumberField F] (C : Set (IdeleGroup F)) (ρ : IdeleGroup F), IsCompact C → 1 < ab ρ → ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) < ⊤ := by
  intro F _ _ C ρ hC hρ
  have hcont : Continuous fun a : IdeleGroup F => (ab a)⁻¹ ^ 2 :=
    (M.continuous_ab.inv₀ fun a => (M.ab_pos a).ne').pow 2
  obtain ⟨B, hB⟩ := hC.bddAbove_image hcont.continuousOn
  have hBC : ∀ c ∈ C, (ab c)⁻¹ ^ 2 ≤ B := fun c hc => hB ⟨c, hc, rfl⟩
  set q : ℝ := (ab ρ)⁻¹ ^ 2 with hq
  have hρ0 : 0 < ab ρ := by linarith
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have : (ab ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
    have h0 : 0 ≤ (ab ρ)⁻¹ := by positivity
    rw [hq]; nlinarith
  have hterm : ∀ n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) ≤
      ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
    intro n
    have hS : MeasurableSet ((ρ ^ n * ·) '' C) :=
      (hC.image (continuous_const_mul _)).measurableSet
    have hμ : ideleMeasure F ((ρ ^ n * ·) '' C) = ideleMeasure F C := by
      rw [Set.image_mul_left]; exact measure_preimage_mul _ _ _
    calc ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
        ≤ ∫⁻ _ in (ρ ^ n * ·) '' C, ENNReal.ofReal q ^ n * ENNReal.ofReal B ∂(ideleMeasure F) := by
          refine setLIntegral_mono' hS ?_
          rintro _ ⟨c, hc, rfl⟩
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (ab (ρ ^ n * c))⁻¹ ^ 2 = q ^ n * (ab c)⁻¹ ^ 2 := by
            rw [M.ab_mul, ab_pow', hq, mul_inv, mul_pow, inv_pow, inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
          rw [e]
          exact mul_le_mul_of_nonneg_left (hBC c hc) (by positivity)
      _ = ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := by
          rw [setLIntegral_const, hμ, mul_assoc]
  have hr : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hq1
  have hfin : ENNReal.ofReal B * ideleMeasure F C < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top
  calc ∫⁻ a in ⋃ n : ℕ, (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F)
      ≤ ∑' n : ℕ, ∫⁻ a in (ρ ^ n * ·) '' C, M.wt a ∂(ideleMeasure F) := lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal q ^ n * (ENNReal.ofReal B * ideleMeasure F C) := ENNReal.tsum_le_tsum hterm
    _ = (1 - ENNReal.ofReal q)⁻¹ * (ENNReal.ofReal B * ideleMeasure F C) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hr)) hfin
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IwDens
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwDens :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F), ∃ ρ : Measure (IdeleGroup F × G1 F), SFinite ρ ∧ (∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u) ∧ ∀ u : IdeleGroup F × G1 F → ℂ, (Integrable u ρ ↔ Integrable (fun p => (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p) M₀.ν) ∧ ∫ p, u p ∂ρ = ∫ p, (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p ∂M₀.ν := by
  intro F _ _ M₀
  have hfm : Measurable (fun p : IdeleGroup F × G1 F => Real.toNNReal ((ab p.1)⁻¹ ^ 2)) :=
    (((M.continuous_ab.measurable.comp measurable_fst).inv).pow_const 2).real_toNNReal
  have hwm : Measurable (fun p : IdeleGroup F × G1 F => M.wt p.1) :=
    M.measurable_wt.comp measurable_fst
  have hsm : ∀ (u : IdeleGroup F × G1 F → ℂ) (p : IdeleGroup F × G1 F),
      Real.toNNReal ((ab p.1)⁻¹ ^ 2) • u p = (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p := by
    intro u p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul]
  haveI : IsProbabilityMeasure M₀.κ := M₀.prob
  haveI : SFinite M₀.ν := by unfold Meas.ν; infer_instance
  refine ⟨M₀.ν.withDensity fun p => (Real.toNNReal ((ab p.1)⁻¹ ^ 2) : ℝ≥0∞), inferInstance, ?_, ?_⟩
  · intro u _
    have h := lintegral_withDensity_eq_lintegral_mul_non_measurable M₀.ν hwm
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top) (fun p => u (mD p.1 * p.2))
    exact h
  · intro u
    refine ⟨?_, ?_⟩
    · rw [integrable_withDensity_iff_integrable_smul hfm]
      simp only [hsm]
    · rw [integral_withDensity_eq_integral_smul hfm]
      simp only [hsm]
end

