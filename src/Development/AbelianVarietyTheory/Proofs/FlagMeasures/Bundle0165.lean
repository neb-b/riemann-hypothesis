module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestWeightVectorFixedByLowerUnitriangular
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Dec.TauExt

variable {n : ℕ} {ε : Fin n → Bool}

theorem conj_mul (a b : Matrix (Fin n) (Fin n) ℂ) : (a * b).map star = a.map star * b.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem conj_one : (1 : Matrix (Fin n) (Fin n) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem conj_conj (a : Matrix (Fin n) (Fin n) ℂ) : (a.map star).map star = a := by
  ext i j; simp

theorem conj_Jm : (Jm ε).map star = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases h' : ε i = true <;> simp [Jm, h']
  · simp [Jm, h]

theorem conj_mem {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k.map star ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have h : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    have e : star (k.map star) = (star k).map star := by ext i j; simp
    rw [e, ← conj_mul, h, conj_one]
  · have := congrArg (fun m : Matrix (Fin n) (Fin n) ℂ => m.map star) hk.2
    simpa only [conj_mul, conj_Jm] using this

theorem mem_KC {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

theorem one_mem_K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

theorem isOpen_units : IsOpen {y : Fin n → Fin n → ℂ | IsUnit (Matrix.of y)} := by
  simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isOpen_ne_fun (Continuous.matrix_det (A := fun y : Fin n → Fin n → ℂ => Matrix.of y) continuous_id)
    continuous_const

theorem conj_torus (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star =
      Matrix.diagonal fun a => Complex.exp (((-θ) a : ℂ) * Complex.I) := by
  rw [Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

section Mul

variable {B : Type} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] {τ : Matrix (Fin n) (Fin n) ℂ → B}

omit [CompleteSpace B] in
theorem differentiableOn_mul
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a) (hb : IsUnit b) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (a * Matrix.of y * b)) {y | Matrix.of y ∈ KC ε} := by
  have h : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => (a * Matrix.of y * b) i j := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hd.comp h.differentiableOn fun y hy => (ha.mul hy.1).mul hb

theorem mul_on_KC
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b) :
    ∀ a ∈ KC ε, ∀ b ∈ KC ε, τ (a * b) = τ a * τ b := by
  have hd' : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | Matrix.of y ∈ KC ε} :=
    hd.mono fun y hy => hy.1
  have h1 : ∀ a ∈ Kset ε, ∀ b ∈ KC ε, τ (a * b * 1) - τ a * τ b = 0 := fun a ha =>
    _root_.GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset n ε B (fun y => τ (a * y * 1) - τ a * τ y)
      ((differentiableOn_mul hd (mem_KC ha).1 isUnit_one).sub (hd'.const_mul _))
      fun k hk => by rw [Matrix.mul_one, hm a ha k hk, sub_self]
  intro a ha b hb
  have h2 := _root_.GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset n ε B (fun y => τ (1 * y * b) - τ y * τ b)
    ((differentiableOn_mul hd isUnit_one hb.1).sub (hd'.mul_const _))
    (fun k hk => by simpa using h1 k hk b hb) a ha
  simpa [sub_eq_zero] using h2

end Mul

theorem adj_on_KC {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    (hd : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)})
    (hK : ∀ y ∈ Kset ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) :
    ∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ := by
  intro y hy u v
  have hc : ∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | IsUnit (Matrix.of y)} := fun u v =>
    ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ W v)).differentiable.comp_differentiableOn hd
  have ht : Differentiable ℂ fun y : Fin n → Fin n → ℂ => fun i j => y j i := by fun_prop
  have h1 : DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => star ⟪u, τ (Matrix.of y)ᴴ v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε} := by
    intro z hz
    have hz' : IsUnit (Matrix.of fun i j => (star z) j i) := by
      exact hz.1.star
    have h2 := (((hc u v).differentiableAt (isOpen_units.mem_nhds hz')).comp (star z) (ht (star z))).star_star
    rw [star_star] at h2
    exact h2.differentiableWithinAt
  have h3 := _root_.GlobalTheory.Dec.KCIdent.eq_zero_on_KC_of_eq_zero_on_Kset n ε ℂ (fun y => ⟪v, τ y u⟫_ℂ - star ⟪u, τ yᴴ v⟫_ℂ)
    (((hc v u).mono fun y (hy : Matrix.of y ∈ KC ε) => hy.1).sub h1)
    (fun k hk => by rw [← hK k hk, Complex.star_def, inner_conj_symm, sub_self]) y hy
  rw [← inner_conj_symm, sub_eq_zero.1 h3, Complex.star_def, Complex.conj_conj]

theorem tauExists : TauExists := by
  intro n ε abelian₂ H _ _ σ S w ⟨⟨h1, hmul⟩, hiso, hcont⟩ ⟨hfin, hst, hirr, _, hdom⟩ hw hwt
  classical
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let π : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun k =>
    if h : k ∈ Kset ε then ((σ (k.map star)).comp S.subtypeL).codRestrict S
      fun v => hst _ (conj_mem h) _ v.2 else 0
  have hπ : ∀ k ∈ Kset ε, ∀ v : S, (π k v : H) = σ (k.map star) v := fun k hk v => by
    simp only [π, dif_pos hk]; rfl
  have hπ1 : π 1 = 1 := by
    ext v
    rw [hπ 1 one_mem_K, conj_one, h1]; rfl
  have hπm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, π (a * b) = π a * π b := by
    intro a ha b hb
    ext v
    rw [hπ _ (Kset_mul ε ha hb), conj_mul, hmul _ (conj_mem ha) _ (conj_mem hb), ContinuousLinearMap.mul_apply,
      hπ a ha, hπ b hb]
    rfl
  have hπc : ContinuousOn π (Kset ε) := by
    refine continuousOn_clm_apply.2 fun v => ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr ((hcont v).comp ?_ fun k hk => conj_mem hk) fun k hk => hπ k hk v
    exact (continuous_id.matrix_map continuous_star).continuousOn
  obtain ⟨τ, hd, hτ⟩ := _root_.GlobalTheory.HolExt.exists_holomorphic_extension n ε (S →L[ℂ] S) π hπ1 hπm hπc
  have hτσ : ∀ k ∈ Kset ε, ∀ v : S, (τ k v : H) = σ (k.map star) v := fun k hk v => by
    rw [hτ k hk, hπ k hk]
  have hτ1 : τ 1 = 1 := by rw [hτ 1 one_mem_K, hπ1]
  have hτm : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, τ (a * b) = τ a * τ b := fun a ha b hb => by
    rw [hτ _ (Kset_mul ε ha hb), hτ a ha, hτ b hb, hπm a ha b hb]
  have hrep : IsCRepOn (KC ε) τ := ⟨hτ1, mul_on_KC hd hτm⟩
  have hwτ : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Kset ε) τ (-μ) v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
    intro μ v
    constructor
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      have := congrArg Subtype.val (h (-θ) hθ')
      rw [hτσ _ hθ', conj_torus, neg_neg] at this
      simpa using this
    · intro h θ hθ
      have hθ' := conj_mem hθ
      rw [conj_torus] at hθ'
      apply Subtype.ext
      rw [hτσ _ hθ, conj_torus, h (-θ) hθ']
      simp
  refine ⟨τ, ⟨hfin, hrep, fun u v => ?_, adj_on_KC hd fun k hk u v => ?_, fun S' hS' => ?_, hw,
    (hwτ abelian₂ w).2 hwt, ?_⟩, hτσ⟩
  · exact ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ S v)).differentiable.comp_differentiableOn
      (hd.mono fun y hy => hy.1)
  · have hk' : kᴴ ∈ Kset ε := Kset_star ε hk
    have hi : ∀ x : S, ‖τ k x‖ = ‖x‖ := fun x => by
      rw [Submodule.coe_norm, hτσ k hk, hiso _ (conj_mem hk), Submodule.coe_norm]
    have e : τ k (τ kᴴ v) = v := by
      have : k * kᴴ = 1 := Unitary.mul_star_self_of_mem hk.1
      rw [← ContinuousLinearMap.mul_apply, ← hτm k hk _ hk', this, hτ1]; rfl
    conv_lhs => rw [← e]
    exact LinearIsometry.inner_map_map ⟨(τ k).toLinearMap, hi⟩ u _
  · have hs : IsKStableOn ε σ (S'.map S.subtype) := by
      rintro g hg _ ⟨v, hv, rfl⟩
      refine ⟨τ (g.map star) v, hS' _ (conj_mem hg) v hv, ?_⟩
      have := hτσ _ (conj_mem hg) v
      rwa [conj_conj] at this
    rcases hirr _ (S.map_subtype_le S') hs with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · refine _root_.GlobalTheory.Dec.LowFix.lowest_fixed n ε abelian₂ S τ w hrep (hd.differentiableAt (isOpen_units.mem_nhds ?_))
      ((hwτ abelian₂ w).2 hwt) fun μ v hv h => hdom μ v v.2 (fun e => hv (Subtype.ext e)) ((hwτ μ v).1 h)
    exact (isUnit_one : IsUnit (1 : Matrix (Fin n) (Fin n) ℂ))

end GlobalTheory.Dec.TauExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityUnfoldSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GenUnfold

theorem covol_eq_of_strict {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) (hμ : ∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) {F : Set G}
    (hF : MeasurableSet F) (h : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) :
    covol (Γ : Set G) μ Set.univ = μ F := by
  classical
  have hmeas : ∀ a : G, Measurable (fun y : G => a * y) := fun a => measurable_const_mul a
  unfold covol
  apply le_antisymm
  · refine iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le ?_ le_rfl))
    intro x _
    obtain ⟨γ, hγ, -⟩ := h x
    exact ⟨γ, γ.2, hγ⟩
  · refine le_iInf fun D => le_iInf fun hD => le_iInf fun hcov => ?_

    have hsub : F ⊆ ⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D := by
      intro x hx
      obtain ⟨γ, hγ, hxD⟩ := hcov x trivial
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hx, hxD⟩

    have hpiece : ∀ γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) =
        μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ
      have hS : MeasurableSet ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := (hmeas _ hF).inter hD
      have e : (μ.map (fun y => (γ : G) * y)) ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) =
          μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by rw [hμ γ γ.2]
      rw [Measure.map_apply (hmeas _) hS] at e
      rw [← e]
      congr 1
      ext y
      simp [inv_mul_cancel_left]

    have hdisj : Pairwise (Function.onFun Disjoint
        fun γ : Γ => (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := by
      intro γ₁ γ₂ hne
      refine Set.disjoint_left.2 fun y hy₁ hy₂ => hne ?_
      obtain ⟨δ, -, huniq⟩ := h y
      have e₁ := huniq γ₁⁻¹ (by simpa using hy₁.1)
      have e₂ := huniq γ₂⁻¹ (by simpa using hy₂.1)
      exact inv_injective (e₁.trans e₂.symm)
    calc μ F ≤ μ (⋃ γ : Γ, F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ (F ∩ (fun y => (γ : G) * y) ⁻¹' D) := measure_iUnion_le _
      _ = ∑' γ : Γ, μ ((fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) := tsum_congr hpiece
      _ = μ (⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' F ∩ D) :=
          (measure_iUnion hdisj fun γ => (hmeas _ hF).inter hD).symm
      _ ≤ μ D := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

theorem isInvInvariant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hUpos : μ (interior K) ≠ 0 :=
    (hUo.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hUfin : μ (interior K) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono interior_subset) hK.measure_lt_top).ne
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c := Measure.haarScalarFactor μ.inv μ
  have key : ∀ s : Set G, MeasurableSet s → μ (Inv.inv ⁻¹' s) = (c : ENNReal) * μ s := by
    intro s hs
    have e : μ.inv s = (c • μ) s := by rw [← hc]
    rw [Measure.inv_def, Measure.map_apply measurable_inv hs, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have h1 := key (interior K) hUo.measurableSet
  have h2 := key (Inv.inv ⁻¹' interior K) (hUo.measurableSet.preimage measurable_inv)
  have hUU : (Inv.inv ⁻¹' (Inv.inv ⁻¹' interior K) : Set G) = interior K := by
    ext x
    simp
  rw [hUU, h1, ← mul_assoc] at h2
  have hcc : (c : ENNReal) * c = 1 :=
    (ENNReal.mul_left_inj hUpos hUfin).1 (h2.symm.trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have hnn : c * c = 1 := by exact_mod_cast hcc
    have hr : (c : ℝ) * c = 1 := by exact_mod_cast hnn
    have h0 : (0 : ℝ) ≤ c := c.2
    exact NNReal.eq (by push_cast; nlinarith)
  constructor
  rw [hc, hc1, one_smul]

private lemma exists_nhds_one_inter_discrete_subgroup_eq_one {H : Type} [Group H] [TopologicalSpace H] (Γ : Subgroup H)
    [DiscreteTopology Γ] : ∃ V ∈ nhds (1 : H), ∀ γ ∈ Γ, γ ∈ V → γ = 1 := by

  have ho : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 ho
  have h1 : (1 : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := by
    rw [hpre]
    exact Set.mem_singleton _
  refine ⟨t, ht.mem_nhds h1, fun γ hγ hγt => ?_⟩
  have h2 : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' t : Set Γ) := hγt
  rw [hpre] at h2
  have h3 : (⟨γ, hγ⟩ : Γ) = 1 := h2
  simpa using congrArg Subtype.val h3

theorem exists_nhds_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsEmbedding j) (Γ : Subgroup H) [DiscreteTopology Γ] :
    ∃ U ∈ nhds (1 : G), ∀ γ ∈ Γ.map j, γ ∈ U → γ = 1 := by
  obtain ⟨V, hV, hVΓ⟩ := exists_nhds_one_inter_discrete_subgroup_eq_one Γ
  rw [hj.isInducing.nhds_eq_comap (1 : H), map_one] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.1 hV
  refine ⟨U, hU, fun γ hγ hγU => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
  rw [hVΓ x hx (hUV hγU), map_one]

theorem covol_withDensity_eq : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (Γ : Subgroup H) [DiscreteTopology Γ] (Φ b : G → ENNReal), Measurable Φ → Measurable b → (∀ h g, Φ (j h * g) = Φ g) → (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) → covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj Γ _ Φ b hΦ hb hΦinv hb1
  classical
  have hjc : Continuous j := hj.continuous
  have : ν.IsInvInvariant := isInvInvariant ν

  obtain ⟨hcnt, F, hFm, hF⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete G
    (Γ.map j) (exists_nhds_map j hj.toIsEmbedding Γ)
  have := hcnt
  have hcntH : Countable Γ :=
    Function.Injective.countable
      (f := fun γ : Γ => (⟨j γ, Subgroup.mem_map_of_mem j γ.2⟩ : Γ.map j))
      (fun a b hab => Subtype.ext (hj.injective (congrArg Subtype.val hab)))

  have hL : covol ((Γ.map j : Subgroup G) : Set G) (μ.withDensity Φ) Set.univ =
      ∫⁻ g in F, Φ g ∂μ := by
    rw [covol_eq_of_strict (Γ.map j) (μ.withDensity Φ) ?_ hFm hF, withDensity_apply _ hFm]
    intro γ hγ
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hγ
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs,
      withDensity_apply _ (measurable_const_mul _ hs), withDensity_apply _ hs,
      ← lintegral_indicator (measurable_const_mul _ hs), ← lintegral_indicator hs,
      ← lintegral_mul_left_eq_self (s.indicator Φ) (j x)]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_preimage, hΦinv]

  have hfib : ∀ g : G, ν {x : H | (j x)⁻¹ * g ∈ F} = covol (Γ : Set H) ν Set.univ := by
    intro g
    have hT : MeasurableSet {x : H | j x * g ∈ F} :=
      hFm.preimage (hjc.mul continuous_const).measurable
    have e₁ : {x : H | (j x)⁻¹ * g ∈ F} = Inv.inv ⁻¹' {x : H | j x * g ∈ F} := by
      ext x
      simp [map_inv]
    rw [e₁, Measure.measure_preimage_inv,
      covol_eq_of_strict Γ ν (fun γ _ => map_mul_left_eq_self ν γ) hT]
    intro x
    obtain ⟨δ, hδ, huniq⟩ := hF (j x * g)
    obtain ⟨γ, hγ, hδe⟩ := Subgroup.mem_map.1 δ.2
    refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
    · show j (γ * x) * g ∈ F
      rw [map_mul, mul_assoc, hδe]
      exact hδ
    · rintro ⟨γ', hγ'⟩ h'
      have h'' : ((⟨j γ', Subgroup.mem_map_of_mem j hγ'⟩ : Γ.map j) : G) * (j x * g) ∈ F := by
        have h3 : j (γ' * x) * g ∈ F := h'
        simpa [map_mul, mul_assoc] using h3
      have e₂ := huniq _ h''
      apply Subtype.ext
      apply hj.injective
      show j γ' = j γ
      rw [hδe]
      exact congrArg Subtype.val e₂
  have hm₁ : Measurable (fun p : G × H => j p.2 * p.1) :=
    ((hjc.comp continuous_snd).mul continuous_fst).measurable
  have hm₂ : Measurable (fun p : H × G => (j p.1)⁻¹ * p.2) :=
    ((hjc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm₃ : ∀ g : G, Measurable (fun x : H => (j x)⁻¹ * g) :=
    fun g => (hjc.inv.mul continuous_const).measurable
  have hbm : ∀ g : G, Measurable (fun x : H => b (j x * g)) :=
    fun g => hb.comp (hjc.mul continuous_const).measurable
  have hI : Measurable (F.indicator (1 : G → ENNReal)) := measurable_one.indicator hFm
  rw [hL]
  calc ∫⁻ g in F, Φ g ∂μ
      = ∫⁻ g, F.indicator 1 g * Φ g * ∫⁻ x, b (j x * g) ∂ν ∂μ := by
        rw [← lintegral_indicator hFm]
        refine lintegral_congr fun g => ?_
        rw [hb1 g, mul_one]
        by_cases hg : g ∈ F <;> simp [hg]
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 g * Φ g * b (j x * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul _ (hbm g)]
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 g * Φ g * b (j x * g) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact (((hI.comp measurable_fst).mul (hΦ.comp measurable_fst)).mul
          (hb.comp hm₁)).aemeasurable
    _ = ∫⁻ x, ∫⁻ g, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂μ ∂ν := by
        refine lintegral_congr fun x => ?_
        have e := lintegral_mul_left_eq_self (μ := μ)
          (fun g => F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g) (j x)
        simpa only [inv_mul_cancel_left, hΦinv] using e
    _ = ∫⁻ g, ∫⁻ x, F.indicator 1 ((j x)⁻¹ * g) * Φ g * b g ∂ν ∂μ := by
        apply lintegral_lintegral_swap
        exact (((hI.comp hm₂).mul (hΦ.comp measurable_snd)).mul
          (hb.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ν {x : H | (j x)⁻¹ * g ∈ F} * (Φ g * b g) ∂μ := by
        refine lintegral_congr fun g => ?_
        have hmg : MeasurableSet {x : H | (j x)⁻¹ * g ∈ F} := hFm.preimage (hm₃ g)
        simp_rw [mul_assoc]
        rw [lintegral_mul_const (f := fun x => F.indicator 1 ((j x)⁻¹ * g)) _ (hI.comp (hm₃ g)),
          ← lintegral_indicator_one hmg]
        rfl
    _ = ∫⁻ g, covol (Γ : Set H) ν Set.univ * (Φ g * b g) ∂μ := by
        simp_rw [hfib]
    _ = covol (Γ : Set H) ν Set.univ * ∫⁻ g, Φ g * b g ∂μ :=
        lintegral_const_mul _ (hΦ.mul hb)

end GlobalTheory.GenUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem muG_preimage_conj {n : ℕ} (ε : Fin n → Bool) (u : Formalism.REAL.UJ ε) (B : Set (Formalism.REAL.UJ ε)) :
    Formalism.REAL.muG ε ((fun g => u⁻¹ * g * u) ⁻¹' B) = Formalism.REAL.muG ε B := by
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  have : (fun g => u⁻¹ * g * u) ⁻¹' B = (fun g => u⁻¹ * g) ⁻¹' ((fun g => g * u) ⁻¹' B) := rfl
  rw [this, measure_preimage_mul, measure_preimage_mul_right]

theorem gauge_map_of_iso : ∀ (n n' : ℕ) (ε : Fin n → Bool) (ε' : Fin n' → Bool), n = n' → ∀ (T : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε') (u : Formalism.REAL.UJ ε), (∀ g, Formalism.REAL.hs (uMat (T (u * g * u⁻¹)) - 1) = Formalism.REAL.hs (uMat g - 1)) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → (ENNReal.ofReal c • Formalism.REAL.muG ε).map T = ENNReal.ofReal c' • Formalism.REAL.muG ε' := by
  intro n n' ε ε' hn T u hT c c' hc hc'
  subst hn
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : (Formalism.REAL.muG ε').IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : ((Formalism.REAL.muG ε).map T).IsHaarMeasure := T.isHaarMeasure_map _
  obtain ⟨a, ha⟩ : ∃ a : NNReal, (Formalism.REAL.muG ε).map T = a • Formalism.REAL.muG ε' :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hball : ∀ r : ℝ, Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      a * Formalism.REAL.muG ε' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro r
    have h1 := congrArg (fun m : Measure (Formalism.REAL.UJ ε') =>
      m {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}) ha
    have h2 := MeasurableEquiv.map_apply (μ := Formalism.REAL.muG ε) T.toHomeomorph.toMeasurableEquiv
      {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}
    have h3 : (T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
        (fun g => u⁻¹ * g * u) ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      ext g
      have := hT (u⁻¹ * g * u)
      rw [show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at this
      simp only [Set.mem_preimage, Set.mem_setOf_eq, this]
    change (Formalism.REAL.muG ε).map T _ = Formalism.REAL.muG ε ((T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' _) at h2
    rw [h3, muG_preimage_conj] at h2
    rw [← h2]
    simpa using h1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hca : c' = c * a := by
    have h1 := Filter.Tendsto.const_mul c' hc
    have h2 := Filter.Tendsto.const_mul (c * a) hc'
    have h3 := tendsto_nhds_unique h1 (h2.congr fun r => by
      rw [hball r, ENNReal.toReal_mul, ENNReal.coe_toReal]; ring)
    exact mul_right_cancel₀ hω.ne' h3
  rw [Measure.map_smul _ (show AEMeasurable (⇑T) (Formalism.REAL.muG ε) from T.continuous.measurable.aemeasurable), ha, hca, ENNReal.ofReal_mul' a.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_smul]
  rfl

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCosetStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootMeasure_transport_doubleCoset : ∀ (D : D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (g a a' : MatKR D.R.k D.R.rS) (μ : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → g ∈ UH (Hpk D.R.k D.R.rS) → a ∈ Sset D.R.k D.R.rS z → a' ∈ Sset D.R.k D.R.rS z' → IsRootMeasR D z z' p g μ → IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  first | exact @GlobalTheory.Amp.RootMove.rootMeas_move | exact GlobalTheory.Amp.RootMove.rootMeas_move | (intros; apply GlobalTheory.Amp.RootMove.rootMeas_move <;> assumption)
end

