module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ConjugationInvariantMeasure
section
noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace QPK

theorem ennreal_eq_one_of_mul {a b : ℝ≥0∞} (h0 : b ≠ 0) (ht : b ≠ ⊤) (h : a * b = b) : a = 1 := by
  calc a = a * b / b := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ = b / b := by rw [h]
    _ = 1 := ENNReal.div_self h0 ht

theorem ennreal_le_one_of_pow_le {d M : ℝ≥0∞} (hdt : d ≠ ⊤) (hM : M ≠ ⊤)
    (h : ∀ k : ℕ, d ^ k ≤ M) : d ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  lift d to NNReal using hdt
  lift M to NNReal using hM
  have h1 : (1 : NNReal) < d := by exact_mod_cast hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M).exists
  have h2 := h k
  rw [← ENNReal.coe_pow, ENNReal.coe_le_coe] at h2
  exact absurd h2 (not_le.mpr hk)

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_conj (h : G) : Measurable (fun x : G => h * x * h⁻¹) := ((continuous_const.mul continuous_id).mul continuous_const).measurable

theorem conj_comp (g h : G) :
    (fun x : G => g * x * g⁻¹) ∘ (fun x : G => h * x * h⁻¹) = fun x => (g * h) * x * (g * h)⁻¹ := by
  funext x
  simp only [Function.comp_apply, mul_inv_rev]
  group

theorem invOn_map_conj {N : Set G} (hNc : IsClosed N) (h : G)
    (hn1 : ∀ m ∈ N, h * m * h⁻¹ ∈ N) (hn2 : ∀ m ∈ N, h⁻¹ * m * h⁻¹⁻¹ ∈ N)
    {μ : Measure G} (hμ : InvOn μ N) : InvOn (μ.map (fun x => h * x * h⁻¹)) N := by
  obtain ⟨hsf, hne, hc, hinv⟩ := hμ
  haveI := hsf
  have hm : Measurable (fun x : G => h * x * h⁻¹) := measurable_conj h
  have hm' : Measurable (fun x : G => h⁻¹ * x * h⁻¹⁻¹) := measurable_conj h⁻¹
  have hid : (fun x : G => h⁻¹ * x * h⁻¹⁻¹) ∘ (fun x : G => h * x * h⁻¹) = id := by
    rw [conj_comp]
    funext x
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : SigmaFinite ((μ.map (fun x : G => h * x * h⁻¹)).map (fun x : G => h⁻¹ * x * h⁻¹⁻¹)) := by
      rw [Measure.map_map hm' hm, hid, Measure.map_id]
      exact hsf
    exact SigmaFinite.of_map _ hm'.aemeasurable h1
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).mpr hne
  · rw [Measure.map_apply hm hNc.measurableSet.compl]
    refine measure_mono_null ?_ hc
    intro x hx hxN
    exact hx (hn1 x hxN)
  · intro s hs
    have hs' : h⁻¹ * s * h⁻¹⁻¹ ∈ N := hn2 s hs
    have hms : Measurable (fun x : G => s * x) := measurable_const_mul s
    have hms' : Measurable (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := measurable_const_mul _
    rw [Measure.map_map hms hm]
    have e : (fun x : G => s * x) ∘ (fun x : G => h * x * h⁻¹) =
        (fun x : G => h * x * h⁻¹) ∘ (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := by
      funext x
      simp only [Function.comp_apply, inv_inv]
      group
    rw [e, ← Measure.map_map hm hms', hinv _ hs']

end

theorem conjugation_invariant_measure : ConjInv := by
  intro G _ _ _ _ _ _ _ _ N H hN hH hGN hGH hnorm μ hμ hfin hpos h hh
  haveI := hfin
  have hinvH : ∀ g ∈ H, g⁻¹ ∈ H := hGH.2.2
  have hinv : ∀ g ∈ H, InvOn (μ.map (fun x => g * x * g⁻¹)) N := fun g hg =>
    invOn_map_conj hN g (hnorm g hg) (hnorm g⁻¹ (hinvH g hg)) hμ
  have hd : ∀ g ∈ H, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun x => g * x * g⁻¹) = c • μ :=
    fun g hg => haar_measure_uniqueness G N hN hGN _ _ (hinv g hg) hμ
  choose d hd0 hdt hdmap using hd
  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : G)
  have hAi : μ (interior K0) ≠ 0 :=
    hpos _ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.mpr hK0n, hGN.1⟩
  have hK0pos : μ K0 ≠ 0 := fun h0 => hAi (measure_mono_null interior_subset h0)
  have hK0fin : μ K0 ≠ ⊤ := hK0c.measure_lt_top.ne
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  let Bc : Set G := (fun p : G × G × G => p.1 * p.2.1 * p.2.2) '' (H ×ˢ (K0 ×ˢ H))
  have hBc : IsCompact Bc :=
    (hH.prod (hK0c.prod hH)).image (by fun_prop)
  have hBcfin : μ Bc ≠ ⊤ := hBc.measure_lt_top.ne

  have hle : ∀ g (hg : g ∈ H), d g hg ≤ 1 := by
    intro g hg
    have hpowmem : ∀ k : ℕ, g ^ k ∈ H := by
      intro k
      induction k with
      | zero => simpa using hGH.1
      | succ k ih => rw [pow_succ]; exact hGH.2.1 _ ih _ hg
    have hpow : ∀ k : ℕ, μ.map (fun x => g ^ k * x * (g ^ k)⁻¹) = d g hg ^ k • μ := by
      intro k
      induction k with
      | zero => simp [Measure.map_id']
      | succ k ih =>
        have e := conj_comp g (g ^ k)
        rw [← pow_succ'] at e
        rw [← e, ← Measure.map_map (measurable_conj g) (measurable_conj (g ^ k)), ih, Measure.map_smul,
          hdmap g hg, smul_smul, pow_succ]
        exact (measurable_conj g).aemeasurable
    have hbd : ∀ k : ℕ, d g hg ^ k ≤ μ Bc / μ K0 := by
      intro k
      rw [ENNReal.le_div_iff_mul_le (Or.inl hK0pos) (Or.inl hK0fin)]
      have h1 : (μ.map (fun x => g ^ k * x * (g ^ k)⁻¹)) K0 = d g hg ^ k * μ K0 := by
        rw [hpow k]
        rfl
      rw [← h1, Measure.map_apply (measurable_conj _) hK0m]
      apply measure_mono
      intro x hx
      refine ⟨((g ^ k)⁻¹, (g ^ k * x * (g ^ k)⁻¹, g ^ k)), ⟨hinvH _ (hpowmem k), hx, hpowmem k⟩, ?_⟩
      simp only
      group
    exact ennreal_le_one_of_pow_le (hdt g hg) (ENNReal.div_ne_top hBcfin hK0pos) hbd

  have hprod : d h hh * d h⁻¹ (hinvH h hh) = 1 := by
    have e := conj_comp h⁻¹ h
    have e2 : (fun x : G => (h⁻¹ * h) * x * (h⁻¹ * h)⁻¹) = id := by
      funext x
      simp
    rw [e2] at e
    have h1 : μ = (d h⁻¹ (hinvH h hh) * d h hh) • μ := by
      conv_lhs => rw [← Measure.map_id (μ := μ), ← e, ← Measure.map_map (measurable_conj h⁻¹) (measurable_conj h)]
      rw [hdmap h hh, Measure.map_smul, hdmap h⁻¹ (hinvH h hh), smul_smul, mul_comm]
      exact (measurable_conj h⁻¹).aemeasurable
    have h2 := congrArg (fun ν : Measure G => ν K0) h1
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rw [mul_comm]
    exact ennreal_eq_one_of_mul hK0pos hK0fin h2.symm
  have hone : d h hh = 1 := by
    apply le_antisymm (hle h hh)
    calc (1 : ℝ≥0∞) = d h hh * d h⁻¹ (hinvH h hh) := hprod.symm
      _ ≤ d h hh * 1 := mul_le_mul_of_nonneg_left (hle h⁻¹ (hinvH h hh)) (by simp)
      _ = d h hh := mul_one _
  rw [hdmap h hh, hone, one_smul]

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

section Pi

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]

theorem isGrp_pi (K : ∀ v, Set (G v)) (hK : ∀ v, IsGrp (K v)) : IsGrp (Set.pi univ K) := by
  refine ⟨fun v _ => (hK v).1, fun a ha b hb v _ => (hK v).2.1 _ (ha v trivial) _ (hb v trivial),
    fun a ha v _ => (hK v).2.2 _ (ha v trivial)⟩

theorem invOn_pi (K : ∀ v, Set (G v)) (μ : ∀ v, Measure (G v)) (h : ∀ v, InvOn (μ v) (K v)) :
    InvOn (Measure.pi μ) (Set.pi univ K) := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v => (h v).1
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun m : Measure (∀ v, G v) => m univ) h0
    simp only [Measure.pi_univ, Measure.coe_zero, Pi.zero_apply, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] at h1
    obtain ⟨v, hv⟩ := h1
    exact (h v).2.1 (Measure.measure_univ_eq_zero.1 hv)
  · have e : (Set.pi univ K)ᶜ = ⋃ v, (fun x : (∀ v, G v) => x v) ⁻¹' (K v)ᶜ := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact measure_iUnion_null fun v => Measure.pi_eval_preimage_null μ ((h v).2.2.1)
  · intro s hs
    have hmap : ∀ v, (μ v).map (fun x => s v * x) = μ v := fun v => (h v).2.2.2 (s v) (hs v trivial)
    haveI : ∀ v, SigmaFinite ((μ v).map (fun x => s v * x)) := fun v => by
      rw [hmap v]
      infer_instance
    have e : (fun x : (∀ v, G v) => s * x) = fun x v => (fun y => s v * y) (x v) := rfl
    rw [e, Measure.pi_map_pi (fun v => (measurable_const_mul (s v)).aemeasurable)]
    simp only [hmap]

theorem lintegral_pi_prod_mul (μ ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] (φ : ∀ v, G v → ℝ≥0∞) (hφ : ∀ v, Measurable (φ v)) :
    ∫⁻ p, ∏ v, φ v (p.1 v * p.2 v) ∂((Measure.pi μ).prod (Measure.pi ν)) =
      ∏ v, ∫⁻ s, φ v s ∂(mulMap (μ v) (ν v)) := by
  have hm : Measurable (fun p : (∀ v, G v) × (∀ v, G v) => ∏ v, φ v (p.1 v * p.2 v)) :=
    Finset.measurable_prod _ fun v _ => (hφ v).comp
      (((measurable_pi_apply v).comp measurable_fst).mul ((measurable_pi_apply v).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ x : (∀ v, G v), ∫⁻ y, ∏ v, φ v (x v * y v) ∂(Measure.pi ν) =
      ∏ v, ∫⁻ y, φ v (x v * y) ∂(ν v) := fun x =>
    lintegral_fintype_prod (fun v y => φ v (x v * y)) (fun v => (hφ v).comp (measurable_const_mul _))
  simp_rw [hin]
  rw [lintegral_fintype_prod (fun v x => ∫⁻ y, φ v (x * y) ∂(ν v))
    (fun v => ((hφ v).comp measurable_mul).lintegral_prod_right')]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mulMap, lintegral_map (hφ v) measurable_mul,
    lintegral_prod (f := fun z : G v × G v => φ v (z.1 * z.2))
      (show Measurable (fun z : G v × G v => φ v (z.1 * z.2)) from
        (hφ v).comp measurable_mul).aemeasurable]

end Pi

theorem weil_quotient_global_assumptions : GlobAsm := by
  intro hU hL ι _ n ε N H hNc hHc hNg hHg hnorm hunim muN muH nuQ hmuN hmuH hW
  have hloc := fun v => hL (Formalism.REAL.UJ (ε v)) (Formalism.REAL.muG (ε v)) (N v) (H v) (hNc v) (hHc v)
    (hNg v) (hHg v) (hnorm v) (hunim v)
  choose μN μH β hμN hμH hμS hβm hβ1 hLW using hloc
  haveI := fun v => (hμN v).1
  haveI := fun v => (hμH v).1
  haveI := fun v => (hμS v).1
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ N)
    (isClosed_set_pi fun v _ => hNc v) (isGrp_pi N hNg) muN (Measure.pi μN) hmuN
    (invOn_pi N μN hμN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := hU (∀ v, Formalism.REAL.UJ (ε v)) (Set.pi univ H)
    (isClosed_set_pi fun v _ => (hHc v).isClosed) (isGrp_pi H hHg) muH (Measure.pi μH) hmuH
    (invOn_pi H μH hμH)
  refine ⟨fun v => mulMap (μN v) (μH v), fun v => (Formalism.REAL.muG (ε v)).withDensity (β v),
    (cN * cH)⁻¹, ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top hcNt hcHt),
    ENNReal.inv_ne_top.mpr (mul_ne_zero hcN0 hcH0), fun v => ⟨hμS v, hLW v⟩, ?_⟩
  intro F hFm hFinv
  set f : (∀ v, Formalism.REAL.UJ (ε v)) → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := hW f hfm

  have hL1 : ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
      ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v)) := by
    rw [hfdef, lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [lintegral_withDensity_eq_lintegral_mul _ (hβm v) (hFm v)]
    rfl

  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH,
      Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : (∀ v, Formalism.REAL.UJ (ε v)) × (∀ v, Formalism.REAL.UJ (ε v)),
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v)) (fun v => ((hβm v).comp (measurable_mul_const _)).mul
      ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(mulMap (μN v) (μH v)), s ∈ prodSet (N v) (H v) :=
        mem_ae_iff.mpr (hμS v).2.2.1
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : (∀ v, Formalism.REAL.UJ (ε v)) => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  change _ = (cN * cH)⁻¹ * ∏ v, ∫⁻ y, F v y ∂((Formalism.REAL.muG (ε v)).withDensity (β v))
  rw [key, ← mul_assoc, ENNReal.inv_mul_cancel (mul_ne_zero hcN0 hcH0)
    (ENNReal.mul_ne_top hcNt hcHt), one_mul]

end QPK
end
end

