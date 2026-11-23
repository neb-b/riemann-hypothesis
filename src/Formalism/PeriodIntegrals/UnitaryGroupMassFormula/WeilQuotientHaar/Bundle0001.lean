module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.BruhatDecomposition
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

namespace Bru

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_cover :
    ∃ K : ℕ → Set G, (∀ n, IsCompact (K n)) ∧ ∀ x, ∃ n, x ∈ interior (K n) := by
  let K := CompactExhaustion.choice G
  refine ⟨K, fun n => K.isCompact n, fun x => ?_⟩
  obtain ⟨n, hn⟩ := K.exists_mem x
  exact ⟨n + 1, K.subset_interior_succ n hn⟩

def gf (μ : Measure G) (K : ℕ → Set G) (n : ℕ) (x : G) : ℝ≥0∞ :=
  μ ((fun s => s * x) ⁻¹' K n)

def Eset (μ : Measure G) (K : ℕ → Set G) (n : ℕ) : Set G :=
  {x | gf μ K n x ≠ 0 ∧ ∀ k < n, gf μ K k x = 0}

def bf (μ : Measure G) (K : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  ∑' n, (Eset μ K n).indicator (fun y => (K n).indicator 1 y * (gf μ K n y)⁻¹) x

theorem gf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (n : ℕ) :
    Measurable (gf μ K n) := by
  have hs : MeasurableSet ((fun p : G × G => p.2 * p.1) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_snd.mul measurable_fst)
  first
  | exact measurable_measure_prodMk_left hs
  | exact measurable_measure_prod_mk_left hs

theorem gf_lt_top (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : ℕ → Set G)
    (hK : ∀ n, IsCompact (K n)) (n : ℕ) (x : G) : gf μ K n x < ⊤ := by
  have h : IsCompact ((fun s => s * x) ⁻¹' K n) :=
    (Homeomorph.mulRight x).isCompact_preimage.2 (hK n)
  exact h.measure_lt_top

theorem gf_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    gf μ K n (t * x) = gf μ K n x := by
  have hm : MeasurableSet ((fun s => s * x) ⁻¹' K n) :=
    (hK n).measurableSet.preimage (measurable_mul_const x)
  show μ ((fun s => s * (t * x)) ⁻¹' K n) = μ ((fun s => s * x) ⁻¹' K n)
  calc μ ((fun s => s * (t * x)) ⁻¹' K n)
      = μ.map (fun s => s * t) ((fun s => s * x) ⁻¹' K n) := by
        rw [Measure.map_apply (measurable_mul_const t) hm]
        congr 1
        ext s
        simp [mul_assoc]
    _ = μ ((fun s => s * x) ⁻¹' K n) := by rw [hr t ht]

theorem gf_pos (μ : Measure G) (K : ℕ → Set G) (S : Set G) (h1 : (1 : G) ∈ S)
    (hpos : PosOn μ S) (n : ℕ) {x : G} (hx : x ∈ interior (K n)) : gf μ K n x ≠ 0 := by
  intro h0
  have hU : IsOpen ((fun s => s * x) ⁻¹' interior (K n)) :=
    isOpen_interior.preimage (continuous_mul_const x)
  have hne := hpos _ hU ⟨1, by simpa using hx, h1⟩
  exact hne (measure_mono_null (Set.preimage_mono interior_subset) h0)

theorem Eset_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n))
    (n : ℕ) : MeasurableSet (Eset μ K n) := by
  have h1 : MeasurableSet {x | gf μ K n x ≠ 0} :=
    (gf_meas μ K hK n) (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {x | ∀ k < n, gf μ K k x = 0} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (gf_meas μ K hK k) (measurableSet_singleton 0)
  exact h1.inter h2

theorem Eset_unique {μ : Measure G} {K : ℕ → Set G} {x : G} {n m : ℕ}
    (hn : x ∈ Eset μ K n) (hm : x ∈ Eset μ K m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd (hm.2 n h) hn.1
  · exact h
  · exact absurd (hn.2 m h) hm.1

theorem Eset_exists (μ : Measure G) (K : ℕ → Set G) (x : G) (h : ∃ n, gf μ K n x ≠ 0) :
    ∃ n, x ∈ Eset μ K n := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun k hk => ?_⟩
  by_contra hc
  exact Nat.find_min h hk hc

theorem Eset_inv (μ : Measure G) (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) (S : Set G)
    (hr : ∀ s ∈ S, μ.map (fun x => x * s) = μ) (n : ℕ) {t : G} (ht : t ∈ S) (x : G) :
    t * x ∈ Eset μ K n ↔ x ∈ Eset μ K n := by
  have h : ∀ k, gf μ K k (t * x) = gf μ K k x := fun k => gf_inv μ K hK S hr k ht x
  simp only [Eset, Set.mem_setOf_eq, h]

theorem bf_meas (μ : Measure G) [SFinite μ] (K : ℕ → Set G) (hK : ∀ n, IsClosed (K n)) :
    Measurable (bf μ K) := by
  unfold bf
  refine Measurable.tsum fun n => ?_
  refine Measurable.indicator ?_ (Eset_meas μ K hK n)
  exact (measurable_one.indicator (hK n).measurableSet).mul (gf_meas μ K hK n).inv

end Bru

open Bru in
theorem bruhat_decomposition' : Bruhat := by
  intro G _ _ _ _ _ _ _ _ S hS hG μ hinv hfin hpos hr
  obtain ⟨hsf, -, hSc, -⟩ := hinv
  haveI := hsf
  haveI := hfin
  obtain ⟨K, hKc, hKx⟩ := exists_cover (G := G)
  have hKcl : ∀ n, IsClosed (K n) := fun n => (hKc n).isClosed
  refine ⟨bf μ K, bf_meas μ K hKcl, fun x => ?_⟩
  obtain ⟨m, hm⟩ := hKx x
  obtain ⟨n, hn⟩ := Eset_exists μ K x ⟨m, gf_pos μ K S hG.1 hpos m hm⟩
  have hS' : ∀ᵐ s ∂μ, s ∈ S := ae_iff.2 hSc
  have hae : ∀ᵐ s ∂μ, bf μ K (s * x) = (K n).indicator 1 (s * x) * (gf μ K n x)⁻¹ := by
    filter_upwards [hS'] with s hs
    unfold bf
    rw [tsum_eq_single n]
    · rw [Set.indicator_of_mem ((Eset_inv μ K hKcl S hr n hs x).2 hn)]
      simp only [gf_inv μ K hKcl S hr n hs x]
    · intro k hk
      have hk' : s * x ∉ Eset μ K k := fun hk' =>
        hk (Eset_unique ((Eset_inv μ K hKcl S hr k hs x).1 hk') hn)
      first
      | exact Set.indicator_of_notMem hk' _
      | exact Set.indicator_of_not_mem hk' _
  have hmeas : Measurable fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x) :=
    (measurable_one.indicator (hKcl n).measurableSet).comp (measurable_mul_const x)
  have e1 : (fun s => (K n).indicator (1 : G → ℝ≥0∞) (s * x)) =
      ((fun s => s * x) ⁻¹' K n).indicator 1 := by
    ext s
    first
    | rfl
    | simp [Set.indicator_apply]
  rw [lintegral_congr_ae hae, lintegral_mul_const _ hmeas, e1,
    lintegral_indicator_one ((hKcl n).measurableSet.preimage (measurable_mul_const x))]
  exact ENNReal.mul_inv_cancel hn.1 (gf_lt_top μ K hKc n x).ne

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness
section
noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace QPK

def toSub {G : Type} [Group G] (K : Set G) (hK : IsGrp K) : Subgroup G where
  carrier := K
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2 _ ha

section Sub

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

lemma map_val_mul (K' : Subgroup G) (g : K') (α : Measure K') :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  have hv : Measurable (Subtype.val : K' → G) := measurable_subtype_coe
  have hm : Measurable (fun x : K' => g * x) := by
    have h : Measurable (fun x : K' => (g : G) * (x : G)) := (measurable_const_mul (g : G)).comp hv
    exact h.subtype_mk
  rw [Measure.map_map hv hm, Measure.map_map (measurable_const_mul _) hv]
  rfl

end Sub

theorem haar_measure_existence : HaarExist := by
  intro G _ _ _ _ _ _ _ _ K hKc hK
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H → G) := hHc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  have hv : Measurable (Subtype.val : H → G) := measurable_subtype_coe
  let α : Measure H := Measure.haar
  have hfin : IsFiniteMeasureOnCompacts (α.map Subtype.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hv hC.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hC).measure_lt_top
  refine ⟨α.map Subtype.val, ⟨?_, ?_, ?_, ?_⟩, hfin, ?_⟩
  · infer_instance
  · intro h
    rw [Measure.map_eq_zero_iff hv.aemeasurable] at h
    exact (Measure.measure_univ_pos.mp (isOpen_univ.measure_pos α Set.univ_nonempty)) h
  · rw [Measure.map_apply hv hKc.measurableSet.compl]
    have h : (Subtype.val : H → G) ⁻¹' Kᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [h, measure_empty]
  · intro s hs
    have h := map_val_mul H ⟨s, hs⟩ α
    rw [map_mul_left_eq_self] at h
    exact h.symm
  · intro U hU ⟨x, hxU, hxK⟩
    rw [Measure.map_apply hv hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_ne_zero α ⟨⟨x, hxK⟩, hxU⟩

theorem haar_measure_uniqueness : HaarUniq := by
  intro G _ _ _ _ _ _ _ _ K hKc hK μ ν hμ hν
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hKc.measurableSet
  let K₀ : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have key : ∀ ρ : Measure G, InvOn ρ K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
    intro ρ ⟨hσ, h0, hc, hinv⟩
    let ρ' : Measure H := ρ.comap Subtype.val
    have hback : ρ'.map Subtype.val = ρ := by
      rw [hme.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    haveI : SigmaFinite ρ' :=
      SigmaFinite.of_map ρ' hme.measurable.aemeasurable (by rw [hback]; exact hσ)
    haveI : IsMulLeftInvariant ρ' := by
      refine ⟨fun g => ?_⟩
      calc ρ'.map (g * ·) = ((ρ'.map (g * ·)).map Subtype.val).comap Subtype.val :=
            (hme.comap_map _).symm
        _ = ((ρ'.map Subtype.val).map ((g : G) * ·)).comap Subtype.val := by rw [map_val_mul]
        _ = ρ' := by rw [hback, hinv (g : G) g.2]
    obtain ⟨c, hK0⟩ : ∃ c : ℝ≥0∞, ρ' = c • Measure.haarMeasure K₀ :=
      ⟨_, Measure.haarMeasure_unique ρ' K₀⟩
    have hρ : ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
      rw [← hback, hK0, Measure.map_smul c hme.measurable.aemeasurable]
    refine ⟨c, ?_, ?_, hρ⟩
    · intro hz
      apply h0
      rw [hρ, hz, zero_smul]
    · intro htop
      have hne : Measure.haarMeasure K₀ (⋃ n, spanningSets ρ' n) ≠ 0 := by
        rw [iUnion_spanningSets]
        exact (lt_of_lt_of_le zero_lt_one
          ((Measure.haarMeasure_self (K₀ := K₀)).symm.le.trans (measure_mono (Set.subset_univ _)))).ne'
      obtain ⟨n, hn⟩ : ∃ n, Measure.haarMeasure K₀ (spanningSets ρ' n) ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne (measure_iUnion_null_iff.2 hall)
      have h2 : ρ' (spanningSets ρ' n) = (c • Measure.haarMeasure K₀) (spanningSets ρ' n) :=
        congrArg (fun m : Measure H => m (spanningSets ρ' n)) hK0
      have h3 := measure_spanningSets_lt_top ρ' n
      rw [h2, Measure.smul_apply, htop, smul_eq_mul, ENNReal.top_mul hn] at h3
      exact lt_irrefl _ h3
  obtain ⟨a, ha0, hat, hμ'⟩ := key μ hμ
  obtain ⟨b, hb0, hbt, hν'⟩ := key ν hν
  refine ⟨a / b, (ENNReal.div_pos ha0 hbt).ne', ENNReal.div_ne_top hat hb0, ?_⟩
  rw [hμ', hν', smul_smul, ENNReal.div_mul_cancel hb0 hbt]

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK


theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LocalWeilRepresentation
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QPK

theorem local_weil_representation : LocWeil := by
  intro G _ _ _ _ _ _ _ _ muG _ μ _ hinv β hβ hβ1 F hF
  have hFm : Measurable (fun p : G × G => F (p.1 * p.2)) := hF.comp measurable_mul
  have hin : Measurable (fun x => ∫⁻ s, F (s * x) ∂μ) := hFm.lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβ hin]
  simp only [Pi.mul_apply]
  have step1 : ∀ x, β x * ∫⁻ s, F (s * x) ∂μ = ∫⁻ s, β x * F (s * x) ∂μ := fun x =>
    (lintegral_const_mul (β x) (hF.comp (measurable_id.mul_const x))).symm
  simp_rw [step1]
  rw [lintegral_lintegral_swap (μ := muG) (ν := μ) (f := fun x s => β x * F (s * x))
    ((hβ.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))).aemeasurable]
  have step2 : ∀ s, ∫⁻ x, β x * F (s * x) ∂muG = ∫⁻ x, β (s⁻¹ * x) * F x ∂muG := by
    intro s
    have key := lintegral_mul_left_eq_self (μ := muG) (fun x => β (s⁻¹ * x) * F x) s
    simp only [inv_mul_cancel_left] at key
    exact key
  simp_rw [step2]
  rw [lintegral_lintegral_swap (μ := μ) (ν := muG) (f := fun s x => β (s⁻¹ * x) * F x)
    ((hβ.comp (measurable_fst.inv.mul measurable_snd)).mul (hF.comp measurable_snd)).aemeasurable]
  have step3 : ∀ x, ∫⁻ s, β (s⁻¹ * x) * F x ∂μ = F x := by
    intro x
    rw [lintegral_mul_const (F x) (f := fun s => β (s⁻¹ * x)) (hβ.comp (measurable_inv.mul_const x))]
    have hsym : ∫⁻ s, β (s⁻¹ * x) ∂μ = ∫⁻ s, β (s * x) ∂μ := by
      conv_rhs => rw [← hinv]
      rw [lintegral_map (f := fun s => β (s * x)) (hβ.comp (measurable_id.mul_const x)) measurable_inv]
    rw [hsym, hβ1 x, one_mul]
  simp_rw [step3]

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.ProdSetIsClosed
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace QPK

section
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

theorem prodSet_eq_mul (N H : Set G) : prodSet N H = N * H := by
  ext s
  simp only [prodSet, Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩

theorem prodSet_isClosed {N H : Set G} (hN : IsClosed N) (hH : IsCompact H) :
    IsClosed (prodSet N H) := by
  rw [prodSet_eq_mul]
  first
    | exact hN.mul_isCompact hH
    | exact IsClosed.mul_isCompact hN hH
    | exact hN.mul_right_of_isCompact hH
    | exact IsClosed.mul_right_of_isCompact hN hH
    | exact hN.mul_isCompact_right hH
    | exact (hN.smul_left_of_isCompact hH)

theorem prodSet_isGrp {N H : Set G} (hN : IsGrp N) (hH : IsGrp H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ N, h * m * h⁻¹ ∈ N) : IsGrp (prodSet N H) := by
  obtain ⟨n1, nmul, ninv⟩ := hN
  obtain ⟨h1, hmul, hinv⟩ := hH
  refine ⟨⟨1, n1, 1, h1, (mul_one 1).symm⟩, ?_, ?_⟩
  · rintro _ ⟨m, hm, h, hh, rfl⟩ _ ⟨m', hm', h', hh', rfl⟩
    refine ⟨m * (h * m' * h⁻¹), nmul _ hm _ (hnorm h hh m' hm'), h * h', hmul _ hh _ hh', ?_⟩
    first
      | group
      | simp [mul_assoc]
  · rintro _ ⟨m, hm, h, hh, rfl⟩
    refine ⟨h⁻¹ * m⁻¹ * h⁻¹⁻¹, hnorm _ (hinv _ hh) _ (ninv _ hm), h⁻¹, hinv _ hh, ?_⟩
    first
      | group
      | simp [mul_assoc]
end

theorem locPack_of (hE : HaarExist) (hC : ConjInv) (hS : SMeas) (hB : Bruhat) (hW : LocWeil) :
    LocPack := by
  intro G _ _ _ _ _ _ _ _ muG _ N H hN hH gN gH hnorm hR
  obtain ⟨μN, hNinv, hNf, hNpos⟩ := hE G N hN gN
  obtain ⟨μH, hHinv, hHf, hHpos⟩ := hE G H hH.isClosed gH
  have hconj := hC G N H hN hH gN gH hnorm μN hNinv hNf hNpos
  obtain ⟨hPinv, hPf, hPpos, hPright, hPinvol⟩ :=
    hS G N H hN hH gN gH hnorm hR μN μH hNinv hNf hNpos hHinv hHf hHpos hconj
  obtain ⟨β, hβm, hβ⟩ := hB G (prodSet N H) (prodSet_isClosed hN hH) (prodSet_isGrp gN gH hnorm)
    (mulMap μN μH) hPinv hPf hPpos hPright
  refine ⟨μN, μH, β, hNinv, hHinv, hPinv, hβm, hβ, ?_⟩
  intro F hF
  haveI := hPf
  have hsf : SigmaFinite (mulMap μN μH) := by
    first
      | exact inferInstance
      | exact MeasureTheory.sigmaFinite_of_isFiniteMeasureOnCompacts _
  exact hW G muG (mulMap μN μH) hsf hPinvol β hβm hβ F hF

end QPK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.QuotProdKOf
section
namespace QPK

theorem quotProdK_of (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK :=
  hA hU hL

end QPK
end

