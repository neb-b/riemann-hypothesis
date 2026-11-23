module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.MeasurableLift
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace Pointwise

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] [MeasurableSpace S] (j : Λ →* S) (B : Subgroup Λ)
  (μ : Measure S) (DB : Set S)

abbrev Qt := Quotient (MulAction.orbitRel (B.map j) S)

def pr : S → Qt j B := Quotient.mk _

def nu : Measure (Qt j B) := (μ.restrict DB).map (pr j B)

abbrev HL := Lp ℝ 2 (nu j B μ DB)

def lift (u : S → ℝ) : Qt j B → ℝ := fun q => u q.out

def Good (u : S → ℝ) : Prop := Measurable u ∧ LInv j B u ∧ MemLp u 2 (μ.restrict DB)

variable {j B μ DB}

theorem linv_rel {u : S → ℝ} (hu : LInv j B u) {x y : S} (h : MulAction.orbitRel (B.map j) S x y) :
    u x = u y := by
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨⟨g, hg⟩, rfl⟩ := h
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  exact hu γ hγ y

theorem measurable_pr : Measurable (pr j B) := by
  exact measurable_quotient_mk''

theorem pr_mul {γ : Λ} (hγ : γ ∈ B) (x : S) : pr j B (j γ * x) = pr j B x := by
  unfold pr
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨⟨j γ, Subgroup.mem_map_of_mem j hγ⟩, rfl⟩

theorem lift_pr {u : S → ℝ} (hu : LInv j B u) (x : S) : lift j B u (pr j B x) = u x := by
  exact linv_rel hu (Quotient.mk_out' x)

theorem measurable_lift {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) : Measurable (lift j B u) := by
  refine measurable_from_quotient.mpr ?_
  have : (lift j B u ∘ Quotient.mk'') = u := funext fun x => lift_pr hu x
  rw [this]; exact hm

theorem memLp_lift {u : S → ℝ} (h : Good j B μ DB u) : MemLp (lift j B u) 2 (nu j B μ DB) := by
  obtain ⟨hm, hi, hmem⟩ := h
  unfold nu
  rw [memLp_map_measure_iff (measurable_lift hm hi).aestronglyMeasurable measurable_pr.aemeasurable]
  have : (lift j B u ∘ pr j B) = u := funext fun x => lift_pr hi x
  rw [this]; exact hmem


variable (j B μ DB) in
def cls (u : S → ℝ) : HL j B μ DB := by
  classical exact if h : Good j B μ DB u then (memLp_lift h).toLp (lift j B u) else 0

theorem good_iff {u : S → ℝ} (hm : Measurable u) (hu : LInv j B u) :
    Good j B μ DB u ↔ IntegrableOn (fun x => u x ^ 2) DB μ := by
  unfold Good
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨fun h => h.2.2, fun h => ⟨hm, hu, h⟩⟩

theorem good_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    Good j B μ DB (fun x => u x - v x) := by
  refine ⟨hu.1.sub hv.1, fun γ hγ x => ?_, hu.2.2.sub hv.2.2⟩
  show u (j γ * x) - v (j γ * x) = u x - v x
  rw [hu.2.1 γ hγ x, hv.2.1 γ hγ x]

theorem cls_sub {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB (fun x => u x - v x) = cls j B μ DB u - cls j B μ DB v := by
  unfold cls
  rw [dite_eq_left (good_sub hu hv), dite_eq_left hu, dite_eq_left hv]
  exact MemLp.toLp_sub (memLp_lift hu) (memLp_lift hv)

theorem cls_inner {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    ⟪cls j B μ DB u, cls j B μ DB v⟫_ℝ = ∫ x in DB, u x * v x ∂μ := by
  unfold cls
  rw [dite_eq_left hu, dite_eq_left hv, L2.inner_def]
  have h1 := (memLp_lift hu).coeFn_toLp
  have h2 := (memLp_lift hv).coeFn_toLp
  have hcongr : (fun q => ⟪((memLp_lift hu).toLp (lift j B u) : Qt j B → ℝ) q,
      ((memLp_lift hv).toLp (lift j B v) : Qt j B → ℝ) q⟫_ℝ) =ᵐ[nu j B μ DB]
      fun q => lift j B u q * lift j B v q := by
    filter_upwards [h1, h2] with q hq1 hq2
    rw [hq1, hq2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae hcongr]
  have hm : Measurable (fun q => lift j B u q * lift j B v q) :=
    (measurable_lift hu.1 hu.2.1).mul (measurable_lift hv.1 hv.2.1)
  unfold nu
  rw [integral_map measurable_pr.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem cls_norm_sq {u : S → ℝ} (hu : Good j B μ DB u) :
    ‖cls j B μ DB u‖ ^ 2 = ∫ x in DB, u x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, cls_inner hu hu]
  simp only [sq]

theorem cls_surj (f : HL j B μ DB) : ∃ u, Good j B μ DB u ∧ cls j B μ DB u = f := by
  have hf := (Lp.aestronglyMeasurable f).aemeasurable
  set g := hf.mk f with hgdef
  have hg : Measurable g := hf.measurable_mk
  have hfg : (f : Qt j B → ℝ) =ᵐ[nu j B μ DB] g := hf.ae_eq_mk
  have hinv : LInv j B (g ∘ pr j B) := fun γ hγ x => by
    show g (pr j B (j γ * x)) = g (pr j B x)
    rw [pr_mul hγ x]
  have hLg : MemLp g 2 (nu j B μ DB) := (Lp.memLp f).ae_eq hfg
  have hgood : Good j B μ DB (g ∘ pr j B) := by
    refine ⟨hg.comp measurable_pr, hinv, ?_⟩
    unfold nu at hLg
    exact (memLp_map_measure_iff hg.aestronglyMeasurable measurable_pr.aemeasurable).1 hLg
  refine ⟨g ∘ pr j B, hgood, ?_⟩
  have hl : lift j B (g ∘ pr j B) = g := funext fun q => by
    show g (Quotient.mk _ q.out) = g q
    rw [Quotient.out_eq]
  unfold cls
  rw [dite_eq_left hgood]
  apply Lp.ext
  filter_upwards [(memLp_lift hgood).coeFn_toLp, hfg] with q h1 h2
  rw [h1, hl, h2]

theorem cls_eq_iff {u v : S → ℝ} (hu : Good j B μ DB u) (hv : Good j B μ DB v) :
    cls j B μ DB u = cls j B μ DB v ↔ u =ᵐ[μ.restrict DB] v := by
  unfold cls; rw [dite_eq_left hu, dite_eq_left hv, MemLp.toLp_eq_toLp_iff]
  unfold nu Filter.EventuallyEq
  rw [ae_map_iff measurable_pr.aemeasurable
    (measurableSet_eq_fun (measurable_lift hu.1 hu.2.1) (measurable_lift hv.1 hv.2.1))]
  simp only [lift_pr hu.2.1, lift_pr hv.2.1]

theorem countable_map [Countable Λ] : Countable (B.map j) := by
  have hc : ((B.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact hc.to_subtype

theorem ae_spread [Countable Λ] [MeasurableMul S] [μ.IsMulLeftInvariant]
    (hD : IsFundamentalDomain (B.map j) DB μ) {u v : S → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hiu : LInv j B u) (hiv : LInv j B v) (h : u =ᵐ[μ.restrict DB] v) : u =ᵐ[μ] v := by
  haveI := countable_map (j := j) (B := B)
  have inv : ∀ w : S → ℝ, LInv j B w → ∀ (g : B.map j) (x : S), w (g • x) = w x :=
    fun w hw g x => linv_rel hw (by rw [MulAction.orbitRel_apply]; exact MulAction.mem_orbit x g)
  have htm : MeasurableSet {x | u x ≠ v x} := (measurableSet_eq_fun hu hv).compl
  have ht : ∀ g : B.map j, g • {x | u x ≠ v x} = {x | u x ≠ v x} := by
    intro g
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq]
    rw [inv u hiu g⁻¹ x, inv v hiv g⁻¹ x]
  have hts : μ ({x | u x ≠ v x} ∩ DB) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h
  exact ae_iff.2 (hD.measure_zero_of_invariant _ ht hts)

theorem ae_translate [MeasurableMul S] [μ.IsMulLeftInvariant] {u v : S → ℝ} (g : S)
    (h : u =ᵐ[μ] v) : (fun x => u (g * x)) =ᵐ[μ] fun x => v (g * x) := by
  exact (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae_eq h

end PositivityTheory.KB.SpectralGap.PGap

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PAEConst
section
open MeasureTheory Filter Set
open scoped symmDiff Topology ENNReal

namespace PositivityTheory.KB.SpectralGap

namespace AlmostEverywhereConstant

variable {S : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) [μ.IsHaarMeasure]

def tr (g : S) : C(S, S) := ⟨(g * ·), continuous_const_mul g⟩

theorem coe_tr (g : S) : ⇑(tr g) = (g * ·) := rfl

theorem continuous_tr : Continuous (tr : S → C(S, S)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_mul

theorem tendsto_pre {x : ℕ → S} {g : S} (hx : Tendsto x atTop (𝓝 g)) {P : Set S}
    (hP : MeasurableSet P) (hμP : μ P ≠ ∞) :
    Tendsto (fun n => μ (((x n * ·) ⁻¹' P) ∆ ((g * ·) ⁻¹' P))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => tr (x n)) atTop (𝓝 (tr g)) := (continuous_tr.tendsto g).comp hx
  have key := tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) hc
    (Eventually.of_forall fun n => measurePreserving_mul_left μ (x n))
    (measurePreserving_mul_left μ g) hP.nullMeasurableSet hμP
  simpa only [coe_tr] using key

theorem isClosed_stab {T : Set S} (hT : MeasurableSet T) :
    IsClosed {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} := by
  apply isClosed_of_closure_subset
  intro g hg
  obtain ⟨x, hxS, hx⟩ := mem_closure_iff_seq_limit.1 hg
  show (g * ·) ⁻¹' T =ᵐ[μ] T
  rw [← measure_symmDiff_eq_zero_iff]
  have key : ∀ K : Set S, IsCompact K → μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K) = 0 := by
    intro K hK
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds g
    set L : Set S := (fun p : S × S => p.1 * p.2) '' (N ×ˢ K) with hLdef
    have hLc : IsCompact L := (hNc.prod hK).image continuous_mul
    have hPm : MeasurableSet (T ∩ L) := hT.inter hLc.measurableSet
    have hPf : μ (T ∩ L) ≠ ∞ :=
      ((measure_mono inter_subset_right).trans_lt hLc.measure_lt_top).ne
    have ev : ∀ᶠ n in atTop, x n ∈ N := hx hN
    have tend := tendsto_pre μ hx hPm hPf
    refine le_antisymm ?_ bot_le
    apply ge_of_tendsto tend
    filter_upwards [ev] with n hn
    have h0 : μ (((x n * ·) ⁻¹' T) ∆ T) = 0 := measure_symmDiff_eq_zero_iff.2 (hxS n)
    have hsub : (((g * ·) ⁻¹' T) ∆ T) ∩ K ⊆
        (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T) := by
      rintro y ⟨hyD, hyK⟩
      have h1 : x n * y ∈ L := ⟨(x n, y), ⟨hn, hyK⟩, rfl⟩
      have h2 : g * y ∈ L := ⟨(g, y), ⟨mem_of_mem_nhds hN, hyK⟩, rfl⟩
      simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage, Set.mem_inter_iff, h1, h2,
        and_true] at hyD ⊢
      tauto
    calc μ ((((g * ·) ⁻¹' T) ∆ T) ∩ K)
        ≤ μ ((((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) ∪ (((x n * ·) ⁻¹' T) ∆ T)) :=
          measure_mono hsub
      _ ≤ μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) + μ (((x n * ·) ⁻¹' T) ∆ T) :=
          measure_union_le _ _
      _ = μ (((x n * ·) ⁻¹' (T ∩ L)) ∆ ((g * ·) ⁻¹' (T ∩ L))) := by rw [h0, add_zero]
  have hD : ((g * ·) ⁻¹' T) ∆ T = ⋃ n, ((((g * ·) ⁻¹' T) ∆ T) ∩ compactCovering S n) := by
    rw [← inter_iUnion, iUnion_compactCovering, inter_univ]
  rw [hD]
  exact measure_iUnion_null fun n => key _ (isCompact_compactCovering S n)

theorem aeconst_set {A : Subgroup S} (hA : Dense (A : Set S)) {T : Set S} (hT : MeasurableSet T)
    (h : ∀ g ∈ A, (g * ·) ⁻¹' T =ᵐ[μ] T) : EventuallyEmptyOrUniv T (ae μ) := by
  have hcl : closure (A : Set S) ⊆ {g : S | (g * ·) ⁻¹' T =ᵐ[μ] T} :=
    closure_minimal (fun g hg => h g hg) (isClosed_stab μ hT)
  rw [hA.closure_eq] at hcl
  exact aeconst_of_forall_preimage_smul_ae_eq S hT.nullMeasurableSet fun g => hcl (mem_univ g)

end AlmostEverywhereConstant

theorem aeConst_holds : AEConst := by
  intro S _ _ _ _ _ _ _ _ μ _ A hA u hu hinv
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet ?_
  intro U hU
  have hT : MeasurableSet (u ⁻¹' U) := hu hU
  have key := AlmostEverywhereConstant.aeconst_set μ hA hT fun g hg => by
    filter_upwards [hinv g hg] with x hx
    show u (g * x) ∈ U ↔ u x ∈ U
    rw [hx]
  exact eventuallyEmptyOrUniv_iff.1 key

end PositivityTheory.KB.SpectralGap
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAvg
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S)

theorem linv_mono {E E' : Subgroup Λ} (h : E ≤ E') {u : S → ℝ} (hu : LInv j E' u) : LInv j E u :=
  fun γ hγ x => hu γ (h hγ) x

theorem linv_sub {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x - v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_mul {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x * v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

theorem linv_sq {E : Subgroup Λ} {u : S → ℝ} (hu : LInv j E u) : LInv j E (fun x => u x ^ 2) := by
  intro γ hγ x
  simp only [hu γ hγ x]

variable {B K : Subgroup Λ}

theorem card_cosets :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem finite_cosets (h : (B.subgroupOf K).index ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
  Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)

theorem avg_sub (h : (B.subgroupOf K).index ≠ 0) (u v : S → ℝ) (x : S) :
    avg j B K (fun y => u y - v y) x = avg j B K u x - avg j B K v x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

theorem avg_mul_left {a : S → ℝ} (ha : LInv j K a) (b : S → ℝ) (x : S) :
    avg j B K (fun y => a y * b y) x = a x * avg j B K b x := by
  by_cases h : (B.subgroupOf K).index = 0
  · simp [avg, h]
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype]
  have hc : ∀ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)),
      a (j (c.out : Λ) * x) * b (j (c.out : Λ) * x) = a x * b (j (c.out : Λ) * x) := by
    intro c
    rw [ha _ c.out.2 x]
  simp only [hc, ← Finset.mul_sum]
  ring

theorem avg_nonneg {u : S → ℝ} (hu : ∀ y, 0 ≤ u y) (x : S) : 0 ≤ avg j B K u x := by
  unfold avg
  apply mul_nonneg
  · positivity
  · exact finsum_nonneg fun c => hu _

theorem avg_sq_le (h : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (x : S) :
    avg j B K u x ^ 2 ≤ avg j B K (fun y => u y ^ 2) x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hc : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_cosets]
  have hn : (0 : ℝ) < (B.subgroupOf K).index := by exact_mod_cast Nat.pos_of_ne_zero h
  simp only [avg, finsum_eq_sum_of_fintype]
  have key := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) => u (j (c.out : Λ) * x))
  rw [hc] at key
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn_def
  set s := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x)
  set t := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x) ^ 2
  calc (n⁻¹ * s) ^ 2 = n⁻¹ ^ 2 * s ^ 2 := by ring
    _ ≤ n⁻¹ ^ 2 * (n * t) := by gcongr
    _ = n⁻¹ * t := by
      field_simp

end PositivityTheory.KB.SpectralGap.PGap

end
end

