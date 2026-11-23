module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PUnfoldA
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.UnfoldA

open PositivityTheory.KB.SpectralGap

variable {Λ S : Type} [Group Λ] [Group S]

abbrev RQ (B K : Subgroup Λ) := Quotient (QuotientGroup.rightRel (B.subgroupOf K))

theorem card_Q (B K : Subgroup Λ) : Nat.card (RQ B K) = (B.subgroupOf K).index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)

theorem finite_Q (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) : Finite (RQ B K) := by
  have h : Nat.card (RQ B K) ≠ 0 := by rw [card_Q]; exact hi
  exact (Nat.card_ne_zero.mp h).2

theorem avg_eq_sum (j : Λ →* S) (B K : Subgroup Λ) [Fintype (RQ B K)] (u : S → ℝ) (x : S) :
    avg j B K u x = ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := by
  rw [avg, finsum_eq_sum_of_fintype]

theorem mk_eq_iff {B K : Subgroup Λ} (a b : K) :
    Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) a = Quotient.mk _ b ↔
      (b : Λ) * (a : Λ)⁻¹ ∈ B := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply.trans (by rw [Subgroup.mem_subgroupOf]; simp)

theorem out_mk {B K : Subgroup Λ} (k : K) :
    (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * (k : Λ)⁻¹ ∈ B := by
  have h : Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K))
      (Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out = Quotient.mk _ k :=
    Quotient.out_eq _
  rw [mk_eq_iff] at h
  simpa [mul_inv_rev] using B.inv_mem h

theorem linv_out {j : Λ →* S} {B K : Subgroup Λ} {u : S → ℝ} (hu : LInv j B u) (k : K) (x : S) :
    u (j (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * x) =
      u (j (k : Λ) * x) := by
  have h := out_mk (B := B) k
  set o : Λ := (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ)
  calc u (j o * x) = u (j (o * (k : Λ)⁻¹) * (j (k : Λ) * x)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
    _ = u (j (k : Λ) * x) := hu _ h _

theorem avg_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j B u) : LInv j K (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  intro γ hγ x
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let g : K := ⟨γ, hγ⟩
  let e : RQ B K ≃ RQ B K := Quotient.congr (Equiv.mulRight g) (fun a b => by
    simp only [Equiv.coe_mulRight]
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
      show b * g * (a * g)⁻¹ = b * a⁻¹ by group])
  refine Fintype.sum_equiv e _ _ (fun c => ?_)
  have hc : e c = Quotient.mk _ (c.out * g) := by
    conv_lhs => rw [← Quotient.out_eq c]
    exact Quotient.congr_mk _ _ _
  rw [hc, linv_out hu, Subgroup.coe_mul, map_mul, mul_assoc]

theorem avg_of_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j K u) : avg j B K u = u := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  funext x
  rw [avg_eq_sum]
  have h : ∀ c : RQ B K, u (j ((c.out : K) : Λ) * x) = u x := fun c => hu _ (c.out : K).2 x
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_Q]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hi) _

theorem avg_meas [MeasurableSpace S] [MeasurableMul S] (j : Λ →* S) (B K : Subgroup Λ)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : Measurable u) :
    Measurable (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  have h : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := funext (avg_eq_sum j B K u)
  rw [h]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun c _ => hu.comp (measurable_const_mul _))

theorem avg_tower (j : Λ →* S) (B E K : Subgroup Λ) (hBE : B ≤ E) (hEK : E ≤ K)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : LInv j B u) :
    avg j E K (avg j B E u) = avg j B K u := by
  have hmul : (B.subgroupOf E).index * (E.subgroupOf K).index = (B.subgroupOf K).index :=
    Subgroup.relIndex_mul_relIndex B E K hBE hEK
  have hBEi : (B.subgroupOf E).index ≠ 0 := fun h => hi (by rw [← hmul, h, zero_mul])
  have hEKi : (E.subgroupOf K).index ≠ 0 := fun h => hi (by rw [← hmul, h, mul_zero])
  haveI := finite_Q B K hi
  haveI := finite_Q B E hBEi
  haveI := finite_Q E K hEKi
  letI := Fintype.ofFinite (RQ B K)
  letI := Fintype.ofFinite (RQ B E)
  letI := Fintype.ofFinite (RQ E K)
  let φ : RQ E K × RQ B E → RQ B K := fun p => Quotient.mk _
    (⟨((p.2.out : E) : Λ) * ((p.1.out : K) : Λ), K.mul_mem (hEK (p.2.out : E).2) (p.1.out : K).2⟩ : K)
  have hinj : Function.Injective φ := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have h1 := (mk_eq_iff _ _).mp h
    simp only at h1
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c', mk_eq_iff]
      have : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = ((d'.out : E) : Λ)⁻¹ *
          ((((d'.out : E) : Λ) * ((c'.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹) *
          ((d.out : E) : Λ) := by group
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem (d'.out : E).2) (hBE h1)) (d.out : E).2
    subst hc
    have hd : d = d' := by
      rw [← Quotient.out_eq d, ← Quotient.out_eq d', mk_eq_iff]
      have : ((d'.out : E) : Λ) * ((d.out : E) : Λ)⁻¹ =
          (((d'.out : E) : Λ) * ((c.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹ := by
        group
      rw [this]; exact h1
    rw [hd]
  have hcard : Fintype.card (RQ E K × RQ B E) = Fintype.card (RQ B K) := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, card_Q, card_Q, card_Q, ← hmul, mul_comm]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  funext x
  rw [avg_eq_sum j E K, avg_eq_sum j B K]
  simp_rw [avg_eq_sum j B E u]
  have hs : ∑ q : RQ B K, u (j ((q.out : K) : Λ) * x) =
      ∑ c : RQ E K, ∑ d : RQ B E, u (j ((d.out : E) : Λ) * (j ((c.out : K) : Λ) * x)) := by
    rw [← Fintype.sum_prod_type']
    refine (Fintype.sum_bijective φ hbij _ _ (fun p => ?_)).symm
    simp only [φ]
    rw [linv_out hu]
    dsimp only
    rw [map_mul, mul_assoc]
  rw [hs, ← Finset.mul_sum, ← hmul, Nat.cast_mul]
  ring

end PositivityTheory.KB.SpectralGap.UnfoldA

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PUnfoldB
section
noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace PositivityTheory.KB.SpectralGap.UnfoldB

open PositivityTheory.KB.SpectralGap

def rep {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ)
    (c : Quotient (QuotientGroup.rightRel (B.subgroupOf K))) : S :=
  j ((c.out : K) : Λ)

theorem card_quot {Λ : Type} [Group Λ] (B K : Subgroup Λ) :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

theorem countable_map {Λ S : Type} [Group Λ] [Countable Λ] [Group S] (j : Λ →* S) (K : Subgroup Λ) :
    Countable (K.map j) := by
  have : ((K.map j : Subgroup S) : Set S).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  exact this.to_subtype

theorem rep_ex {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ) :
    ∀ g ∈ K.map j, ∃ h ∈ B.map j, ∃ c, g = h * rep j B K c := by
  rintro g ⟨k, hk, rfl⟩
  let c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) := Quotient.mk _ ⟨k, hk⟩
  have hr : QuotientGroup.rightRel (B.subgroupOf K) c.out ⟨k, hk⟩ := Quotient.mk_out _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at hr
  refine ⟨j (k * ((c.out : K) : Λ)⁻¹), ⟨_, ?_, rfl⟩, c, ?_⟩
  · simpa using hr
  · simp [rep]

theorem rep_inj {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) :
    ∀ h ∈ B.map j, ∀ h' ∈ B.map j, ∀ c c', h * rep j B K c = h' * rep j B K c' → c = c' := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ c c' heq
  rw [rep, rep, ← map_mul, ← map_mul] at heq
  have e := hj heq
  rw [← Quotient.out_equiv_out]
  show QuotientGroup.rightRel (B.subgroupOf K) c.out c'.out
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  have key : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = b'⁻¹ * b := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e]
    group
  simpa [key] using B.mul_mem (B.inv_mem hb') hb

theorem unfold_fd (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S]
    [MeasurableMul S] (μ : Measure S) [μ.IsMulLeftInvariant] (j : Λ →* S) (hj : Function.Injective j)
    (B K : Subgroup Λ) (hBK : B ≤ K) (hi : (B.subgroupOf K).index ≠ 0) :
    ∀ D : Set S, IsFundamentalDomain (K.map j) D μ →
    (∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ) ∧
    ∀ D' : Set S, IsFundamentalDomain (B.map j) D' μ → μ D' = (B.subgroupOf K).index * μ D ∧
      ∀ u : S → ℝ, Measurable u → LInv j B u →
        (IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ) ∧
        (IntegrableOn u D' μ → IntegrableOn (avg j B K u) D μ ∧
          ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ) := by
  intro D hD
  haveI : Countable (K.map j) := countable_map j K
  haveI : Countable (B.map j) := countable_map j B
  haveI : Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
    Nat.finite_of_card_ne_zero (by rw [card_quot]; exact hi)
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hrepΓ : ∀ c, rep j B K c ∈ K.map j := fun c => ⟨((c.out : K) : Λ), c.out.2, rfl⟩
  have hBK' : B.map j ≤ K.map j := Subgroup.map_mono hBK
  have hn : ((B.subgroupOf K).index : ℝ) ≠ 0 := by exact_mod_cast hi
  have hcard : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_quot]
  have hmp : ∀ a : S, MeasurePreserving (fun x => a • x) μ μ := fun a => measurePreserving_smul a μ
  have hemb : ∀ a : S, MeasurableEmbedding (fun x : S => a • x) :=
    fun a => measurableEmbedding_const_smul a
  have havg : ∀ (f : S → ℝ) (x : S), avg j B K f x
      = ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, f (rep j B K c * x) := by
    intro f x
    simp only [avg, finsum_eq_sum_of_fintype]
    rfl
  set D0 : Set S := ⋃ c, rep j B K c • D with hD0def
  have hmeasc : ∀ c, NullMeasurableSet (rep j B K c • D) μ := fun c =>
    hD.nullMeasurableSet_smul (⟨rep j B K c, hrepΓ c⟩ : K.map j)
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun c => rep j B K c • D) := by
    intro c c' hcc'
    have hne : (⟨rep j B K c, hrepΓ c⟩ : K.map j) ≠ ⟨rep j B K c', hrepΓ c'⟩ := by
      intro h
      apply hcc'
      have e := congrArg Subtype.val h
      exact rep_inj j hj B K 1 (one_mem _) 1 (one_mem _) c c' (by simpa using e)
    exact hD.aedisjoint hne
  have hD0 : IsFundamentalDomain (B.map j) D0 μ := by
    refine ⟨NullMeasurableSet.iUnion hmeasc, ?_, ?_⟩
    · filter_upwards [hD.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      obtain ⟨h, hh, c, hgc⟩ := rep_ex j B K ((g : S)⁻¹) (inv_mem g.2)
      refine ⟨⟨h⁻¹, inv_mem hh⟩, Set.mem_iUnion.2 ⟨c, ?_⟩⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      have e : (rep j B K c)⁻¹ * h⁻¹ = (g : S) := by
        rw [← mul_inv_rev, ← hgc, inv_inv]
      convert hg using 1
      show (rep j B K c)⁻¹ * (h⁻¹ * x) = (g : S) * x
      rw [← mul_assoc, e]
    · intro δ δ' hδ
      show AEDisjoint μ ((δ : S) • D0) ((δ' : S) • D0)
      rw [hD0def, Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
      intro c
      rw [AEDisjoint.iUnion_right_iff]
      intro c'
      rw [smul_smul, smul_smul]
      have h1 : (δ : S) * rep j B K c ∈ K.map j := mul_mem (hBK' δ.2) (hrepΓ c)
      have h2 : (δ' : S) * rep j B K c' ∈ K.map j := mul_mem (hBK' δ'.2) (hrepΓ c')
      have hne : (⟨_, h1⟩ : K.map j) ≠ ⟨_, h2⟩ := by
        intro h
        have e := congrArg Subtype.val h
        have hc := rep_inj j hj B K _ δ.2 _ δ'.2 c c' e
        subst hc
        exact hδ (Subtype.ext (mul_right_cancel e))
      exact hD.aedisjoint hne
  refine ⟨⟨D0, hD0⟩, fun D' hD' => ⟨?_, fun u hu hinv => ?_⟩⟩
  · rw [hD'.measure_eq hD0, ← setLIntegral_one, hD0def, lintegral_iUnion₀ hmeasc hdisj, tsum_fintype]
    simp only [setLIntegral_one]
    have hmc : ∀ c, μ (rep j B K c • D) = μ D := fun c => measure_smul μ (rep j B K c) D
    simp only [hmc, Finset.sum_const, hcard, nsmul_eq_mul]
  · have hinvΔ : ∀ (δ : B.map j) (x : S), u (δ • x) = u x := by
      rintro ⟨_, b, hb, rfl⟩ x
      exact hinv b hb x
    have hI : IntegrableOn u D' μ ↔ IntegrableOn u D0 μ := hD'.integrableOn_iff hD0 hinvΔ
    have hIc : IntegrableOn u D0 μ ↔ ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      rw [hD0def, integrableOn_finite_iUnion]
      exact forall_congr' fun c => (hmp _).integrableOn_image (hemb _)
    have hm : ∀ c, Measurable (fun x => u (rep j B K c * x)) := fun c =>
      hu.comp (measurable_const_mul _)
    have hAbs : IntegrableOn (avg j B K fun y => |u y|) D μ ↔
        ∀ c, IntegrableOn (fun x => u (rep j B K c * x)) D μ := by
      constructor
      · intro h c
        have h2 : IntegrableOn (fun x => ((B.subgroupOf K).index : ℝ) *
            avg j B K (fun y => |u y|) x) D μ := h.const_mul _
        refine Integrable.mono' h2 (hm c).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
        rw [havg, Real.norm_eq_abs, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
        exact Finset.single_le_sum (f := fun c => |u (rep j B K c * x)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
      · intro h
        have e : (avg j B K fun y => |u y|)
            = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, |u (rep j B K c * x)| :=
          funext fun x => havg _ x
        rw [e]
        exact (integrable_finsetSum _ fun c _ => (h c).abs).const_mul _
    refine ⟨hI.trans (hIc.trans hAbs.symm), fun hint => ?_⟩
    have hcs := hIc.1 (hI.1 hint)
    have havgInt : IntegrableOn (avg j B K u) D μ := by
      have e : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ * ∑ c, u (rep j B K c * x) :=
        funext fun x => havg _ x
      rw [e]
      exact (integrable_finsetSum _ fun c _ => hcs c).const_mul _
    refine ⟨havgInt, ?_⟩
    have hint0 : IntegrableOn u (⋃ c, rep j B K c • D) μ := by
      rw [← hD0def]
      exact hI.1 hint
    rw [hD'.setIntegral_eq hD0 hinvΔ, hD0def, integral_iUnion_ae hmeasc hdisj hint0, tsum_fintype]
    have hterm : ∀ c, ∫ x in rep j B K c • D, u x ∂μ = ∫ x in D, u (rep j B K c * x) ∂μ :=
      fun c => (hmp _).setIntegral_image_emb (hemb _) u D
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← integral_finsetSum _ fun c _ => hcs c,
      ← integral_const_mul]
    congr 1
    ext x
    rw [havg, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

end PositivityTheory.KB.SpectralGap.UnfoldB

end
end

