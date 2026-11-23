module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.AlternatingMapSubBaseEqAlternatingSumRemoveNth
section
open Function

namespace PositivityTheory.KB.StokesSlices

section Alt

variable {V : Type} [AddCommGroup V] [Module ℝ V]

lemma alternatingMap_sub_on_finset_eq_sub_sum_update {q : ℕ} (f : V [⋀^Fin q]→ₗ[ℝ] ℝ) (x : V) (S : Finset (Fin q)) :
    ∀ u : Fin q → V, f (fun j => if j ∈ S then u j - x else u j) =
      f u - ∑ j ∈ S, f (update u j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro u; simp
  | insert a S ha ih =>
    intro u
    have hfun : (fun j => if j ∈ insert a S then u j - x else u j) =
        (fun j => if j ∈ S then update u a (u a - x) j - x else update u a (u a - x) j) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj, Function.update_of_ne hj]
    rw [hfun, ih]
    have h1 : f (update u a (u a - x)) = f u - f (update u a x) := by
      rw [f.map_update_sub, update_eq_self]
    have h2 : ∀ j ∈ S, f (update (update u a (u a - x)) j x) = f (update u j x) := by
      intro j hj
      have haj : a ≠ j := fun h => ha (h ▸ hj)
      rw [Function.update_comm haj, f.map_update_sub]
      have e1 : update (update u j x) a (u a) = update u j x := by
        conv_lhs => rw [show u a = update u j x a from (Function.update_of_ne haj _ _).symm]
        exact update_eq_self _ _
      have e2 : f (update (update u j x) a x) = 0 := by
        apply f.map_eq_zero_of_eq _ (i := a) (j := j) _ haj
        simp [Function.update_of_ne haj.symm, haj]
      rw [e1, e2, sub_zero]
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_insert ha]
    abel

lemma cons_removeNth_tail {q : ℕ} (v : Fin (q + 2) → V) (j : Fin (q + 1)) :
    Matrix.vecCons (v 0) (j.removeNth (Fin.tail v)) = j.succ.removeNth v := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.tail, Fin.succ_succAbove_succ]

lemma alternatingMap_sub_base_eq_alternating_sum_removeNth (q : ℕ) (f : V [⋀^Fin q]→ₗ[ℝ] ℝ) (v : Fin (q + 1) → V) :
    f (fun j => v j.succ - v 0) = ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) * f (i.removeNth v) := by
  classical
  have h := alternatingMap_sub_on_finset_eq_sub_sum_update f (v 0) Finset.univ (fun j => v j.succ)
  simp only [Finset.mem_univ, if_true] at h
  have hj : ∀ j : Fin q, f (update (fun j => v j.succ) j (v 0)) =
      (-1 : ℝ) ^ (j : ℕ) * f (j.succ.removeNth v) := by
    cases q with
    | zero => intro j; exact j.elim0
    | succ m =>
      intro j
      have hc := cons_removeNth_tail v j
      rw [← Fin.insertNth_removeNth, f.map_insertNth]
      erw [hc]
      simp [Units.smul_def, zsmul_eq_mul]
  have e0 : Fin.removeNth 0 v = fun j => v j.succ := by
    funext j
    simp [Fin.removeNth]
  rw [h, Fin.sum_univ_succ, Finset.sum_congr rfl (fun j _ => hj j), e0, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Alt

theorem subAlt : StokesSimplexSubdivision := by
  intro V _ _ q f v
  exact alternatingMap_sub_base_eq_alternating_sum_removeNth q f.toAlternatingMap v

end PositivityTheory.KB.StokesSlices
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.InsertNthSuccEq
section
open Function MeasureTheory

noncomputable section

namespace PositivityTheory.KB.StokesSlices

namespace Hyp

lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have : Δ m = (⋂ j, {t : Fin m → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by ext t; simp [Δ]
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

variable {n : ℕ}

lemma succAbove_cs_eq (i j : Fin (n + 1)) (h : j ≠ i) : i.castSucc.succAbove j = i.succ.succAbove j := by
  have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

lemma succAbove_cs_self (i : Fin (n + 1)) : i.castSucc.succAbove i = i.succ := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

lemma succAbove_s_self (i : Fin (n + 1)) : i.succ.succAbove i = i.castSucc := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

def invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := update s i (1 - ∑ j, s j)

lemma sum_eq_removeNth (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) :
    ∑ j, s j = s i + ∑ j, i.removeNth s j := by
  rw [Fin.sum_univ_succAbove s i]; rfl

lemma removeNth_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : i.removeNth (invC i s) = i.removeNth s := by
  funext j
  simp [invC, Fin.removeNth]

lemma sum_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : ∑ j, invC i s j = 1 - s i := by
  rw [sum_eq_removeNth i (invC i s), removeNth_invC]
  simp only [invC, update_self]
  rw [sum_eq_removeNth i s]
  ring

lemma invC_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : invC i (invC i s) = s := by
  rw [show invC i (invC i s) = update (invC i s) i (1 - ∑ j, invC i s j) from rfl, sum_invC]
  simp [invC]

lemma invC_mem (i : Fin (n + 1)) {s : Fin (n + 1) → ℝ} (hs : s ∈ Δ (n + 1)) : invC i s ∈ Δ (n + 1) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp [invC]; linarith [hs.2]
    · simp [invC, update_of_ne h, hs.1 j]
  · rw [sum_invC]; linarith [hs.1 i]

lemma preimage_invC (i : Fin (n + 1)) : invC i ⁻¹' Δ (n + 1) = Δ (n + 1) := by
  ext s
  constructor
  · intro h
    have := invC_mem i h
    rwa [invC_invC] at this
  · exact invC_mem i

lemma continuous_invC (i : Fin (n + 1)) : Continuous (invC i) := by
  have hsum : Continuous (fun s : Fin (n + 1) → ℝ => ∑ j, s j) :=
    continuous_finsetSum Finset.univ fun j _ => continuous_apply j
  exact continuous_id.update i (continuous_const.sub hsum)

def invCE (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun := invC i
  invFun := invC i
  left_inv s := invC_invC i s
  right_inv s := invC_invC i s
  measurable_toFun := (continuous_invC i).measurable
  measurable_invFun := (continuous_invC i).measurable

lemma mp_reflect : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (1 - ∑ j, p.2 j - p.1, p.2))
    (volume.prod volume) (volume.prod volume) := by
  have hT : MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => (p.1, 1 - ∑ j, p.1 j - p.2))
      (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id volume).skew_product (g := fun (r : Fin n → ℝ) (x : ℝ) => 1 - ∑ j, r j - x) ?_ ?_
    · have hsum : Continuous (fun p : (Fin n → ℝ) × ℝ => ∑ j, p.1 j) :=
        continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).comp continuous_fst
      exact ((continuous_const.sub hsum).sub continuous_snd).measurable
    · exact Filter.Eventually.of_forall fun r => (Measure.measurePreserving_sub_left volume _).map_eq
  exact (Measure.measurePreserving_swap.comp hT).comp Measure.measurePreserving_swap

lemma mp_invC (i : Fin (n + 1)) : MeasurePreserving (invC i) volume volume := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hfun : invC i = e.symm ∘ (fun p : ℝ × (Fin n → ℝ) => (1 - ∑ j, p.2 j - p.1, p.2)) ∘ e := by
    funext s
    apply e.injective
    have he_apply : ∀ s, e s = (s i, i.removeNth s) := fun s => rfl
    rw [comp_apply, comp_apply, MeasurableEquiv.apply_symm_apply, he_apply, he_apply, removeNth_invC]
    refine Prod.ext ?_ rfl
    simp only [invC, update_self]
    rw [sum_eq_removeNth i s]
    ring
  rw [hfun]
  exact he.symm.comp (mp_reflect.comp he)

lemma insertNth_succ_eq (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i.succ (1 - ∑ j, s j) s =
      Fin.insertNth (α := fun _ => ℝ) i.castSucc (1 - ∑ j, invC i s j) (invC i s) := by
  rw [sum_invC, sub_sub_cancel]
  funext k
  refine i.succ.succAboveCases ?_ (fun j => ?_) k
  · rw [Fin.insertNth_apply_same, ← succAbove_cs_self, Fin.insertNth_apply_succAbove]
    simp [invC]
  · rw [Fin.insertNth_apply_succAbove]
    by_cases h : j = i
    · subst h
      rw [succAbove_s_self, Fin.insertNth_apply_same]
    · rw [← succAbove_cs_eq i j h, Fin.insertNth_apply_succAbove]
      simp [invC, update_of_ne h]

lemma hyp_step (m : ℕ) (G : (Fin (m + 1) → ℝ) → ℝ) (i : Fin m) :
    ∫ s in Δ m, G (i.succ.insertNth (1 - ∑ j, s j) s) =
      ∫ s in Δ m, G (i.castSucc.insertNth (1 - ∑ j, s j) s) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  have h := (mp_invC i).setIntegral_preimage_emb (invCE i).measurableEmbedding
    (fun s => G (i.castSucc.insertNth (1 - ∑ j, s j) s)) (Δ (n + 1))
  rw [preimage_invC] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_Δ _) fun s _ => ?_
  exact congrArg G (insertNth_succ_eq i s)

end Hyp

open Hyp in
theorem subHyp : SubHyp := by
  intro m G i
  induction i using Fin.induction with
  | zero =>
    congr 1
    funext s
    congr 1
    exact Fin.insertNth_zero' _ _
  | succ i ih => rw [hyp_step, ih]

end PositivityTheory.KB.StokesSlices
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SumInsertNth
section
noncomputable section

open MeasureTheory Set

namespace PositivityTheory.KB.StokesSlices

lemma sum_insertNth' {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    ∑ j, i.insertNth x s j = x + ∑ j, s j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

lemma mem_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (x : ℝ) (s : Fin m → ℝ) :
    i.insertNth x s ∈ Δ (m + 1) ↔ s ∈ Δ m ∧ x ∈ Icc 0 (1 - ∑ j, s j) := by
  simp only [Δ, mem_ofPred_eq, mem_Icc, sum_insertNth', i.forall_iff_succAbove,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  constructor
  · rintro ⟨⟨hx, hs⟩, h⟩
    exact ⟨⟨hs, by
      have : 0 ≤ ∑ j, s j := Finset.sum_nonneg fun j _ => hs j
      linarith⟩, hx, by linarith⟩
  · rintro ⟨⟨hs, _⟩, hx, h⟩
    exact ⟨⟨hx, hs⟩, by linarith⟩

lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ j, 0 ≤ t j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ j, t j ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  exact h1.inter h2

lemma isCompact_Δ (m : ℕ) : IsCompact (Δ m) := by
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).of_isClosed_subset (isClosed_Δ m) ?_
  rintro t ⟨h0, h1⟩
  refine ⟨fun j => h0 j, fun j => ?_⟩
  calc t j ≤ ∑ k, t k := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
    _ ≤ 1 := h1

lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

lemma integrableOn_Δ_insertNth {m : ℕ} (i : Fin (m + 1)) (G : (Fin (m + 1) → ℝ) → ℝ)
    (W : Set (Fin (m + 1) → ℝ)) (hΔW : Δ (m + 1) ⊆ W) (hG : ContinuousOn G W)
    (c : (Fin m → ℝ) → ℝ) (hc : Continuous c) (hc0 : ∀ s ∈ Δ m, 0 ≤ c s)
    (hc1 : ∀ s ∈ Δ m, c s ≤ 1 - ∑ j, s j) :
    IntegrableOn (fun s => G (i.insertNth (c s) s)) (Δ m) := by
  refine ContinuousOn.integrableOn_compact (isCompact_Δ m) ?_
  have hcont : Continuous (fun s : Fin m → ℝ => (i.insertNth (c s) s : Fin (m + 1) → ℝ)) :=
    Continuous.finInsertNth i hc continuous_id
  refine hG.comp hcont.continuousOn ?_
  intro s hs
  exact hΔW ((mem_Δ_insertNth i _ _).2 ⟨hs, hc0 s hs, hc1 s hs⟩)

theorem subSlice : SubSlice := by
  intro m i G D W hW hΔW hG hD hderiv
  set e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm with he_def
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have he : ∀ p : ℝ × (Fin m → ℝ), e p = i.insertNth p.1 p.2 := fun p => rfl
  have hDint : IntegrableOn D (Δ (m + 1)) :=
    (hD.mono hΔW).integrableOn_compact (isCompact_Δ _)
  have hS : MeasurableSet (e ⁻¹' Δ (m + 1)) := e.measurable (measurableSet_Δ _)
  have hFint : IntegrableOn (fun p => D (e p)) (e ⁻¹' Δ (m + 1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hDint
  rw [← hem.map_eq, setIntegral_map_equiv, Measure.volume_eq_prod,
    ← integral_indicator hS, integral_prod_symm _ ((integrable_indicator_iff hS).2 hFint)]
  have hA := integrableOn_Δ_insertNth i G W hΔW hG (fun s => 1 - ∑ j, s j)
    (continuous_const.sub (by fun_prop))
    (fun s hs => by have := hs.2; linarith) (fun s hs => le_rfl)
  have hB := integrableOn_Δ_insertNth i G W hΔW hG (fun _ => 0) continuous_const
    (fun s hs => le_rfl) (fun s hs => by have := hs.2; linarith)
  rw [← integral_sub hA hB, ← integral_indicator (measurableSet_Δ m)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Δ m
  · rw [Set.indicator_of_mem hs]
    have ha : 0 ≤ 1 - ∑ j, s j := by have := hs.2; linarith
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) =
        (Icc 0 (1 - ∑ j, s j)).indicator (fun x => D (i.insertNth x s)) x := by
      intro x
      by_cases hx : x ∈ Icc 0 (1 - ∑ j, s j)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        · rw [he]
        · show e (x, s) ∈ Δ (m + 1)
          rw [he]
          exact (mem_Δ_insertNth i x s).2 ⟨hs, hx⟩
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        show e (x, s) ∉ Δ (m + 1)
        rw [he]
        exact fun h => hx ((mem_Δ_insertNth i x s).1 h).2
    simp_rw [h1]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ha]
    have hcs : Continuous fun x : ℝ => Fin.insertNth (α := fun _ => ℝ) i x s := by
      fun_prop
    have hin : ∀ x ∈ Icc 0 (1 - ∑ j, s j), i.insertNth x s ∈ W :=
      fun x hx => hΔW ((mem_Δ_insertNth i x s).2 ⟨hs, hx⟩)
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G (i.insertNth x s))
    · intro x hx
      rw [Set.uIcc_of_le ha] at hx
      have := hderiv _ (hin x hx)
      simpa [Fin.update_insertNth, Fin.insertNth_apply_same] using this
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ha]
      exact hD.comp hcs.continuousOn hin
  · rw [Set.indicator_of_notMem hs]
    have h1 : ∀ x, (e ⁻¹' Δ (m + 1)).indicator (fun p => D (e p)) (x, s) = 0 := by
      intro x
      apply Set.indicator_of_notMem
      show e (x, s) ∉ Δ (m + 1)
      rw [he]
      exact fun h => hs ((mem_Δ_insertNth i x s).1 h).1
    simp_rw [h1]
    simp

end PositivityTheory.KB.StokesSlices
end
end

