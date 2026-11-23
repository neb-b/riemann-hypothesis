module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensVdApply
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

def twT (ε : Fin n → Bool) : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
  LinearMap.pi fun c => sg ε (Fin.rev c) • prj (Fin.rev c)

theorem twT_apply (ε : Fin n → Bool) (f : Fin n → M) (c : Fin n) :
    twT ε f c = sg ε (Fin.rev c) • f (Fin.rev c) := by
  simp [twT, prj]

theorem twT_eq_zero {ε : Fin n → Bool} {f : Fin n → M} (h : twT ε f = 0) : f = 0 := by
  funext c
  have := congrFun h (Fin.rev c)
  rw [twT_apply, Fin.rev_rev] at this
  exact (smul_eq_zero.1 this).resolve_left (sg_ne ε c)

theorem twT_tens (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) :
    tensV (twE ε E) a b (twT ε f) = twT ε (twE ε (tensVd E) a b f) := by
  funext c
  rw [tensV_apply', twT_apply, twT_apply, twE_apply, twE_apply, map_smul (twT ε), Pi.smul_apply,
    twT_apply, tensVd_apply', map_smul]
  simp only [Fin.rev_inj]
  by_cases hc : c = a
  · subst hc
    simp only [if_true]
    unfold sg; split_ifs <;> module
  · simp [hc]

theorem twT_ee (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    eeV (twE ε E) (twT ε f) = twT ε (eeVd E f) := by
  funext d
  rw [eeV_apply', twT_apply, eeVd_apply', smul_neg, Finset.smul_sum,
    ← sum_rev (fun c => sg ε (Fin.rev d) • E (Fin.rev d) c (f c)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [twT_apply, twE_apply, map_smul, smul_smul, ← neg_smul]
  congr 1
  linear_combination (-sg ε (Fin.rev d)) * sg_sq ε (Fin.rev c)

theorem mem_Xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs A S θ ↔ (∀ c, f c ∈ S) ∧ A f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]

theorem xs_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} {θ : ℝ}
    {f : Fin n → M} (h : f ∈ Xs (eeVd E) S θ) : twT ε f ∈ Xs (eeV (twE ε E)) S θ := by
  rw [mem_Xs] at h ⊢
  refine ⟨fun c => ?_, ?_⟩
  · rw [twT_apply]; exact S.smul_mem _ (h.1 _)
  · rw [twT_ee, h.2, map_smul]

theorem khwT_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ}
    {f : Fin n → M} (h : IsKHWVec ε (tensVd E) μ f) :
    IsKHWVec (ε ∘ Fin.rev) (tensV (twE ε E)) (fun a => -μ (Fin.rev a)) (twT ε f) := by
  have h' := khw_tw h
  exact ⟨fun a => by rw [twT_tens, h'.1, map_smul], fun a b hab he => by
    rw [twT_tens, h'.2 a b hab he, map_zero]⟩

end Tens

section Wt

theorem rhoN_tw (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  unfold rhoN
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

theorem rhoC_tw (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  unfold rhoC
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

theorem lowK_tw (ε : Fin n → Bool) (ν : Fin n → ℝ) :
    lowK (ε ∘ Fin.rev) (fun a => -ν (Fin.rev a)) = fun a => -lowK ε ν (Fin.rev a) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]
  ring

theorem casVal_tw (lam : Fin n → ℝ) : casVal (fun a => -lam (Fin.rev a)) = casVal lam := by
  unfold casVal nsq dot
  simp only [neg_mul_neg]
  rw [sum_rev (fun a => lam a * lam a)]

theorem pOf_tw (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε := by
  unfold pOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem qOf_tw (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε := by
  unfold qOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem gapLap_tw {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
  · have := h1 (Fin.rev_lt_rev.2 hab)
    simp only; linarith
  · have := h2 (Fin.rev a) (Fin.rev b) hab
    rw [abs_sub_comm] at this
    simp only; rwa [neg_sub_neg]
  · have e : hNeed (ε ∘ Fin.rev) = hNeed ε := by unfold hNeed; rw [pOf_tw, qOf_tw]
    rw [e]; exact h3

theorem root_rev (a b x : Fin n) : root (Fin.rev b) (Fin.rev a) x = -root a b (Fin.rev x) := by
  have e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i) := fun i j => by
    constructor <;> rintro rfl <;> simp
  simp only [root, Pi.sub_apply, Pi.single_apply, e]
  ring

theorem cone_ev (k : Fin n → Fin n → ℕ) (y : Fin n) :
    (∑ a, ∑ b, if a < b then (k a b : ℝ) • root a b else 0) y =
      ∑ a, ∑ b, if a < b then (k a b : ℝ) * root a b y else 0 := by
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cone_rev {β : Fin n → ℝ} (h : InRootCone (fun a => -β (Fin.rev a))) : InRootCone β := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun a b => m (Fin.rev b) (Fin.rev a), ?_⟩
  funext x
  have hx := congrFun hm (Fin.rev x)
  simp only [Fin.rev_rev] at hx
  rw [cone_ev] at hx
  rw [cone_ev, show β x = -(-β x) by ring, hx, ← sum_rev, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sum_rev, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.rev_rev, Fin.rev_lt_rev, root_rev]
  split_ifs <;> ring

end Wt

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core2

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_cone_core (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (A : Module.End ℂ U)
    (hA : ∀ a b, Commute A (T a b)) (F : ℕ → Submodule ℂ U) (θ : ℕ → ℂ)
    (hF : ∀ k a b, ∀ x ∈ F k, T a b x ∈ F k)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1))
    (m j : ℕ) (h0 : F 0 = ⊤) (hm : F m = ⊥) (hj : j < m) (hθ : ∀ k < m, k ≠ j → θ k ≠ θ j)
    (v : U) (base : Fin n → ℝ) (hFj : F j ≤ genSub T (Submodule.span ℂ {v}) ⊔ F (j + 1))
    (hlow : ∀ a b, b < a → T a b v ∈ F (j + 1)) (hdiag : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    (∀ (μ : Fin n → ℝ) (x : U), A x = θ j • x → x ≠ 0 → (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) →
        InRootCone (μ - base)) ∧
    ∀ x₁ x₂ : U, A x₁ = θ j • x₁ → A x₂ = θ j • x₂ →
      (∀ a, T a a x₁ = ((base a : ℝ) : ℂ) • x₁) → (∀ a, T a a x₂ = ((base a : ℝ) : ℂ) • x₂) →
      ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • x₁ + c₂ • x₂ = 0 := by
  have hiter_maps : ∀ k₀ i x, x ∈ F k₀ → vcIter A θ k₀ i x ∈ F (k₀ + i) := by
    intro k₀ i
    induction i with
    | zero =>
        intro x hx
        simpa [vcIter] using hx
    | succ i ih =>
        intro x hx
        have h := hstep (k₀ + i) _ (ih x hx)
        simpa [vcIter, Module.End.mul_apply, LinearMap.sub_apply, add_assoc] using h
  set post := vcIter A θ (j + 1) (m - j - 1) with hpost
  set c' : ℂ := ∏ i ∈ range (m - j - 1), (θ j - θ (j + 1 + i)) with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc', Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    exact sub_ne_zero.mpr (hθ (j + 1 + i) (by omega) (by omega)).symm
  have hpostT : ∀ a b, Commute post (T a b) := fun a b => vcIter_comm A θ _ (hA a b) _
  have hred : ∀ x, A x = θ j • x → ∃ y ∈ Submodule.span ℂ (vcMonAll T v), post y = c' • x := by
    intro x hx
    have hxj : x ∈ F j := by
      have h1 := hiter_maps 0 j x (by rw [h0]; exact Submodule.mem_top)
      rw [vcIter_eig A θ 0 hx j, Nat.zero_add] at h1
      have hc : (∏ i' ∈ range j, (θ j - θ (0 + i'))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        exact sub_ne_zero.mpr (hθ (0 + i) (by omega) (by omega)).symm
      have := (F j).smul_mem (∏ i' ∈ range j, (θ j - θ (0 + i')))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hx2 : x ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F (j + 1) := by
      have h3 := vc_genSub_le_mon T hT v (F (j + 1)) (hF (j + 1)) hlow (fun a => ⟨_, hdiag a⟩)
      exact (sup_le h3 le_sup_right) (hFj hxj)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
    refine ⟨y, hy, ?_⟩
    have hpz : post z = 0 := by
      have := hiter_maps (j + 1) (m - j - 1) z hz
      rw [show j + 1 + (m - j - 1) = m by omega, hm] at this
      exact (Submodule.mem_bot ℂ).mp this
    have hpx : post x = c' • x := vcIter_eig A θ (j + 1) hx _
    rw [← hpx, ← hyz, map_add (f := _), hpz, add_zero]
  have hpostGood : ∀ (P : (Fin n → ℝ) → Prop) (w : U), w ∈ vcGood T P → post w ∈ vcGood T P := by
    intro P w ⟨ν, hP, hν⟩
    refine ⟨ν, hP, fun a => ?_⟩
    rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hν a, map_smul]
  have hspanGood : ∀ (P : (Fin n → ℝ) → Prop) (G : Set U), G ⊆ vcGood T P →
      ∀ y ∈ Submodule.span ℂ G, post y ∈ Submodule.span ℂ (vcGood T P) := by
    intro P G hG y hy
    have : Submodule.span ℂ G ≤ (Submodule.span ℂ (vcGood T P)).comap post :=
      Submodule.span_le.mpr (fun w hw => Submodule.subset_span (hpostGood P w (hG hw)))
    exact this hy
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hμ
    by_contra hcone
    obtain ⟨y, hy, hyx⟩ := hred x hx
    have hmon : vcMonAll T v ⊆ vcGood T (fun ν => InRootCone (ν - base)) := by
      intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ν, hν, hc, _⟩ := vcMon_weight T hT hdiag k w hk
      exact ⟨ν, hc, hν⟩
    have hs := hspanGood _ _ hmon y hy
    rw [hyx] at hs
    have hz := vc_eq_zero_of_mem_span T (fun ν => InRootCone (ν - base)) hcone
      (x := c' • x) (fun a => by rw [map_smul, hμ a, smul_comm]) hs
    exact hx0 ((smul_eq_zero.mp hz).resolve_left hc'0)
  · have hpv : ∀ a, T a a (post v) = ((base a : ℝ) : ℂ) • post v := by
      intro a
      rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hdiag a, map_smul]
    have hvert : ∀ x, A x = θ j • x → (∀ a, T a a x = ((base a : ℝ) : ℂ) • x) →
        ∃ β : ℂ, x = β • post v := by
      intro x hx hxw
      obtain ⟨y, hy, hyx⟩ := hred x hx
      have hmon : vcMonAll T v ⊆
          (Submodule.span ℂ {v} ⊔ Submodule.span ℂ (vcGood T (fun ν => ν ≠ base)) : Submodule ℂ U) := by
        intro w hw
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
        rcases k with _ | k
        · have hwv : w = v := hk
          subst hwv
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
        · obtain ⟨ν, hν, _, hht⟩ := vcMon_weight T hT hdiag (k + 1) w hk
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨ν, ?_, hν⟩)
          intro hνb
          rw [hνb, sub_self, vcHt_zero] at hht
          push_cast at hht
          linarith
      have hy2 := (Submodule.span_le.mpr hmon) hy
      obtain ⟨y1, hy1, r, hr, hyr⟩ := Submodule.mem_sup.mp hy2
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy1
      have hpr := hspanGood (fun ν => ν ≠ base) _ (Set.Subset.refl _) r hr
      have hd : c' • x - α • post v = post r := by
        rw [← hyx, ← hyr, map_add (f := _), map_smul]
        abel
      have hdw : ∀ a, T a a (c' • x - α • post v) = ((base a : ℝ) : ℂ) • (c' • x - α • post v) := by
        intro a
        rw [map_sub, map_smul, map_smul, hxw a, hpv a, smul_sub, smul_comm c', smul_comm α]
      have hd0 := vc_eq_zero_of_mem_span T (fun ν => ν ≠ base) (μ := base) (by simp) hdw
        (by rw [hd]; exact hpr)
      refine ⟨c'⁻¹ * α, ?_⟩
      rw [sub_eq_zero] at hd0
      rw [mul_smul, ← hd0, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
    intro x₁ x₂ h1 h2 hw1 hw2
    obtain ⟨β₁, rfl⟩ := hvert x₁ h1 hw1
    obtain ⟨β₂, rfl⟩ := hvert x₂ h2 hw2
    by_cases hb : β₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hb]⟩
    · refine ⟨β₂, -β₁, Or.inr (neg_ne_zero.mpr hb), ?_⟩
      rw [smul_smul, smul_smul, mul_comm β₂ β₁, neg_mul, neg_smul, add_neg_cancel]

def vcFlag (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ) (k : ℕ) : Submodule ℂ U :=
  genSub T (Submodule.span ℂ (g '' {t | k ≤ r t}))

variable (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ)

theorem vcFlag_stable (k : ℕ) (a b : Fin n) : ∀ x ∈ vcFlag T g r k, T a b x ∈ vcFlag T g r k :=
  fun _ hx => vc_genSub_stable T _ a b hx

theorem vcFlag_gen {t : Fin n} {k : ℕ} (h : k ≤ r t) : g t ∈ vcFlag T g r k :=
  vc_le_genSub T _ (Submodule.subset_span ⟨t, h, rfl⟩)

theorem vcFlag_anti {k l : ℕ} (h : k ≤ l) : vcFlag T g r l ≤ vcFlag T g r k :=
  vc_genSub_le T _ _ (Submodule.span_le.mpr (by
    rintro _ ⟨t, ht, rfl⟩
    exact vcFlag_gen T g r (le_trans h ht))) (vcFlag_stable T g r k)

theorem vcFlag_eq_bot {m : ℕ} (hm : ∀ t, r t < m) : vcFlag T g r m = ⊥ := by
  refine le_bot_iff.mp (vc_genSub_le T _ ⊥ ?_ (fun a b v hv => by
    rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _))
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact absurd ht (not_le.mpr (hm t))

theorem vcFlag_step (A : Module.End ℂ U) (hA : ∀ a b, Commute A (T a b)) (θ : ℕ → ℂ)
    (hgen : ∀ t, A (g t) - θ (r t) • g t ∈ vcFlag T g r (r t + 1)) :
    ∀ k, ∀ x ∈ vcFlag T g r k, A x - θ k • x ∈ vcFlag T g r (k + 1) := by
  have hAst : ∀ k, ∀ x ∈ vcFlag T g r k, A x ∈ vcFlag T g r k := by
    intro k
    let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r k).comap A
    have hle : vcFlag T g r k ≤ S := by
      refine vc_genSub_le T _ S ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨vcFlag_gen T g r ht, ?_⟩
        show A (g t) ∈ vcFlag T g r k
        have h1 := vcFlag_anti T g r (show k ≤ r t + 1 by simp at ht; omega) (hgen t)
        have h2 := (vcFlag T g r k).smul_mem (θ (r t)) (vcFlag_gen T g r ht)
        simpa using (vcFlag T g r k).add_mem h1 h2
      · intro a b x hx
        refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
        show A (T a b x) ∈ vcFlag T g r k
        rw [← Module.End.mul_apply, (hA a b).eq, Module.End.mul_apply]
        exact vcFlag_stable T g r k a b _ hx.2
    exact fun x hx => (hle hx).2
  intro k
  let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r (k + 1)).comap (A - θ k • 1)
  have hle : vcFlag T g r k ≤ S := by
    refine vc_genSub_le T _ S ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨vcFlag_gen T g r ht, ?_⟩
      show (A - θ k • 1) (g t) ∈ vcFlag T g r (k + 1)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      have ht' : k ≤ r t := ht
      rcases eq_or_lt_of_le ht' with h | h
      · rw [h]; exact hgen t
      · have hg : g t ∈ vcFlag T g r (k + 1) := vcFlag_gen T g r h
        exact Submodule.sub_mem _ (hAst (k + 1) _ hg) (Submodule.smul_mem _ _ hg)
    · intro a b x hx
      refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
      show (A - θ k • 1) (T a b x) ∈ vcFlag T g r (k + 1)
      have hc : Commute (A - θ k • 1) (T a b) := (hA a b).sub_left ((Commute.one_left _).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      exact vcFlag_stable T g r (k + 1) a b _ hx.2
  intro x hx
  have := (hle hx).2
  simpa using this

theorem vcFlag_top_le {j : ℕ} {s : Fin n} (hr : Function.Injective r) (hj : r s = j) :
    vcFlag T g r j ≤ genSub T (Submodule.span ℂ {g s}) ⊔ vcFlag T g r (j + 1) := by
  refine vc_genSub_le T _ _ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : j ≤ r t := ht
    rcases eq_or_lt_of_le ht' with h | h
    · have hts : t = s := hr (by omega)
      subst hts
      exact Submodule.mem_sup_left (vc_le_genSub T _ (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (vcFlag_gen T g r h)
  · intro a b x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (vc_genSub_stable T _ a b hy) (vcFlag_stable T g r _ a b z hz)

end Core2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

