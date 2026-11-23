module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationBoundaryCriterionOfWdBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma wd_congr' (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, w i = 0 ∨ c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h
  · simp [h]
  · rw [h]

private lemma card_erase_mem' {Q t : Finset σ} {i : σ} (hi : i ∈ t) (hQ : i ∈ Q) :
    (((t.erase i) ∩ Q).card : ℤ) = ((t ∩ Q).card : ℤ) - 1 := by
  have h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : i ∈ t ∩ Q := Finset.mem_inter.2 ⟨hi, hQ⟩
  have h3 : 0 < (t ∩ Q).card := Finset.card_pos.2 ⟨i, h2⟩
  rw [h1, Finset.card_erase_of_mem h2]
  omega

private lemma card_erase_not' {Q t : Finset σ} {i : σ} (hQ : i ∉ Q) :
    (t.erase i) ∩ Q = t ∩ Q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩

private lemma levQ' (w : σ → Module.End ℂ E) (Q : Finset σ) {m m' : ℤ} (hm : m' = m + 1)
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m') (wd (wOn Q w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m') := ht
  have h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · right
      refine hy _ ?_
      have h1 := card_erase_mem' hi hiQ
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      omega
    · left
      simp [wOn, hiQ]
  rw [h0, map_zero]
  rfl

private lemma levC' (w : σ → Module.End ℂ E) (Q : Finset σ) {m : ℤ}
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m) (wd (wOn Qᶜ w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m) := ht
  have h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · left
      simp [wOn, hiQ]
    · right
      refine hy _ ?_
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      rw [card_erase_not' hiQ]
      exact ht'
  rw [h0, map_zero]
  rfl

private lemma wd_split' (hW : WdBasic) (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = wd (wOn Q w) c t + wd (wOn Qᶜ w) c t := by
  have h := (hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)
  have h2 : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [h2] at h
  rw [h]
  rfl

private lemma sub_cocycle' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (hcx : (acx A w).IsCx) {n : ℤ} {c y : Finset σ → E} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) : c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨h1, h2⟩ := hcx _ y hy
  rw [sub_add_cancel] at h1
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩
  have h3 : wd w c = 0 := hc2
  have h4 : wd w (wd w y) = 0 := h2
  show wd w (c - wd w y) = 0
  rw [map_sub, h3, h4, sub_zero]

private lemma of_sub' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c y : Finset σ → E} (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have h2 : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  simpa using add_mem h h2

private lemma low' (hW : WdBasic) {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {Q : Finset σ} {d : ℤ} (hok : WOk A w) (hq : QEx A w Q d) :
    ∀ k : ℕ, k ≤ d.toNat → ∀ (n : ℤ) (c : Finset σ → E), c ∈ (acx A w).Z n →
      Lev Q (· ≤ (k : ℤ) - 1) c → c ∈ (acx A w).B n := by
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  intro k
  induction k with
  | zero =>
    intro _ n c hc hl
    have h0 : c = 0 := by
      funext s
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)
      omega
    rw [h0]
    exact zero_mem _
  | succ k ih =>
    intro hk n c hc hl
    have hkd : (k : ℤ) < d := by omega
    have hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0 := by
      intro s hs
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)
      push_cast
      omega
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
    have hc3 : wd w c = 0 := hc2
    let cm : Finset σ → E := fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0
    have hcm : cm ∈ (acx A w).C n := by
      refine Submodule.mem_pi.2 fun s hs => ?_
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · have : cm s = c s := if_pos h
        rw [this]
        exact Submodule.mem_pi.1 hc1 s hs
      · have : cm s = 0 := if_neg h
        rw [this]
        exact zero_mem _
    have hcl : Lev Q (· = (k : ℤ)) cm := fun s hs => if_neg hs
    have hkill : wd (wOn Q w) cm = 0 := by
      funext t
      by_cases ht : ((t ∩ Q).card : ℤ) = k + 1
      · have e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · right
            have h1 := card_erase_mem' hi hiQ
            exact if_pos (by omega)
          · left
            simp [wOn, hiQ]
        have e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · left
            simp [wOn, hiQ]
          · right
            refine hl' _ ?_
            rw [card_erase_not' hiQ]
            omega
        have e3 := wd_split' hW A w Q c t
        rw [hc3, e2, map_zero] at e3
        rw [e1]
        simpa using e3.symm
      · exact levQ' w Q rfl hcl t ht
    obtain ⟨y, hy, hyl, hyd⟩ := hq n k hkd cm hcm hcl hkill
    refine of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)
    intro s hs
    have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1) := hs
    have e1 := wd_split' hW A w Q y s
    have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
      show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1)
      omega)
    have e3 : wd (wOn Q w) y s = cm s := congrFun hyd s
    have e4 : cm s = c s := by
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · exact if_pos h
      · have : cm s = 0 := if_neg h
        rw [this, hl' s (by omega)]
    show c s - wd w y s = 0
    rw [e1, e2, e3, e4, add_zero, sub_self]

end

theorem UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic :
    WdBasic → FiltrationBoundaryCriterion := by
  intro hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0
  obtain ⟨y, hy, hyl, hyd⟩ := hy0
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  have hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0 := by
    intro s hs
    refine hl s ?_
    show ¬ (((s ∩ Q).card : ℤ) ≤ d)
    omega
  refine of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)
  intro s hs
  have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1) := hs
  have hge : d ≤ ((s ∩ Q).card : ℤ) := by omega
  have e1 := wd_split' hW A w Q y s
  have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
    show ¬ (((s ∩ Q).card : ℤ) = d - 1)
    omega)
  show c s - wd w y s = 0
  rw [e1, e2, add_zero]
  by_cases h : ((s ∩ Q).card : ℤ) = d
  · rw [hyd s h, sub_self]
  · have e3 : wd (wOn Q w) y s = 0 := levQ' w Q (by ring) hyl s h
    rw [e3, hl' s (by omega), sub_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoExactOfGl2
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.WH

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_single {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (T : Finset σ) (v : E) :
    wd w (Pi.single T v) =
      ∑ i ∈ Tᶜ, Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) := by
  funext t
  have hl : wd w (Pi.single T v) t =
      ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  have L : ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ((Pi.single T v : Finset σ → E) (t.erase i)) =
      ∑ i, if i ∈ t ∧ t.erase i = T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : t.erase i = T
    · simp [hi, h]
    · simp [hi, h, Pi.single_eq_of_ne h]
  have Rr : (∑ i ∈ Tᶜ, (Pi.single (insert i T) (GlobalTheory.cubeSign (insert i T) i • w i v) :
      Finset σ → E)) t =
      ∑ i, if i ∉ T ∧ t = insert i T then GlobalTheory.cubeSign t i • w i v else 0 := by
    rw [Finset.sum_apply, ← Finset.sum_subset (Finset.subset_univ Tᶜ)
      (fun i _ hi => by simp at hi; simp [hi])]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ∉ T := by simpa using hi
    by_cases h : t = insert i T
    · subst h; simp [hi']
    · simp [hi', h, Pi.single_eq_of_ne h]
  rw [hl, L, Rr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (i ∈ t ∧ t.erase i = T) ↔ (i ∉ T ∧ t = insert i T) := by
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨Finset.mem_insert_self _ _, Finset.erase_insert h1⟩
  simp only [this]

private theorem sm_dec {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) {x : E}
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧ x = ∑ j, act (f j) (g j) := by
  unfold sm at hx
  rw [iSup_range] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ∃ g : Fin d → E, (∀ j, g j ∈ M) ∧
    x = ∑ j, act (f j) (g j)) hx ?_ ?_ ?_
  · intro j x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨Pi.single j m, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using hm
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  · exact ⟨0, fun _ => M.zero_mem, by simp⟩
  · rintro x y ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', fun j => M.add_mem (hg j) (hg' j), by
      simp [Finset.sum_add_distrib]⟩

private theorem single_mem {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (M : Submodule ℂ E) (w : σ → Module.End ℂ E) {T : Finset σ} {v : E} {d : ℕ}
    (hT : T.card = d) (hv : v ∈ M) :
    (Pi.single T v : Finset σ → E) ∈ (acx (fun _ => M) w).C d := by
  simp only [acx, Submodule.mem_pi]
  intro s _
  by_cases h : s = T
  · subst h; simp [hT, hv]
  · simp [Pi.single_eq_of_ne h]

theorem koszulTwoExact_of_gl2 : FiltrationCocycleLiftCriterion → SubQEx → KoszulCocycleExistsWithPrescribedComponent := by
  intro gl2 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hke m hm hsm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = img e := ⟨_, rfl⟩
  have hcard : Q.card = d := by simp [hQ, img]
  have hQmem : ∀ j, e j ∈ Q := fun j => by simp [hQ, img]
  have qex : QEx (fun _ => M) (fun l => act (r l)) Q d := hQ ▸ subq S E act κ M r d e hke
  have wok : WOk (fun _ : Finset κ => M) (fun l => act (r l)) :=
    ⟨fun i j => by
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm], fun s i _ x hx => hst _ (hr i) _ hx⟩
  choose g hgM hg using fun l => sm_dec act M (fun j => r (e j)) (hsm l)
  have hTcard : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)).card = d := fun l hl j => by
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (hQmem j)), Finset.card_insert_of_notMem hl,
      hcard]
    rfl
  have hTQ : ∀ l, l ∉ Q → ∀ j, ((insert l Q).erase (e j)) ∩ Q = Q.erase (e j) := fun l hl j => by
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, Or.inr h2⟩, h2⟩
  have hterm : ∀ l, l ∉ Q → ∀ j (v : E),
      wd (wOn Q fun l => act (r l)) (Pi.single ((insert l Q).erase (e j)) v) =
        Pi.single (insert l Q) (GlobalTheory.cubeSign (insert l Q) (e j) • act (r (e j)) v) := by
    intro l hl j v
    have hmem : e j ∈ insert l Q := Finset.mem_insert_of_mem (hQmem j)
    rw [wd_single, Finset.sum_eq_single (e j)]
    · rw [Finset.insert_erase hmem]
      simp [wOn, hQmem j]
    · intro i hi hne
      have hiQ : i ∉ Q := by
        intro h
        apply (Finset.mem_compl.1 hi)
        exact Finset.mem_erase.2 ⟨hne, Finset.mem_insert_of_mem h⟩
      simp [wOn, hiQ]
    · intro h
      exact absurd (Finset.mem_compl.2 (Finset.notMem_erase _ _)) h
  have hsum : ∀ (t : Finset κ) (f : Fin d → E),
      (Pi.single t (∑ j, f j) : Finset κ → E) = ∑ j, Pi.single t (f j) := fun t f =>
    map_sum (AddMonoidHom.single (fun _ : Finset κ => E) t) f Finset.univ
  have hy : ∃ y ∈ (acx (fun _ => M) (fun l => act (r l))).C d, Lev Q (· = (d : ℤ) - 1) y ∧
      wd (wOn Q fun l => act (r l)) y = wd (wOn Qᶜ fun l => act (r l)) (Pi.single Q m) := by
    refine ⟨∑ l ∈ Qᶜ, ∑ j, Pi.single ((insert l Q).erase (e j))
        ((GlobalTheory.cubeSign (insert l Q) l * GlobalTheory.cubeSign (insert l Q) (e j)) • g l j), ?_, ?_, ?_⟩
    · refine Submodule.sum_mem _ fun l hl => Submodule.sum_mem _ fun j _ => ?_
      have hl' : l ∉ Q := by simpa using hl
      exact single_mem M _ (hTcard l hl' j) (Submodule.smul_of_tower_mem _ _ (hgM l j))
    · intro s hs
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' : l ∉ Q := by simpa using hl
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : s ≠ (insert l Q).erase (e j) := by
        rintro rfl
        apply hs
        rw [hTQ l hl' j, Finset.card_erase_of_mem (hQmem j), hcard]
        have : 1 ≤ d := by
          rw [← hcard]
          exact Finset.card_pos.2 ⟨_, hQmem j⟩
        omega
      exact Pi.single_eq_of_ne this _
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [wd_single, map_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l ∉ Q := by simpa using hl
        have hlc : l ∈ Qᶜ := hl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [hterm l hl']
        rw [← hsum]
        congr 1
        have hw : wOn Qᶜ (fun l => act (r l)) l m = ∑ j, act (r (e j)) (g l j) := by
          simpa [wOn, hl'] using hg l
        rw [hw, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, smul_smul, mul_comm, mul_assoc, GlobalTheory.cubeSign_mul_self, mul_one]
  obtain ⟨c, hc, hlev⟩ := gl2 κ E (fun _ => M) (fun l => act (r l)) Q d d wok qex
    (Pi.single Q m) (single_mem M _ hcard hm)
    (by
      intro s hs
      have : s ≠ Q := by
        rintro rfl
        simp [hcard] at hs
      exact Pi.single_eq_of_ne this _)
    (by
      rw [wd_single]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : i ∉ Q := by simpa using hi
      simp [wOn, this])
    hy
  refine ⟨c, hc, ?_⟩
  have h := hlev Q (by simp [hcard])
  rw [hQ] at h
  have h' : c (img e) - (Pi.single (img e) m : Finset κ → E) (img e) = 0 := h
  simpa [sub_eq_zero] using h'

end UpperTheory.Gal.productCup_of_system

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMuSpan
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma muSpan_base {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (R : Subalgebra ℂ S) (i j a : Fin (d + 1)) :
    InSp R (fun t => T.r n11 T.mu i j (dj j t)) (T.r n11 T.mu i j (toLex (a, j))) := by
  by_cases h : a = j
  · subst h
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    simp [Sys.r, Sys.mu, mul_comm]
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
    refine ⟨Pi.single t 1, fun l => ?_, ?_⟩
    · by_cases hl : l = t
      · subst hl
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hl] using R.zero_mem
    · rw [Finset.sum_eq_single t]
      · simp only [Pi.single_eq_same, one_mul]
        rfl
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact absurd (Finset.mem_univ t) hb

private lemma muSpan_rel {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (i j : Fin (d + 1)) (l : Mi d) :
    T.r n11 T.mu i j l =
      ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).1, j)) -
      ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).2, j)) := by
  have hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j := fun _ => by simp [Sys.u, n11]
  simp only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]
  linear_combination (-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) *
    ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv

theorem UpperTheory.Gal.productCup_of_system.muSpan_of :
    MuSpan := by
  intro d S E _ _ _ _ T hT I J i hi j hj l
  have hI : I.Nonempty := ⟨i, hi⟩
  obtain ⟨p, hp, hp'⟩ := muSpan_base T (T.R I J) i j (ofLex l).1
  obtain ⟨q, hq, hq'⟩ := muSpan_base T (T.R I J) i j (ofLex l).2
  have hb := hT.memY I J hI j hj (ofLex l).2
  have ha := hT.memY I J hI j hj (ofLex l).1
  refine ⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t -
    ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩
  · exact sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))
  · rw [muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
end

