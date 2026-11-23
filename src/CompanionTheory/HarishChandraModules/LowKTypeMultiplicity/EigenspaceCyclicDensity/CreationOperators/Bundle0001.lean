module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0018
public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreApply
section
open Finset

noncomputable section

namespace CompanionTheory.D.LK.Car

variable {n : ℕ}

theorem key_inj {i j : Pos n} (h : key i = key j) : i = j := by
  unfold key at h
  have hi := i.1.2.2
  have hj := j.1.2.2
  have hn : 0 < n := by omega
  have h2 : (i.1.2 : ℕ) = j.1.2 := by
    have := congrArg (· % n) h
    simpa [Nat.mul_add_mod_of_lt hi, Nat.mul_add_mod_of_lt hj] using this
  have h1 : (i.1.1 : ℕ) = j.1.1 := by
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel h)
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))

def tw (i j : Pos n) : ℂ := if key j < key i then -1 else 1

theorem tw_self (i : Pos n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Pos n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Pos n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : key i ≠ key j := fun e => h (key_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : Pos n) (A : Finset (Pos n)) : sg i A * sg i A = 1 := by
  unfold sg
  rw [← mul_pow]; simp

theorem sg_insert (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∉ A) :
    sg i (insert j A) = tw i j * sg i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : Pos n) {j : Pos n} {A : Finset (Pos n)} (h : j ∈ A) :
    sg i (A.erase j) = tw i j * sg i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    ann i x A = if i ∈ A then 0 else sg i A • x (insert i A) := rfl

theorem cre_apply (i : Pos n) (x : Cn n V) (A : Finset (Pos n)) :
    cre i x A = if i ∈ A then sg i A • x (A.erase i) else 0 := rfl

theorem ann_ann (i j : Pos n) : (ann i * ann j + ann j * ann i : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    ann_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem cre_cre (i j : Pos n) : (cre i * cre j + cre j * cre i : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    cre_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

theorem ann_cre (i j : Pos n) :
    (ann i * cre j + cre j * ann i : Module.End ℂ (Cn n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, ann_apply, cre_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sg i A * (-tw i j * sg j A) + sg j A * (tw i j * sg i A) = 0 := by ring
  rw [this, zero_smul]

end CompanionTheory.D.LK.Car
end
end

-- bundled from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
section
open Finset

noncomputable section

namespace CompanionTheory.D.LK

open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq term_le normSq_le pair_lt abs_sig rho_eq)
open PI.UpqRep

variable {n : ℕ}

def ind (A : Finset (Pos n)) (a b : Fin n) : ℝ := ∑ i ∈ A, if i.1 = (a, b) then 1 else 0

theorem ind_eq (A : Finset (Pos n)) (a b : Fin n) :
    ind A a b = if h : a < b then (if (⟨(a, b), h⟩ : Pos n) ∈ A then 1 else 0) else 0 := by
  unfold ind
  split_ifs with h h1
  · rw [Finset.sum_eq_single_of_mem _ h1 fun i _ hi => if_neg fun e => hi (Subtype.ext e), if_pos rfl]
  · exact Finset.sum_eq_zero fun i hi => if_neg fun e => h1 ((Subtype.ext e : i = ⟨(a, b), h⟩) ▸ hi)
  · exact Finset.sum_eq_zero fun i _ => if_neg fun e => h (by have := i.2; rwa [e] at this)

theorem wt_eq (A : Finset (Pos n)) (c : Fin n) : wt A c = ∑ b, (ind A c b - ind A b c) := by
  rw [Finset.sum_sub_distrib]
  unfold wt ind
  rw [Finset.sum_comm, Finset.sum_comm (s := univ), card_filter, card_filter, Nat.cast_sum, Nat.cast_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · simp only [Prod.ext_iff, ite_and]
    split_ifs <;> simp
  · simp only [Prod.ext_iff, ite_and, Finset.sum_ite_eq, mem_univ, if_true]
    split_ifs <;> simp

def sc (ε : Fin n → Bool) (a b : Fin n) : ℝ := if ε a = ε b then sig a b else 0

theorem sc_anti (ε : Fin n → Bool) (a b : Fin n) : sc ε b a = -sc ε a b := by
  unfold sc
  by_cases h : ε a = ε b
  · rw [if_pos h, if_pos h.symm, sig_anti]
  · rw [if_neg h, if_neg (Ne.symm h), neg_zero]

theorem rhoC_eq (ε : Fin n → Bool) (a : Fin n) : rhoC ε a = (∑ b, sc ε a b) / 2 := by
  unfold rhoC
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sc sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]

theorem exists_sort (ε : Fin n → Bool) (κ : Fin n → ℝ) : ∃ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) ∧
    ∀ a b, a < b → ε a = ε b → κ (w b) ≤ κ (w a) := by
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (univ.filter fun w : Equiv.Perm (Fin n) => ∀ c, ε (w c) = ε c)
    (fun w => ∑ c, κ (w c) * ((c : ℕ) : ℝ)) ⟨1, by simp⟩
  have hw' := (mem_filter.1 hw).2
  refine ⟨w, hw', fun a b hab h => ?_⟩
  have := hmin (w * Equiv.swap a b) (mem_filter.2 ⟨mem_univ _, fun c => by
    rw [Equiv.Perm.mul_apply, hw', Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl⟩)
  have e : ∑ c, κ ((w * Equiv.swap a b) c) * ((c : ℕ) : ℝ) - ∑ c, κ (w c) * ((c : ℕ) : ℝ) =
      (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem a b (mem_univ _) (mem_univ _) hab.ne]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]; ring
    · intro c _ hc
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]
  have hp : (0 : ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := sub_pos.2 (by exact_mod_cast hab)
  have : 0 ≤ (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by rw [← e]; linarith
  linarith [nonneg_of_mul_nonneg_left this hp]

theorem K_type_count : NumK := by
  intro n ε lam ν B C hl hB hBn hC _ hdom hn
  set κ := lowK ε lam + rhoC ε - wt B with hκ
  set μ := lowK ε lam + (2 : ℝ) • rhoC ε - wt B - wt C with hμ
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  obtain ⟨m, hm, hm2⟩ := hdom w hw
  have i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a := by
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a) := fun a => by
      have := congrFun hm2 a
      simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← mul_sub, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun d _ => ?_
    rw [← Finset.mul_sum]
    by_cases h0 : m c d = 0
    · simp [h0]
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      simp only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]
      exact hs c d (hm c d h0).1 (hm c d h0).2
  let tC : Fin n → Fin n → ℝ := fun a b => 2 * (ind C a b - ind C b a) - sc ε a b
  have htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0 := fun a b => by
    simp only [tC, ind_eq, sc, sig]
    rcases lt_trichotomy a b with h | h | h
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h]
      by_cases h1 : (⟨(a, b), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := hC _ h1
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
    · subst h; simp
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]
      by_cases h1 : (⟨(b, a), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := (hC _ h1).symm
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
  have i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a := by
    have p1 := pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ
    have p2 := pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)
    have e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2 := fun a => by
      simp only [tC]
      rw [wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]
      ring
    simp only [e]
    simp only [rhoC_eq]
    have : ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b)) := by
      calc _ ≤ ∑ a, ∑ b, (if ε a = ε b then 1 else 0) * |κ a - κ b| :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (le_abs_self _).trans (by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))
        _ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by
            rw [← Equiv.sum_comp w]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Equiv.sum_comp w]
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hw, hw, sc, sig]
            by_cases h : ε a = ε b
            · rcases lt_trichotomy a b with h1 | h1 | h1
              · simp [h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]
              · simp [h1]
              · simp [h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]
            · simp [h]
    linarith
  have hκw : ∀ a, κ (w a) = ν a + rhoC ε a := by
    have e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a) := by
      rw [Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a := Equiv.sum_comp w fun a => κ a * κ a
    have e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a -
        2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a := hn
    have h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => hBn _ h2 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hne : t c d = -sig c d := by
    have h1 : ¬ε c = ε d := hBn _ hi
    have hcd' : c < d := hcd
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have j1 := pair_lt t ta tb' hl c d (ne_of_lt hcd) hne
  have j2 := normSq_le t ta tb'
  have f1 : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = lam a + (∑ b, t a b) / 2 := fun a => by
    have h1 := hκw (w.symm a)
    have h2 := rho_eq ε a
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    simp only [hκ, lowK, Equiv.apply_symm_apply, Pi.add_apply, Pi.sub_apply] at h1
    simp only [t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b), Finset.sum_sub_distrib (f := fun b => sig a b),
      ← Finset.mul_sum]
    linarith
  have f2 : ∀ a, (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold vNormSq nsq dot
  rw [← Equiv.sum_comp w.symm]
  simp only [f1, f2]
  rw [ex, ex]
  linarith

end CompanionTheory.D.LK
end
end

-- bundled from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.RhoSurj
section
noncomputable section

namespace GlobalTheory.CompanionTheory.LKDens

open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem burnside {A : Type} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hnt : Nontrivial V) (hirr : ∀ W : Submodule ℂ V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  classical
  letI : Module A V := Module.compHom V (ρ : A →+* Module.End ℂ V)
  have hsm : ∀ (a : A) (x : V), a • x = ρ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A V := ⟨fun c a x => by simp [hsm]⟩
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun W => ?_ }
    rcases hirr (W.restrictScalars ℂ) (fun a w hw => W.smul_mem a hw) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 h
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  intro f
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ V
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).symm

def rho (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ L :=
  FreeAlgebra.lift ℂ fun p => if h : ε p.1 = ε p.2 then (E p.1 p.2).restrict (hL p.1 p.2 h) else 0

def psi (ε : Fin n → Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if ε p.1 = ε p.2 then FreeAlgebra.ι ℂ p else 0

theorem ev_psi (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    (r : FreeAlgebra ℂ (Fin n × Fin n)) : ∀ s : L, ev E (psi ε r) s = (rho ε E L hL r s : V) := by
  induction r using FreeAlgebra.induction with
  | grade0 c => intro s; simp [Module.algebraMap_end_apply]
  | grade1 p =>
    intro s
    by_cases h : ε p.1 = ε p.2
    · simp [psi, rho, ev, h]
    · simp [psi, rho, ev, h]
  | mul a b ha hb => intro s; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro s; simp [map_add (f := _), ha, hb]

theorem rho_surj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    [FiniteDimensional ℂ L] {v : V} (hv : v ≠ 0) (hvL : v ∈ L)
    (hirr : ∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) : Function.Surjective (rho ε E L hL) := by
  refine burnside (rho ε E L hL) ⟨⟨v, hvL⟩, 0, fun h => hv (congrArg Subtype.val h)⟩ ?_
  intro W hW
  have hst : KStab ε E (W.map L.subtype) := by
    rintro a b hab _ ⟨w, hw, rfl⟩
    refine ⟨rho ε E L hL (FreeAlgebra.ι ℂ (a, b)) w, hW _ w hw, ?_⟩
    simp [rho, hab]
  rcases hirr _ (Submodule.map_subtype_le L W) hst with h | h
  · left
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h
  · right
    apply Submodule.map_injective_of_injective L.injective_subtype
    simpa using h

theorem dens : CompanionTheory.D.LK.Dens := by
  intro n ε V _ _ E μ v L _ _ hv hvL _ hfd hL hirr _
  have hs := rho_surj ε E L hL hv hvL hirr
  let b := Module.finBasis ℂ L
  constructor
  · intro x hx
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
      (show (⟨v, hvL⟩ : L) ≠ 0 from fun h => hv (congrArg Subtype.val h))
    obtain ⟨r, hr⟩ := hs (f.smulRight (⟨x, hx⟩ : L))
    refine ⟨psi ε r, ?_⟩
    have := ev_psi ε E L hL r ⟨v, hvL⟩
    rw [hr] at this
    simpa [hf] using this
  · intro φ hφ
    choose u hu using fun i => hφ (b i)
    choose r hr using fun i => hs ((b.coord i).smulRight (⟨v, hvL⟩ : L))
    refine ⟨∑ i, u i * psi ε (r i), fun s => ?_⟩
    have hu' : ∀ i, ev E (u i) v = φ (b i) := fun i => by simpa using hu i
    conv_rhs => rw [← b.sum_repr s]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, ev_psi ε E L hL, hr, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hu']

end GlobalTheory.CompanionTheory.LKDens
end
end

