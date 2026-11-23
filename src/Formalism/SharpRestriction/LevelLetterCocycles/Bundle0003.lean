module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.PadicValNatFactorialSucc
section
namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

theorem padicValNat_factorial_succ (p : ℕ) [Fact p.Prime] (M : ℕ) :
    padicValNat p (M + 1).factorial = padicValNat p M.factorial + padicValNat p (M + 1) := by
  rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.add_one_ne_zero M) (Nat.factorial_ne_zero M)]
  omega

theorem padicValNat_sum_Ioc_add_factorial (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    ∑ k ∈ Finset.Ioc K M, padicValNat p k + padicValNat p K.factorial = padicValNat p M.factorial := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM, padicValNat_factorial_succ]
    omega

theorem digits_sum_le_log (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (p.digits K).sum ≤ (p - 1) * (Nat.log p K + 1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p.digits K).sum ≤ (p.digits K).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits K) (p - 1) (fun x hx => by
      have := Nat.digits_lt_base hp.one_lt hx
      omega)
    simpa using this
  have h2 : (p.digits K).length ≤ Nat.log p K + 1 := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [Nat.length_digits p K hp.one_lt hK.ne']
  calc (p.digits K).sum ≤ (p.digits K).length * (p - 1) := h1
    _ ≤ (Nat.log p K + 1) * (p - 1) := Nat.mul_le_mul h2 (le_refl _)
    _ = (p - 1) * (Nat.log p K + 1) := Nat.mul_comm _ _

theorem padicValNat_sum_Ioc_le (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k ≤ M - K + (p.digits K).sum := by
  have h2 := padicValNat_sum_Ioc_add_factorial p K M h
  have hM : (p - 1) * padicValNat p M.factorial = M - (p.digits M).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := M) (Fact.out : p.Prime))
  have hK : (p - 1) * padicValNat p K.factorial = K - (p.digits K).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := K) (Fact.out : p.Prime))
  have sM := Nat.digit_sum_le p M
  have sK := Nat.digit_sum_le p K
  have e : (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k + (p - 1) * padicValNat p K.factorial =
      (p - 1) * padicValNat p M.factorial := by
    rw [← Nat.mul_add, h2]
  omega

theorem padicValInt_sum_le_Ioc (p : ℕ) (Y : Finset ℤ) (K M : ℕ) (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    ∑ x ∈ Y, padicValInt p x ≤ ∑ k ∈ Finset.Ioc K M, padicValNat p k := by
  have e : ∑ k ∈ Y.image Int.natAbs, padicValNat p k = ∑ x ∈ Y, padicValInt p x :=
    by
      simpa only [padicValInt, Nat.padicValNat_def] using
        (Finset.sum_image (f := fun k => padicValNat p k) (by intro x hx y hy hxy; exact hinj x hx y hy hxy))
  rw [← e]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  rw [Finset.mem_Ioc]
  exact hY x hx

private theorem sub_one_mul_sum_padicValInt_le_sub_add_digits_sum (p : ℕ) [Fact p.Prime] (Y : Finset ℤ) (K M : ℕ) (h : K ≤ M)
    (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    (p - 1) * ∑ x ∈ Y, padicValInt p x ≤ M - K + (p.digits K).sum :=
  le_trans (Nat.mul_le_mul (le_refl _) (padicValInt_sum_le_Ioc p Y K M hY hinj))
    (padicValNat_sum_Ioc_le p K M h)

theorem padicValInt_sum_le (p : ℕ) [Fact p.Prime] (bb S η a : ℕ) (hab : a + η < bb) (X : Finset ℤ)
    (hX : ∀ x ∈ X, x ≠ 0 ∧ ((1 - ((bb + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - bb) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ)))) :
    (p - 1) * ∑ x ∈ X, padicValInt p x ≤
      2 * a + 2 * η + S + (p - 1) * (Nat.log p (bb - a - 1) + 1) := by
  have e1 : ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x = ∑ x ∈ X, padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not X (fun x => x ≤ (a : ℤ) - bb) (padicValInt p)
  have e2 : ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x =
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not _ (fun x => 0 < x) (padicValInt p)
  have b1 : (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x ≤
      (bb + S - 1) - (bb - a - 1) + (p.digits (bb - a - 1)).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hx' := hX x hx.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b2 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x),
      padicValInt p x ≤ (η + a) - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b3 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
      padicValInt p x ≤ η - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      have hx' := hX x hx.1.1
      have hy' := hX y hy.1.1
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have z : (p.digits 0).sum = 0 := by simp
  have d := digits_sum_le_log p (bb - a - 1)
  have total : (p - 1) * ∑ x ∈ X, padicValInt p x =
      (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
        padicValInt p x := by
    rw [← e1, ← e2]
    ring
  omega

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StageStep
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrA

variable {K : Type*} [Field K] {d : ℕ}

def PiLocalization₂ (G : ℤ → Submodule K (Fin d → K)) (hi u : ℤ) : Prop :=
  ∃ (S : Set (Fin d → K)) (ℓ : (Fin d → K) → ℤ), LinearIndepOn K id S ∧
    (∀ x ∈ S, x ∈ G (ℓ x) ∧ u ≤ ℓ x ∧ ℓ x ≤ hi) ∧ S ⊆ G u ∧
    ∀ u', u ≤ u' → u' ≤ hi → G u' ≤ Submodule.span K {x | x ∈ S ∧ u' ≤ ℓ x}

theorem stage_top (G : ℤ → Submodule K (Fin d → K)) (hi : ℤ) : PiLocalization₂ G hi hi := by
  unfold PiLocalization₂
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K (G hi : Set (Fin d → K))
  refine ⟨b, fun _ => hi, hli, fun x hx => ⟨hbt hx, le_rfl, le_rfl⟩, hbt, ?_⟩
  intro u' h1 h2 v hv
  have hsub : b ⊆ {x | x ∈ b ∧ u' ≤ (fun _ => hi) x} := fun x hx => ⟨hx, h2⟩
  refine Submodule.span_mono hsub ?_
  rw [hspan, Submodule.span_eq]
  rwa [← le_antisymm h2 h1]

theorem stage_step (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi u : ℤ) (hu : u < hi)
    (h : PiLocalization₂ G hi (u + 1)) : PiLocalization₂ G hi u := by
  unfold PiLocalization₂ at h ⊢
  obtain ⟨S, ℓ, hli, hmem, hSG, hspan⟩ := h
  have hSu : S ⊆ (G u : Set (Fin d → K)) := fun x hx => hG (by omega : u ≤ u + 1) (hSG hx)
  obtain ⟨b, hbt, hSb, htb, hlib⟩ := exists_linearIndepOn_id_extension hli hSu
  refine ⟨b, fun x => if x ∈ S then ℓ x else u, hlib, ?_, hbt, ?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, h3⟩ := hmem x hxS
      simp only [hxS, if_true]
      exact ⟨h1, by omega, h3⟩
    · simp only [hxS, if_false]
      exact ⟨hbt hx, le_rfl, hu.le⟩
  · intro u' h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · intro v hv
      have hsub : b ⊆ {x | x ∈ b ∧ u ≤ (fun x => if x ∈ S then ℓ x else u) x} := by
        intro x hx
        refine ⟨hx, ?_⟩
        by_cases hxS : x ∈ S
        · have h3 := (hmem x hxS).2.1
          simp only [hxS, if_true]
          omega
        · simp only [hxS, if_false]
          exact le_rfl
      exact Submodule.span_mono hsub (htb hv)
    · refine (hspan u' (by omega) h2).trans (Submodule.span_mono ?_)
      rintro x ⟨hxS, hx⟩
      exact ⟨hSb hxS, by simpa [hxS] using hx⟩

theorem stage_all (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi : ℤ) :
    ∀ u ≤ hi, PiLocalization₂ G hi u := by
  have key : ∀ k : ℕ, PiLocalization₂ G hi (hi - k) := by
    intro k
    induction k with
    | zero => simpa using stage_top G hi
    | succ k ih =>
      refine stage_step G hG hi (hi - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_
      have e : hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - (k : ℤ) := by push_cast; ring
      rw [e]
      exact ih
  intro u hu
  have h := key (hi - u).toNat
  rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

theorem adapted (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (lo hi : ℤ) (hlh : lo ≤ hi)
    (hlo : G lo = ⊤) :
    ∃ (I : ℕ) (P : Fin I → Fin d → K) (Q : Fin I → Fin d → K) (h : Fin I → ℤ),
      (∀ c : Fin d → K, c = ∑ i, (∑ m, Q i m * c m) • P i) ∧
      (∀ i, P i ∈ G (h i)) ∧ (∀ i, lo ≤ h i ∧ h i ≤ hi) ∧
      ∀ u : ℤ, u ≤ hi → ∀ c ∈ G u, ∀ i, h i < u → ∑ m, Q i m * c m = 0 := by
  obtain ⟨S, ℓ, hli, hmem, _, hspan⟩ := stage_all G hG hi lo hlh
  have hfin : S.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  have := hfin.fintype
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → Fin d → K)) := by
    rw [Subtype.range_coe, ← hlo]
    exact (hspan lo le_rfl hlh).trans (Submodule.span_mono fun x hx => hx.1)
  let B0 : Module.Basis S K (Fin d → K) := Module.Basis.mk (v := ((↑) : S → Fin d → K)) hli hsp
  let e := Fintype.equivFin S
  let B := B0.reindex e
  have hB : ∀ i, B i = ((e.symm i : S) : Fin d → K) := fun i => by
    simp only [B, B0, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply hli hsp (e.symm i)
  have hQ : ∀ (c : Fin d → K) i, ∑ m, B.repr (Pi.single m 1) i * c m = B.repr c i := by
    intro c i
    conv_rhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hs : (Pi.single m (c m) : Fin d → K) = c m • Pi.single m 1 := by
      ext j
      by_cases hj : j = m
      · subst hj
        simp
      · simp [hj]
    rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨Fintype.card S, fun i => B i, fun i m => B.repr (Pi.single m 1) i, fun i => ℓ (B i),
    ?_, ?_, ?_, ?_⟩
  · intro c
    simp only [hQ]
    exact (B.sum_repr c).symm
  · intro i
    show B i ∈ G (ℓ (B i))
    rw [hB]
    exact (hmem _ (e.symm i).2).1
  · intro i
    show lo ≤ ℓ (B i) ∧ ℓ (B i) ≤ hi
    rw [hB]
    obtain ⟨_, h1, h2⟩ := hmem _ (e.symm i).2
    exact ⟨h1, h2⟩
  · intro u hu c hc i hi'
    have hi'' : ℓ (B i) < u := hi'
    show ∑ m, B.repr (Pi.single m 1) i * c m = 0
    rw [hQ]
    by_cases hul : u ≤ lo
    · exfalso
      have h1 := (hmem _ (e.symm i).2).2.1
      rw [hB] at hi''
      omega
    · have hcs := hspan u (by omega) hu hc
      have hset : {x | x ∈ S ∧ u ≤ ℓ x} = B '' {j | u ≤ ℓ (B j)} := by
        ext x
        constructor
        · rintro ⟨hxS, hx⟩
          refine ⟨e ⟨x, hxS⟩, ?_, ?_⟩
          · show u ≤ ℓ (B (e ⟨x, hxS⟩))
            rw [hB, Equiv.symm_apply_apply]
            exact hx
          · rw [hB, Equiv.symm_apply_apply]
        · rintro ⟨j, hj, rfl⟩
          exact ⟨by rw [hB]; exact (e.symm j).2, hj⟩
      rw [hset, Module.Basis.mem_span_image] at hcs
      by_contra hne
      have hmemi := hcs (Finsupp.mem_support_iff.2 hne)
      exact absurd (show u ≤ ℓ (B i) from hmemi) (not_le.2 hi'')

end Formalism.MainNotions.UnusedSlot80.CrA
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SumSubEqSumIocOfSub
section
namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Finset

variable (l : ℕ) [hl : Fact l.Prime]

theorem sum_Ioc_zero_eq_factorial (y : ℕ) :
    ∑ m ∈ Ioc 0 y, padicValNat l m = padicValNat l y.factorial := by
  induction y with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero n)]
    ring

theorem padicValNat_factorial_le_div_sub_one (y : ℕ) :
    ((padicValNat l y.factorial : ℕ) : ℝ) ≤ (y : ℝ) / ((l : ℝ) - 1) := by
  have h1 : 1 < l := hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by
    have : (1:ℝ) < l := by exact_mod_cast h1
    linarith
  have key : (l - 1) * padicValNat l y.factorial ≤ y := by
    rw [Nat.padicValNat_def, hl.out.sub_one_mul_multiplicity_factorial]; exact Nat.sub_le _ _
  have key' : (((l - 1 : ℕ) : ℝ)) * (padicValNat l y.factorial : ℝ) ≤ y := by
    exact_mod_cast key
  rw [Nat.cast_sub h1.le, Nat.cast_one] at key'
  rw [le_div_iff₀ hc]; linarith

theorem padicValNat_choose_le_logb' (k n : ℕ) :
    ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ Real.logb l k := by
  have h1 : padicValNat l (k.choose n) ≤ Nat.log l k := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have h2 : ((Nat.log l k : ℕ) : ℝ) ≤ Real.logb l k := by
    first
    | exact Real.natLog_le_logb k l
    | rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
        rw [Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast hk), Real.rpow_natCast]
        exact_mod_cast Nat.pow_log_le_self l hk.ne'
  calc ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ ((Nat.log l k : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l k := h2

theorem sum_Ioc_padicValNat_le_div_sub_one_add_logb (k0 k1 : ℕ) (h : k0 ≤ k1) :
    ((∑ m ∈ Ioc k0 k1, padicValNat l m : ℕ) : ℝ) ≤
      ((k1 - k0 : ℕ) : ℝ) / ((l : ℝ) - 1) + Real.logb l k1 := by
  have hsplit : ∑ m ∈ Ioc 0 k0, padicValNat l m + ∑ m ∈ Ioc k0 k1, padicValNat l m
      = ∑ m ∈ Ioc 0 k1, padicValNat l m :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le k0) h
  rw [sum_Ioc_zero_eq_factorial, sum_Ioc_zero_eq_factorial] at hsplit
  have hA : k1.choose k0 * k0.factorial ≠ 0 :=
    mul_ne_zero (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)
  have hfac : k1.factorial = k1.choose k0 * k0.factorial * (k1 - k0).factorial :=
    (Nat.choose_mul_factorial_mul_factorial h).symm
  rw [hfac, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hA (Nat.factorial_ne_zero _),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)] at hsplit
  have heq : ∑ m ∈ Ioc k0 k1, padicValNat l m
      = padicValNat l (k1.choose k0) + padicValNat l (k1 - k0).factorial := by omega
  rw [heq, Nat.cast_add]
  have h2 := padicValNat_factorial_le_div_sub_one l (k1 - k0)
  have h3 := padicValNat_choose_le_logb' l k1 k0
  linarith

theorem sum_sub_eq_sum_Ioc (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j0 - j ∧ j0 - j ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j0 - j).toNat) (fun m => j0 - (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt, ← Nat.padicValNat_def]
    congr 1
    omega

theorem sum_sub_eq_sum_Ioc_of_sub (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j - j0 ∧ j - j0 ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j - j0).toNat) (fun m => j0 + (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt, ← Nat.padicValNat_def]
    congr 1
    omega

theorem sum_erase_add_sum_le (a b S η h : ℕ) (hb : 2 * a + η ≤ b) (hbh : b ≤ h) (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (j₀ : ℤ) (hj₀ : j₀ ∈ Icc ((b : ℤ) - a + 1) (b : ℤ)) :
    (((∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt l (j₀ - j)) +
        ∑ j ∈ S₂, padicValInt l (j₀ - j) : ℕ) : ℝ) ≤
      (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) + Real.logb l ((h + η : ℕ) : ℝ) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by linarith
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨p, hp⟩ : ∃ p : ℕ, j₀ = (b : ℤ) - p := ⟨((b : ℤ) - j₀).toNat, by omega⟩
  subst hp
  have hpa : p + 1 ≤ a := by omega
  have e1 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e2 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => ¬ j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 p, padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e12 : ∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m + ∑ m ∈ Ioc 0 p, padicValNat l m := by
    rw [← e1, ← e2]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdisj : Disjoint (Icc ((b : ℤ) + 1) ((b : ℤ) + S + a))
      (Icc (1 - (η : ℤ)) ((η : ℤ) + a)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have e3 : ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j) ≤
      ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j) +
      ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j) := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hS₂
  have eA : ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc p (p + S + a), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have eB : ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have ePQ : ∑ m ∈ Ioc 0 p, padicValNat l m + ∑ m ∈ Ioc p (p + S + a), padicValNat l m
      = padicValNat l (p + S + a).factorial := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le p) (by omega : p ≤ p + S + a),
      sum_Ioc_zero_eq_factorial]
  have eR : ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m = padicValNat l (a - 1 - p).factorial :=
    sum_Ioc_zero_eq_factorial l _
  have hN : (∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)) + ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j)
      ≤ padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
        ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    rw [eA, eB] at e3
    rw [e12]
    omega
  have hR := padicValNat_factorial_le_div_sub_one l (a - 1 - p)
  have hP := padicValNat_factorial_le_div_sub_one l (p + S + a)
  have hB := sum_Ioc_padicValNat_le_div_sub_one_add_logb l (b - p - η - a - 1) (b - p + η - 1) (by omega)
  have hx : (0:ℝ) < ((b - p + η - 1 : ℕ) : ℝ) := by
    have : 0 < b - p + η - 1 := by omega
    exact_mod_cast this
  have hxy : ((b - p + η - 1 : ℕ) : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b - p + η - 1 ≤ h + η)
  have hlog : Real.logb l ((b - p + η - 1 : ℕ) : ℝ) ≤ Real.logb l ((h + η : ℕ) : ℝ) := by
    first
    | exact Real.logb_le_logb_of_le hl1 hx hxy
    | exact (Real.logb_le_logb hl1 hx (by linarith)).mpr hxy
  have hnum : ((a - 1 - p : ℕ) : ℝ) + ((p + S + a : ℕ) : ℝ) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) = 3 * (a : ℝ) + S + 2 * η - 1 := by
    have e4 : (b - p + η - 1) - (b - p - η - a - 1) = 2 * η + a := by omega
    have e6 : ((a - 1 - p : ℕ) : ℝ) + 1 + p = a := by
      exact_mod_cast (by omega : a - 1 - p + 1 + p = a)
    rw [e4]
    push_cast
    linarith
  have hdiv : ((a - 1 - p : ℕ) : ℝ) / ((l : ℝ) - 1) + ((p + S + a : ℕ) : ℝ) / ((l : ℝ) - 1) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) / ((l : ℝ) - 1)
      = (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) := by
    rw [← hnum]; ring
  calc _ ≤ ((padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
          ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) :=
        Nat.cast_le.mpr hN
    _ = ((padicValNat l (a - 1 - p).factorial : ℕ) : ℝ) +
          ((padicValNat l (p + S + a).factorial : ℕ) : ℝ) +
          ((∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add]
    _ ≤ _ := by linarith

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
end

