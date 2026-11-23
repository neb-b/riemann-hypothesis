module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.PolBridge
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CthMonomial
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Cth

variable {K : Type} [Field K] {σ : Type}

def cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial (Finsupp.single v n) (1 : K) * divDer (Finsupp.single v n) F

theorem coeff_cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cth v n F) μ = AddMonoidAlgebra.coeff F μ * (((μ v).choose n : ℕ) : K) := by
  unfold cth
  rw [eig_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Finsupp.prod_single_index (by simp)]

theorem cth_add (v : σ) (n : ℕ) (F G : MvPolynomial σ K) : cth v n (F + G) = cth v n F + cth v n G := by
  ext μ
  simp only [coeff_cth, MvPolynomial.coeff_add, add_mul]

theorem cth_smul (v : σ) (n : ℕ) (c : K) (F : MvPolynomial σ K) : cth v n (c • F) = c • cth v n F := by
  ext μ
  simp only [coeff_cth, coeff_smul, smul_eq_mul, mul_assoc]

def cthL (v : σ) (n : ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K where
  toFun := cth v n
  map_add' := cth_add v n
  map_smul' := cth_smul v n

theorem cth_monomial (v : σ) (n : ℕ) (e : σ →₀ ℕ) (c : K) :
    cth v n (monomial e c) = monomial e (c * (((e v).choose n : ℕ) : K)) := by
  classical
  ext μ
  rw [coeff_cth, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

theorem cth_zero (v : σ) (F : MvPolynomial σ K) : cth v 0 F = F := by
  ext μ
  simp [coeff_cth]

theorem cth_mul (v : σ) (n : ℕ) (F G : MvPolynomial σ K) :
    cth v n (F * G) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, cth v ab.1 F * cth v ab.2 G := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' =>
    rw [add_mul, cth_add, hF, hF', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, add_mul]
  | monomial e c =>
    induction G using MvPolynomial.induction_on' with
    | add G G' hG hG' =>
      rw [mul_add, cth_add, hG, hG', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, mul_add]
    | monomial e' c' =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [monomial_mul, cth_monomial, Finsupp.add_apply, Nat.add_choose_eq, Nat.cast_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [cth_monomial, cth_monomial, monomial_mul]
      congr 1
      push_cast
      ring

theorem cth_free (v : σ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) {n : ℕ} (hn : n ≠ 0) :
    cth v n F = 0 := by
  ext μ
  rw [coeff_cth]
  change F.coeff μ * (((μ v).choose n : ℕ) : K) = 0
  by_cases h : μ ∈ F.support
  · rw [hF μ h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hn)]
    simp
  · rw [notMem_support_iff.1 h, zero_mul]

theorem cth_mul_free (v : σ) (n : ℕ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) (G : MvPolynomial σ K) :
    cth v n (F * G) = F * cth v n G := by
  classical
  rw [cth_mul, Finset.sum_eq_single (0, n)]
  · rw [cth_zero]
  · rintro ⟨a, b⟩ hab hne
    have ha : a ≠ 0 := by
      rintro rfl
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      simp only [zero_add] at hab
      exact hne (by rw [hab])
    rw [cth_free v hF ha, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem cth_pow (v : σ) {E m : MvPolynomial σ K} (h1 : cth v 1 E = m) (h2 : ∀ a, 2 ≤ a → cth v a E = 0) (j l : ℕ) :
    cth v l (E ^ j) = ((j.choose l : ℕ) : K) • (E ^ (j - l) * m ^ l) := by
  classical
  induction j generalizing l with
  | zero =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero]
    · rw [pow_zero, Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_smul]
      refine cth_free v ?_ hl.ne'
      intro μ hμ
      have : μ = 0 := by
        by_contra hne
        rw [mem_support_iff, coeff_one, if_neg (Ne.symm hne)] at hμ
        exact hμ rfl
      rw [this]; rfl
  | succ j ih =>
    rw [pow_succ, cth_mul]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero, pow_succ]
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hsub : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (l' + 1), ab ≠ (l' + 1, 0) → ab ≠ (l', 1) →
          cth v ab.1 (E ^ j) * cth v ab.2 E = 0 := by
        rintro ⟨a, b⟩ hab hn1 hn2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        simp only at hab
        have hb : 2 ≤ b := by
          by_contra hb
          have : b = 0 ∨ b = 1 := by omega
          rcases this with rfl | rfl
          · exact hn1 (by simp at hab; rw [hab])
          · exact hn2 (by have : a = l' := by omega
                          rw [this])
        rw [h2 b hb, mul_zero]
      have hne : ((l' + 1, 0) : ℕ × ℕ) ≠ (l', 1) := by simp
      rw [← Finset.sum_subset (s₁ := {(l' + 1, 0), (l', 1)})
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal])
        (by
          intro x hx hx'
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
          exact hsub x hx hx'.1 hx'.2),
        Finset.sum_pair hne]
      simp only
      rw [ih, ih, cth_zero, h1, Nat.choose_succ_succ' j l']
      by_cases hlj : l' + 1 ≤ j
      · have e1 : j + 1 - (l' + 1) = (j - (l' + 1)) + 1 := by omega
        have e2 : j - l' = (j - (l' + 1)) + 1 := by omega
        rw [e1, e2]
        push_cast
        simp only [smul_eq_C_mul, pow_succ, map_add (f := _)]
        ring
      · have e0 : j.choose (l' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e1 : j + 1 - (l' + 1) = j - l' := by omega
        rw [e0, e1]
        simp only [Nat.cast_zero, zero_smul, zero_mul, zero_add, add_zero, smul_eq_C_mul, pow_succ]
        ring

end Cth

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symVar_inj (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    Function.Injective (symVar C0 CE1 CE2 X j) := by
  rintro (⟨a, c⟩ | ⟨l, b⟩) (⟨a', c'⟩ | ⟨l', b'⟩) h
  · simp only [symVar] at h
    have ha2 := a.2
    have ha2' := a'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      have e1' : (a : ℕ) / 2 = (a' : ℕ) / 2 := congrArg Fin.val (topOdd_inj X j e1)
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, e3⟩ := h
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2.symm
  · simp only [symVar] at h
    have hl2 := l.2
    have hl2' := l'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, -⟩ := h
      have e1' : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (X.seg C0 CE1 CE2 j).sigma + (l' : ℕ) :=
        congrArg Fin.val (topOdd_inj X j e1)
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, -⟩ := h
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]

theorem symLev_pos (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (v : BV C0 CE1 CE2 X j) :
    0 < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, b⟩
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos

theorem coarse_eval (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (v0 : BV C0 CE1 CE2 X j) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      (symVar C0 CE1 CE2 X j v0) = symLev X.p C0 CE1 CE2 X j v0 * μ v0 := by
  classical
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single v0]
  · simp
  · intro v _ hv
    rw [if_neg fun e => hv (symVar_inj C0 CE1 CE2 X j e)]
  · intro hv
    simp [Finsupp.notMem_support_iff.1 hv]

theorem ioExp_inj (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Function.Injective (ioExp C0 CE1 CE2 X j b) := by
  intro μ μ' h
  unfold ioExp at h
  have h' := add_left_cancel h
  ext v0
  have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
  rw [coarse_eval, coarse_eval] at this
  exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this

theorem ioBlock_monomial (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K] (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (μ : BV C0 CE1 CE2 X j →₀ ℕ) (c : K) :
    ioBlock K X.p C0 CE1 CE2 X j b (monomial μ c) = monomial (ioExp C0 CE1 CE2 X j b μ) c := by
  classical
  have hd : digitMon K C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon K X.p C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have ha : aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v) (monomial μ c) =
      monomial (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) c := by
    rw [aeval_monomial, monomial_finsupp_sum_index]
    congr 1
    refine Finsupp.prod_congr fun v _ => ?_
    rw [← pow_mul, X_pow_eq_monomial]
  unfold ioBlock ioExp baseExp
  rw [hd, hs, ha, monomial_mul, monomial_mul, one_mul, one_mul]

theorem ioFockAt : IoFockAt := by
  intro C0 CE1 CE2 X K _ hp j b u u'
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  exact fock_monoMap f (ioExp C0 CE1 CE2 X j b) (ioExp_inj C0 CE1 CE2 X hp j b)
    (fun μ c => ioBlock_monomial C0 CE1 CE2 X K j b μ c) u u'

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolVariableLowerLetter
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem wh_aeval {K : Type} [CommRing K] {σ τ : Type} (ω : τ → ℕ) (f : σ → τ) (lev : σ → ℕ) (u : MvPolynomial σ K) (n : ℕ)
    (h : IsWeightedHomogeneous (fun v => lev v * ω (f v)) u n) :
    IsWeightedHomogeneous ω (aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u) n := by
  have e : aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u =
      ∑ μ ∈ u.support, aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) (monomial μ (u.coeff μ)) := by
    conv_lhs => rw [← support_sum_monomial_coeff u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [e]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hw : Finsupp.weight (fun v => lev v * ω (f v)) μ = n := h (mem_support_iff.1 hμ)
  have h1 := IsWeightedHomogeneous.prod μ.support (fun v => ((X (f v) : MvPolynomial τ K) ^ lev v) ^ μ v) _
    (fun v _ => ((isWeightedHomogeneous_X K ω (f v)).pow (lev v)).pow (μ v))
  have h2 := (isWeightedHomogeneous_C ω (u.coeff μ)).mul h1
  refine wh_congr h2 ?_
  rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul]

theorem sum_chain {s : ℕ} (f : Fin (2 * s + 1) → ℕ) :
    ∑ a, f a = ∑ i : Fin s, (f ⟨2 * i.val, by omega⟩ + f ⟨2 * i.val + 1, by omega⟩) + f ⟨2 * s, by omega⟩ := by
  let F : ℕ → ℕ := fun k => if h : k < 2 * s + 1 then f ⟨k, h⟩ else 0
  have e1 : ∑ a, f a = ∑ k ∈ Finset.range (2 * s + 1), F k := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F]
    rw [dite_eq_left a.2]
  have e2 : ∀ n, ∑ k ∈ Finset.range (2 * n + 1), F k = ∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1)) + F (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  rw [e1, e2 s, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    simp only [F]
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  · simp only [F]
    rw [dite_eq_left (by omega)]

theorem sum_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) :
    ∑ l : Fin S.t, g (uTop S l) = ∑ i : Fin s, if S.sigma ≤ i.val then g i else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    apply Fin.ext
    have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have := i.2
    exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
      Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩

section Sym

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

theorem sv_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) = ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
  simp only [symVar]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem sl_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  simp only [symLev]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem symbol_variable_last (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = ((topEnd X j, !β), 0) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_level_last (β : Bool) : symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_variable_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, true), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  have e2 : decide ((2 * i.val) % 2 = 0) = true := by simp
  show ((topOdd X j ⟨(2 * i.val) / 2, _⟩, decide ((2 * i.val) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem symbol_level_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val) / 2, _⟩ = _
  rw [e1]

theorem sv_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, false), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  have e2 : decide ((2 * i.val + 1) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]
    omega
  show ((topOdd X j ⟨(2 * i.val + 1) / 2, _⟩, decide ((2 * i.val + 1) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem sl_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val + 1) / 2, _⟩ = _
  rw [e1]

theorem sv_U (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topEnd X j, true), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]
  show ((topEnd X j, decide (2 * segS X.TT j = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_U (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]

theorem sv_xi (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = ((topEnd X j, false), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]
  show ((topEnd X j, decide (2 * segS X.TT j + 1 = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_xi (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
end
end

