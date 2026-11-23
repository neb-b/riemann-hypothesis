module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpECutOmEquivariant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.CutRow

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

end GlobalTheory.RootEx.CutRow


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.opE_cut_om_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : GL n k), ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c p ⊓ _root_.GlobalTheory.RootEx.N k n c (p + 1), _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ y) = (((_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (ψ (-_root_.GlobalTheory.RootEx.simpleSum u) : ℂ)) • _root_.GlobalTheory.SplitWeil.om μ 1 x (_root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * Φ y)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ ν _ μ χ Φ x u hu
  obtain ⟨huP, huP1⟩ := Subgroup.mem_inf.mp hu
  set cut : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun y =>
    ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0 with hcut
  have hlevi : ∀ (g : GL n k) (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      cut (((_root_.GlobalTheory.RootEx.embX c g : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * y) = cut y := by
    intro g y
    simp only [hcut, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.OpELevi.left_inr]
  have hgen : _root_.GlobalTheory.RootEx.InN p u⁻¹ :=
    _root_.GlobalTheory.RootEx.Model.mem_N_iff.mp (inv_mem huP)
  have hunip : ∀ (x₀ : Matrix n n' k) (e : { rs // _root_.GlobalTheory.RootEx.Free (p + 1) rs } → k),
      cut (((u⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) =
        cut (_root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) := by
    intro x₀ e
    simp only [hcut]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · congr 1
      funext s
      rw [_root_.GlobalTheory.RootEx.TargetUnip.mul_apply_of_inN hgen, Finset.sum_eq_zero, add_zero]
      intro r _
      split_ifs with hlt
      · cases r with
        | inl i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          omega
        | inr i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          rw [_root_.GlobalTheory.RootEx.TargetUnip.affPt_of_not_free]
          · simp [_root_.GlobalTheory.RootEx.basePt]
          · simp [_root_.GlobalTheory.RootEx.Free]
            omega
      · rfl
    · rfl
  have hmul : _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ =
      _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (_root_.GlobalTheory.SplitWeil.om μ 1 u Φ) := by
    have h := _root_.GlobalTheory.SplitWeil.Model.om_mul μ 1 1 (_root_.GlobalTheory.RootEx.embX c x) u Φ
    rwa [one_mul] at h
  have hcomm : ∀ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ,
      (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) Ψ y) =
        _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (fun y => cut y * Ψ y) := by
    intro Ψ
    funext y
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, ← map_inv, hlevi]
    ring
  have hcut_unip : _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 u Φ y) =
      _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (_root_.GlobalTheory.SplitWeil.om μ 1 u (fun y => cut y * Φ y)) := by
    funext x₀
    unfold _root_.GlobalTheory.RootEx.opE
    congr 1
    funext e
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, hunip]
    ring
  rw [hmul, hcomm, (_root_.GlobalTheory.RootEx.opE_om_embX k n n' c (p + 1) (by omega) (by omega) ψ ν μ _).1 x,
    hcut_unip, _root_.GlobalTheory.RootEx.opE_om_target_unipotent k n n' c (p + 1) (by omega) (by omega) ψ ν μ _ u huP1]
  funext y
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
section
open Formalism.REAL Finset

namespace GlobalTheory.CapelliDiff

theorem prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by
  intro n
  induction n with
  | zero =>
    intro x y d h
    simp [h 0]
  | succ n ih =>
    intro x y d h
    rw [List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    have key := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)
    have e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod
        = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.succ).prod) := by
      rw [h 0]; noncomm_ring
    rw [e1, key, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [List.ofFn_succ, List.prod_cons]
      have h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ := by simp [Fin.succ_pos]
      rw [if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]
      have hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) =
          (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ) := by
        congr 1; funext j; simp only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      rw [hl]

theorem Tm_add_one {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add (f := _)]; abel

def extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv k).permCongr τ)

theorem extAt_succAbove {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]

theorem sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

theorem sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by
  let e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a} :=
    ((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]
  · rw [← Equiv.sum_comp e]
    rfl
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h a ha; rw [ha]; exact h
    · intro h; exact h k rfl

theorem qdet_add_one_sub (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ) :
    qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  unfold qdet qminor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have step : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod -
        (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod := by
    intro σ
    rw [prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
      (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]
    · apply Finset.sum_congr rfl
      intro k _
      congr 2
      congr 1
      funext j
      by_cases hj : Fin.castSucc j < k
      · rw [if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]
        simp [Fin.coe_castSucc]
      · rw [if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]
        simp only [id, Fin.val_succ]
        congr 1
        push_cast; ring
    · intro k
      have : u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1 := by ring
      simp only [this, Tm_add_one, id]
  simp_rw [step, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) =
      if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod else 0 := by
    intro σ
    split_ifs <;> simp
  simp_rw [h2]
  rw [sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [sign_extAt, extAt_succAbove]

end GlobalTheory.CapelliDiff

theorem GlobalTheory.qdet_add_one_sub_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem affine_mul_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (d : ℕ) (p q : A) (c : ℕ → A) :
    ∃ c' : ℕ → A, c' (d + 1) = p * c d ∧ ∀ u : ℂ, (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • c' i := by
  refine ⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A)
    + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_polyMap_top {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (p q : Fin t → A) :
    ∃ c : ℕ → A, c t = (List.ofFn p).prod ∧ ∀ u : ℂ, (List.ofFn fun k => u • p k + q k).prod
      = ∑ i ∈ range (t + 1), u ^ i • c i := by
  induction t with
  | zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩
  | succ t ih =>
    obtain ⟨c, hct, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    obtain ⟨c', hct', hc'⟩ := affine_mul_polyMap_top t (p 0) (q 0) c
    refine ⟨c', ?_, fun u => ?_⟩
    · rw [hct', hct, List.ofFn_succ, List.prod_cons]
    · rw [List.ofFn_succ, List.prod_cons, hc u, hc' u]

theorem qdet_polyMap_monic (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  have h : ∀ σ : Equiv.Perm (Fin n), ∃ c : ℕ → A,
      c n = (List.ofFn fun k : Fin n => if σ k = k then (1 : A) else 0).prod ∧ ∀ u : ℂ,
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (n + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hct, hc⟩ := prod_affine_polyMap_top n
      (fun k => if σ k = k then (1 : A) else 0)
      (fun k => Tm E (-(k : ℂ)) (σ k) k)
    refine ⟨c, hct, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Tm
    simp only [id]
    split_ifs
    · rw [← add_assoc, ← Algebra.algebraMap_eq_smul_one, ← map_add (f := _)]
      congr 2
      all_goals ring
    · simp
  choose c hct hc using h
  have htop : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 → c σ n = 0 := by
    intro σ hσ
    rw [hct σ]
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext hne)
    apply List.prod_eq_zero
    rw [List.mem_ofFn]
    exact ⟨k, if_neg hk⟩
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [hct 1]
      simp
    · intro σ _ hσ
      rw [htop σ hσ, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  · unfold qdet qminor
    simp only [hc, mul_sum, smul_sum, mul_smul_comm]
    exact sum_comm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [DecidableEq a] [DecidableEq b] in
theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ



end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverse
section
open Formalism.REAL Finset

namespace GlobalTheory.TracedComatrix

theorem epow_succ_left {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) :
    ∀ (k : ℕ) (a b : Fin n), epow E (k + 1) a b = ∑ c, E a c * epow E k c b := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [epow]
  | succ k ih =>
    intro a b
    calc epow E (k + 1 + 1) a b = ∑ c, epow E (k + 1) a c * E c b := rfl
      _ = ∑ c, (∑ d, E a d * epow E k d c) * E c b :=
          Finset.sum_congr rfl fun c _ => by rw [ih a c]
      _ = ∑ d, E a d * ∑ c, epow E k d c * E c b := by
          simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ d, E a d * epow E (k + 1) d b := rfl

theorem key {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (N : ℕ)
    (j i : Fin n) :
    ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i =
      algebraMap ℂ A (x ^ (N + 1)) * (if j = i then 1 else 0) +
        algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i := by
  have h1 : ∀ k, ∑ l, Tm E x j l * epow E k l i = algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i := by
    intro k
    rw [epow_succ_left]
    simp [Tm, add_mul, Finset.sum_add_distrib, ite_mul]
  have h2 : ∑ l, Tm E x j l * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * epow E k l i
      = ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) * ∑ l, Tm E x j l * epow E k l i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
  rw [h2]
  simp_rw [h1]
  set a : ℕ → A := fun k => algebraMap ℂ A ((-1) ^ k * x ^ (N + 1 - k)) * epow E k j i with ha
  have h3 : ∀ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * x ^ (N - k)) *
      (algebraMap ℂ A x * epow E k j i + epow E (k + 1) j i) = a k - a (k + 1) := by
    intro k hk
    have hk' : N + 1 - k = (N - k) + 1 := by
      have := Finset.mem_range.mp hk; omega
    simp only [ha, hk', Nat.add_sub_add_right, mul_add, ← mul_assoc, ← map_mul, sub_eq_add_neg,
      ← neg_mul, ← map_neg]
    congr 3 <;> ring
  rw [Finset.sum_congr rfl h3, Finset.sum_range_sub']
  simp only [ha, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.sub_zero, sub_eq_add_neg, ← neg_mul, ← map_neg]
  congr 2
  congr 1
  ring

theorem traced_comatrix : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  intro A _ _ m E hE u N
  set C : Fin (m + 1) → Fin (m + 1) → A := fun i j =>
    (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u with hC
  set P : Fin (m + 1) → Fin (m + 1) → A := fun l i =>
    ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * epow E k l i with hP
  have hQ := qComatrix A m E hE u
  have S1 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
    simp only [hC, hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    congr 1
    simp only [hP, etr, Finset.mul_sum]
    exact Finset.sum_comm
  have S2 : ∑ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
      algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i := by
    have h : ∀ i, ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i =
        ∑ j, C i j * (algebraMap ℂ A ((u - m) ^ (N + 1)) * (if j = i then 1 else 0) +
          algebraMap ℂ A ((-1) ^ N) * epow E (N + 1) j i) := by
      intro i
      calc ∑ l, (∑ j, C i j * Tm E (u - (m : ℂ)) j l) * P l i
          = ∑ j, C i j * ∑ l, Tm E (u - (m : ℂ)) j l * P l i := by
            simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
            exact Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun j _ => congrArg (C i j * ·) (key E (u - (m : ℂ)) N j i)
    simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.commutes]
      simp [hC, ← two_mul, pow_mul]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← mul_assoc, ← Algebra.commutes, hC]
  exact S2.symm.trans S1

end GlobalTheory.TracedComatrix
end

