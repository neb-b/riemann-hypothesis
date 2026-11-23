module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemN1IffLocalHom
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.UnipRead

variable {E : Type} [Field E] {M c : ℕ}

def lv (M u : ℕ) : ℕ := if u < M then 1 else u - M + 1

theorem one_le_lv (M u : ℕ) : 1 ≤ lv M u := by unfold lv; split_ifs <;> omega

def Unip (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : Prop :=
  ∀ u v : Fin (M + c), lv M v.1 ≤ lv M u.1 → x (Pi.single v 1) u = if u = v then 1 else 0

theorem apply_eq_sum (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) (w : Fin (M + c) → E) (l : Fin (M + c)) :
    x w l = ∑ v, w v * x (Pi.single v 1) l := by
  have hw : w = ∑ v, Pi.single v (w v) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : (Pi.single v (w v) : Fin (M + c) → E) = w v • (Pi.single v (1 : E) : Fin (M + c) → E) := by
    ext j; simp [Pi.single_apply]
  rw [h, map_smul]
  simp

theorem eN_val (v : Fin (M + c)) : Loc.eN E (M + c) v.1 = Pi.single v 1 := by
  ext l; simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_out {j : ℕ} (h : ¬ j < M + c) : Loc.eN E (M + c) j = 0 := by
  ext l; simp only [Loc.eN, Pi.zero_apply]; rw [if_neg]; omega

theorem inX_apply (y : Fin M → E) (l : Fin (M + c)) :
    Loc.inX E M c y l = if h : l.1 < M then y ⟨l.1, h⟩ else 0 := by
  simp only [Loc.inX, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem col {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) (j : ℕ) (l : Fin (M + c))
    (hle : lv M j ≤ lv M l.1) : x (Loc.eN E (M + c) j) l = Loc.eN E (M + c) j l := by
  by_cases h : j < M + c
  · have := eN_val (E := E) (⟨j, h⟩ : Fin (M + c))
    simp only at this
    rw [this, hU l ⟨j, h⟩ hle]
    simp [Pi.single_apply]
  · rw [eN_out h, map_zero]

theorem r1cond_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : Loc.R1cond E M c x := by
  refine ⟨fun i w hw l hl => ?_, ?_, fun i l hl => ?_⟩
  · rw [apply_eq_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v.1 < M + i
    · have hl' : ¬ l.1 < M + i := hl
      rw [hU l v (by unfold lv; split_ifs <;> omega), if_neg (by intro h; subst h; exact hl' hv), mul_zero]
    · rw [hw v hv, zero_mul]
  · ext l
    exact col hU M l (by have := one_le_lv M l.1; unfold lv at this ⊢; simp; omega)
  · have hl' : ¬ l.1 < M + i := hl
    show x _ l - _ = 0
    rw [col hU (M + i) l (by unfold lv; split_ifs <;> omega), sub_self]

theorem fixX_of_unip {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hU : Unip x) : x ∈ Loc.fixX E M c := by
  intro y
  ext l
  rw [apply_eq_sum, Finset.sum_eq_single l]
  · by_cases hl : l.1 < M
    · rw [hU l l (le_refl _), if_pos rfl, mul_one]
    · simp [inX_apply, hl]
  · intro v _ hvl
    by_cases hv : v.1 < M
    · rw [hU l v (by have := one_le_lv M l.1; unfold lv; rw [if_pos hv]; exact this), if_neg (Ne.symm hvl), mul_zero]
    · rw [inX_apply, dite_eq_right hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem unip_of {x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)} (hR : Loc.R1cond E M c x)
    (hX : x ∈ Loc.fixX E M c) : Unip x := by
  intro u v hle
  by_cases hv : v.1 < M
  · have hs : (Pi.single v 1 : Fin (M + c) → E) = Loc.inX E M c (Pi.single ⟨v.1, hv⟩ 1) := by
      ext l; rw [inX_apply]; split_ifs with h
      · simp [Pi.single_apply, Fin.ext_iff]
      · simp [Pi.single_apply, Fin.ext_iff]; omega
    rw [hs, hX, ← hs]
    simp [Pi.single_apply]
  · have hj : M + (v.1 - M) = v.1 := by omega
    by_cases hu : u.1 < M + (v.1 - M)
    · have hvM : v.1 = M := by
        unfold lv at hle; split_ifs at hle <;> omega
      have h2 := congrFun hR.2.1 u
      have h4 := eN_val (E := E) v
      rw [hvM] at h4
      rw [h4] at h2
      rw [h2]; simp [Pi.single_apply]
    · have h3 := hR.2.2 (v.1 - M) u hu
      rw [hj, eN_val] at h3
      have h3' : x (Pi.single v 1) u - (Pi.single v 1 : Fin (M + c) → E) u = 0 := h3
      rw [sub_eq_zero] at h3'
      rw [h3']; simp [Pi.single_apply]

section Read
variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem lev_eq (s : A ⊕ Fin c) : lev 1 s = lv M (e s).1 := by
  rcases s with a | i
  · have := eX_lt e rfl he a
    simp [lev, lv, this]
  · simp only [lev, Sum.elim_inr, lv, he i]
    split_ifs <;> omega


include he in
theorem inN_iff (x : (Fin (M + c) → E) ≃ₗ[E] (Fin (M + c) → E)) : InN 1 (locHom ι e x) ↔ Unip x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hent : ∀ (a : E) (r s : A ⊕ Fin c),
      ι a = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s ↔ a = if e r = e s then 1 else 0 := by
    intro a r s
    rw [Matrix.one_apply]
    by_cases h : r = s
    · simp [h, map_eq_one_iff ι ι.injective]
    · simp [h, e.injective.eq_iff]
  constructor
  · intro h u v hle
    have := h (e.symm u) (e.symm v) (by rw [lev_eq e he, lev_eq e he]; simpa using hle)
    rw [hval, hent] at this
    simpa using this
  · intro h r s hle
    rw [hval, hent]
    rw [lev_eq e he, lev_eq e he] at hle
    exact h (e r) (e s) hle

end Read

theorem mem_N1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [Model.mem_N_iff, inN_iff ι e he]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact unip_of h1 h2
  · intro h
    have hN : locHom ι e x ∈ N k A c' 1 := Model.mem_N_iff.2 ((inN_iff ι e he x).2 h)
    have hinv : Unip x⁻¹ := by
      rw [← inN_iff ι e he, map_inv]
      exact Model.mem_N_iff.1 (inv_mem hN)
    exact ⟨⟨r1cond_of_unip h, r1cond_of_unip hinv⟩, fixX_of_unip h⟩

end GlobalTheory.UnipRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHom
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.RankOneMatrix

def stepAt (M : ℕ) {N : ℕ} (l : Fin N) : ℕ := if l.val < M then 1 else l.val - M + 1

variable {E : Type} [Field E] {M c : ℕ}

theorem eN_eq_single {N j : ℕ} (h : j < N) : Loc.eN E N j = Pi.single (⟨j, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, Fin.val_mk]

theorem eN_eq_zero {N j : ℕ} (h : N ≤ j) : Loc.eN E N j = 0 := by
  funext l
  have : l.val ≠ j := by have := l.isLt; omega
  simp [Loc.eN, this]

theorem mem_Ufl {v : Sp E (M + c)} {i : ℕ} :
    v ∈ Loc.Ufl E M c i ↔ ∀ l : Fin (M + c), M + i ≤ l.val → v l = 0 := by
  show (∀ l : Fin (M + c), l.1 ∉ {l | l < M + i} → v l = 0) ↔ _
  simp only [Set.mem_setOf_eq, not_lt]

def ColCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Prop :=
  ∀ l m : Fin (M + c), stepAt M m ≤ stepAt M l → (M ≤ l.val ∨ M ≤ m.val) →
    x (Pi.single m 1) l = (Pi.single m 1 : Sp E (M + c)) l

theorem colCond_of_R1cond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : Loc.R1cond E M c x) : ColCond x := by
  intro l m hlm hM
  by_cases hm : m.val < M
  · have hl : M ≤ l.val := hM.resolve_right (by omega)
    have hv : (Pi.single m 1 : Sp E (M + c)) ∈ Loc.Ufl E M c 0 := by
      rw [mem_Ufl]
      intro l' hl'
      have : l' ≠ m := by rintro rfl; omega
      simp [Pi.single_apply, this]
    have h1 := (mem_Ufl.1 (h.1 0 _ hv)) l (by omega)
    have hne : l ≠ m := by rintro rfl; omega
    rw [h1]
    simp [Pi.single_apply, hne]
  · obtain ⟨j, hj⟩ : ∃ j, m.val = M + j := ⟨m.val - M, by omega⟩
    have hsingle : (Pi.single m 1 : Sp E (M + c)) = Loc.eN E (M + c) (M + j) := by
      rw [eN_eq_single (by omega : M + j < M + c)]
      congr 1
      exact Fin.ext hj
    by_cases hl : l.val < M
    · have hj0 : j = 0 := by
        simp only [stepAt, hl, hm, if_true, if_false] at hlm
        omega
      subst hj0
      rw [hsingle, add_zero, h.2.1]
    · have hjl : M + j ≤ l.val := by
        simp only [stepAt, hl, hm, if_false] at hlm
        omega
      have h3 := (mem_Ufl.1 (h.2.2 j)) l hjl
      rw [Pi.sub_apply, sub_eq_zero, ← hsingle] at h3
      exact h3

theorem R1cond_of_colCond {x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)} (h : ColCond x) : Loc.R1cond E M c x := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl] at hv ⊢
    intro l hl
    have hv' : v = ∑ m, v m • (Pi.single m 1 : Sp E (M + c)) := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv', map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : M + i ≤ m.val
    · rw [hv m hm, zero_mul]
    · have hne : l ≠ m := by rintro rfl; omega
      rw [h l m (by simp only [stepAt]; split_ifs <;> omega) (Or.inl (by omega))]
      simp [Pi.single_apply, hne]
  · by_cases hc : M < M + c
    · rw [eN_eq_single hc]
      funext l
      exact h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr le_rfl)
    · rw [eN_eq_zero (by omega), map_zero]
  · by_cases hc : M + i < M + c
    · rw [mem_Ufl, eN_eq_single hc]
      intro l hl
      rw [Pi.sub_apply, h l _ (by simp only [stepAt, Fin.val_mk]; split_ifs <;> omega) (Or.inr (by simp)), sub_self]
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

theorem R1cond_iff_colCond (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : Loc.R1cond E M c x ↔ ColCond x :=
  ⟨colCond_of_R1cond, R1cond_of_colCond⟩

section Matrix

variable {k : Type} [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
  (e : A ⊕ Fin c ≃ Fin (M + c)) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem lev_eq_stepAt (r : A ⊕ Fin c) : lev 1 r = stepAt M (e r) := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp [lev, stepAt, this]
  · have := he i
    simp only [lev, Sum.elim_inr, stepAt, this]
    split_ifs <;> omega

include he in
theorem isRight_iff (r : A ⊕ Fin c) : r.isRight ↔ M ≤ (e r).val := by
  rcases r with a | i
  · have := eX_lt e rfl he a
    simp only [Sum.isRight_inl, Bool.false_eq_true, false_iff, not_le]
    exact this
  · simp [he i]


include he in
theorem inR_locHom_iff (x : Sp E (M + c) ≃ₗ[E] Sp E (M + c)) : VolN.InR 1 (locHom ι e x) ↔ ColCond x := by
  have hval : ∀ r s, (locHom ι e x).val r s = ι (x (Pi.single (e s) 1) (e r)) := fun r s => rfl
  have hone : ∀ r s, (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k) r s = ι ((Pi.single (e s) (1 : E) : Sp E (M + c)) (e r)) := by
    intro r s
    simp only [Matrix.one_apply, Pi.single_apply, e.apply_eq_iff_eq]
    split_ifs <;> simp
  constructor
  · intro h l m hlm hM
    have := h (e.symm l) (e.symm m) (by rw [lev_eq_stepAt e he, lev_eq_stepAt e he]; simpa using hlm)
      (by rw [isRight_iff e he, isRight_iff e he]; simpa using hM)
    rw [hval, hone] at this
    simpa using ι.injective this
  · intro h r s hrs hR
    rw [hval, hone]
    congr 1
    apply h
    · rw [← lev_eq_stepAt e he, ← lev_eq_stepAt e he]; exact hrs
    · rw [← isRight_iff e he, ← isRight_iff e he]; exact hR

end Matrix

theorem mem_rationalFirstParabolic_iff_localGL_mem_rootExchange : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
    (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) →
    ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  intro E k _ _ ι A _ _ M c c' e hcc he x
  subst hcc
  rw [VolN.mem_R_iff, ← map_inv, inR_locHom_iff ι e he, inR_locHom_iff ι e he,
    ← R1cond_iff_colCond, ← R1cond_iff_colCond]
  exact Iff.rfl

end GlobalTheory.RankOneMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ExchangeProof

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_mul_le_one (a : kˣ) (z : k) :
    valuation k (((a⁻¹ : kˣ) : k) * z) ≤ 1 ↔ valuation k z ≤ valuation k (a : k) := by
  have : 0 < valuation k (a : k) := by simp [zero_lt_iff]
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ this]

variable [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem opE_step (ν : Measure k) (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t]
    [DecidableEq t] (hP : S.Pattern t) (j c : ℕ) (H : j + c = s) (q : Fin c) (hq : q.val + 1 ≤ S.ρ)
    (hqc : q.val + 2 ≤ c) : ∃ C : ℝ, 0 < C ∧
      opE S.ψ ν (q.val + 2) ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν (q.val + 1) ((S.T t).Phi j c H) := by
  haveI := hν.1
  have := secondCountable k
  have := t2Space k
  set Φ := (S.T t).Phi j c H with hΦ
  let I := (XIx (Fin κ) t (j + 1) ⊕ Fin c) × (XIx (Fin κ) t j ⊕ Fin (c + 1))
  let A : I → Prop := fun i => i.1 = Sum.inr q ∧ i.2.isLeft = true
  let B : I → Prop := fun i => i.2 = Sum.inr q.succ ∧ i.1.isLeft = true
  let R : I → Prop := fun i => Free (q.val + 1) i ∧ ¬ B i
  let a : kˣ := S.ϖ ^ (q.val + 1)
  let b : kˣ := S.ϖ ^ (q.val + 2)
  let sA : Set k := cball a
  let sB : Set k := (fun z => (b : k) * z) ⁻¹' {z | valuation k z < 1}
  have oB : IsOpen sB := IsOpen.preimage (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
  have sBc : sB ⊆ cball b⁻¹ := fun z hz => by
    have hz : valuation k ((b : k) * z) < 1 := hz
    have : 0 < valuation k (b : k) := by simp [zero_lt_iff]
    rw [map_mul] at hz
    change valuation k z ≤ valuation k ((b⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : valuation k z = (valuation k (b : k))⁻¹ * (valuation k (b : k) * valuation k z) := by
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    rw [h1]; exact mul_le_of_le_one_right' hz.le
  have mA : MeasurableSet sA := (isOpen_cball a).measurableSet
  have mB : MeasurableSet sB := oB.measurableSet
  have fA : ν sA ≠ ⊤ := (isCompact_cball a).measure_lt_top.ne
  have fB : ν sB ≠ ⊤ := ((isCompact_cball b⁻¹).measure_lt_top.trans_le' (measure_mono sBc)).ne
  have pA : 0 < ν sA := (isOpen_cball a).measure_pos ν ⟨0, by simp [sA, cball]⟩
  have pB : 0 < ν sB := oB.measure_pos ν ⟨0, by simp [sB]⟩
  let G : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k → (I → k) → ℂ := fun x₀ m =>
    Φ (basePt c x₀ + Matrix.of fun r s' => m (r, s')) * (S.ψ (-ch (basePt c x₀ + Matrix.of fun r s' => m (r, s'))) : ℂ)
  have hR2 : ∀ i, R i ↔ Free (q.val + 2) i ∧ ¬ A i := by
    rintro ⟨r | r, s' | s'⟩ <;> simp [R, A, B, Free, Fin.ext_iff] <;> omega
  have hR1 : ∀ i, R i ↔ Free (q.val + 1) i ∧ ¬ B i := fun i => Iff.rfl
  have hA : ∀ i, A i → Free (q.val + 2) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [A, Free]
  have hB : ∀ i, B i → Free (q.val + 1) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [B, Free]
  have gA : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, A i → m i ∈ sA then (1 : ℂ) else 0) * G x₀ (fun i => if A i then 0 else m i) := by
    intro x₀ m
    let v : XIx (Fin κ) t j → k := fun s' => m (Sum.inr q, Sum.inl s')
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if A (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 := by
      ext (r | r) (s' | s')
      · simp [A]
      · simp [A]
      · by_cases h : r = q
        · subst h; simp [A, v, basePt]
        · simp [A, h]
      · simp [A]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) := by
      simp [ch, A]
    have row0 : ∀ s', (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) (Sum.inr q) (Sum.inl s') = 0 := by
      intro s'; simp [basePt, A]
    have hiff : (∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1) ↔ ∀ i, A i → m i ∈ sA := by
      constructor
      · rintro h ⟨r, s' | s'⟩ ⟨rfl, hs⟩
        · exact (val_inv_mul_le_one a _).1 (h s')
        · simp at hs
      · intro h s'; exact (val_inv_mul_le_one a _).2 (h (Sum.inr q, Sum.inl s') ⟨rfl, rfl⟩)
    simp only [G]
    rw [hch, hx, hΦ, _root_.GlobalTheory.SymChain.RowShift.phi_add_row k s κ S t hP j c H q hq _ row0 v]
    by_cases hc : ∀ i, A i → m i ∈ sA
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have gB : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, B i → m i ∈ sB then (1 : ℂ) else 0) * G x₀ (fun i => if B i then 0 else m i) := by
    intro x₀ m
    let w : XIx (Fin κ) t (j + 1) → k := fun r => m (Sum.inl r, Sum.inr q.succ)
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if B (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0 := by
      ext (r | r) (s' | s')
      · simp [B]
      · by_cases h : s' = q.succ
        · subst h; simp [B, w, basePt]
        · simp [B, h]
      · simp [B]
      · simp [B]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) := by
      simp [ch, B]
    have col0 : ∀ r, (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) (Sum.inl r) (Sum.inr q.succ) = 0 := by
      intro r; simp [basePt, B]
    have hiff : (∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1) ↔ ∀ i, B i → m i ∈ sB := by
      constructor
      · rintro h ⟨r | r, s'⟩ ⟨rfl, hs⟩
        · exact h r
        · simp at hs
      · intro h r; exact h (Sum.inl r, Sum.inr q.succ) ⟨rfl, rfl⟩
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.matrix_block_column_vanishing_step k s κ S t hP j c H q hq hqc _ col0 w]
    by_cases hc : ∀ i, B i → m i ∈ sB
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have e2 : ∀ x₀, opE S.ψ ν (q.val + 2) Φ x₀ = (((ν sA).toReal ^ Fintype.card {i // A i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 2)) A R hR2 hA sA mA fA (G x₀) (gA x₀)
  have e1 : ∀ x₀, opE S.ψ ν (q.val + 1) Φ x₀ = (((ν sB).toReal ^ Fintype.card {i // B i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 1)) B R hR1 hB sB mB fB (G x₀) (gB x₀)
  have tA : 0 < (ν sA).toReal := ENNReal.toReal_pos pA.ne' fA
  have tB : 0 < (ν sB).toReal := ENNReal.toReal_pos pB.ne' fB
  refine ⟨(ν sA).toReal ^ Fintype.card {i // A i} / (ν sB).toReal ^ Fintype.card {i // B i},
    div_pos (pow_pos tA _) (pow_pos tB _), funext fun x₀ => ?_⟩
  rw [Pi.smul_apply, e2, e1, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos tB _).ne']

end Step

theorem exchangeAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP j c H p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ _; exact ⟨1, one_pos, by simp⟩
  | succ p hp ih =>
    intro hpc hpρ
    obtain ⟨C, hC, e⟩ := ih (by omega) (by omega)
    obtain ⟨C', hC', e'⟩ := opE_step ν hν S t hP j c H ⟨p - 1, by omega⟩ (by simp; omega) (by simp; omega)
    have h2 : (p - 1) + 2 = p + 1 := by omega
    have h1 : (p - 1) + 1 = p := by omega
    simp only [h1, h2] at e'
    refine ⟨C' * C, mul_pos hC' hC, ?_⟩
    rw [e', e, smul_smul, Complex.ofReal_mul]

end GlobalTheory.SymChain.ExchangeProof
end
end

