module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnipotentIntegralPreservesLattice
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def fr (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  Fin.snoc (α := fun _ => (VS D).V) x.1 x.2

def act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    (Fin D.R.rS → (VS D).V) × (VS D).V :=
  (fun a => n (x.1 a), n x.2)

def Good (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Prop :=
  (∀ b, fr D x b ∈ Λ) ∧ (∀ a b, brS (VS D) (fr D x b) (F0.fvec a) = Z a b) ∧
  (∀ a b, (VS D).hT (fr D x a) (fr D x b) =
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0)

def pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a - ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
    + ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm

def pWf (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  fun b => pW D (fr D x b)

def alM (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => (VS D).hT (D.sp.hypF a) (fr D x b)

def betaZ (D : Formalism.BasicNotions.D7) (Z : MatZ D) : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  Z.submatrix Fin.castSucc id

def RankG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 →
    ∃ R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E, betaZ D Z * R = 1

def FixedOK (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Prop :=
  Submodule.IsLattice D.host.E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ ∧ F0.e = D.sp.hypE ∧ (∀ a, F0.e a ∈ Λ) ∧
    ∃ c : D.host.E, c ≠ 0 ∧ F0.z = c • D.sp.zm

def GoodEZ : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D), ∀ F' ∈ EZ T' F0 Λ Z, Good D T' F0 Λ Z (F'.fl.e, F'.fl.z)

def Stage1 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∃ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → ∃ n ∈ N0 F0 Λ, pWf D (act D n x) ∈ Wf

def Stage2 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite →
    ∃ Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), Af.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → pWf D x ∈ Wf →
        ∃ n ∈ N0 F0 Λ, pWf D (act D n x) = pWf D x ∧ alM D (act D n x) * R ∈ Af

def FinK : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ (Wf : Set (Fin (D.R.rS + 1) → (VS D).V)) (Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)),
      Wf.Finite → Af.Finite →
      {x | Good D T' F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af}.Finite

theorem fr_act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V)
    (b : Fin (D.R.rS + 1)) : fr D (act D n x) b = n (fr D x b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b <;> simp [fr, act]

theorem unipotentIntegral_fixes_flag (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (a : Fin (D.R.rS + 1)) : n (F0.fvec a) = F0.fvec a := by
  obtain ⟨-, he, hz⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp [FlagG.fvec, he, hz]

theorem unipotentIntegral_isometry (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (x y : (VS D).V) : (VS D).hT (n x) (n y) = (VS D).hT x y := by
  obtain ⟨hL, -, -⟩ := hn
  unfold NLam at hL
  obtain ⟨hA, -, -⟩ := hL
  unfold IsAutLam at hA
  exact hA.1 x y

theorem unipotentIntegral_preserves_lattice (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    {v : (VS D).V} (hv : v ∈ Λ) : n v ∈ Λ := by
  obtain ⟨hL, -, -⟩ := hn
  obtain ⟨⟨-, hg⟩, -, -⟩ := hL
  unfold Formalism.HermitianLatticesTheory.gmap at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

theorem good_move (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ) :
    Good D T' F0 Λ Z (act D n x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [fr_act]
    exact unipotentIntegral_preserves_lattice D F0 Λ hn (h1 b)
  · rw [fr_act, ← unipotentIntegral_fixes_flag D F0 Λ hn a]
    unfold brS
    rw [unipotentIntegral_isometry D F0 Λ hn]
    have h2' := h2 a b
    unfold brS at h2'
    exact h2'
  · rw [fr_act, fr_act, unipotentIntegral_isometry D F0 Λ hn]
    exact h3 a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.WeightPositive
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hswap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem hzero_swap (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [hswap, h, star_zero]

theorem hFE (D : Formalism.BasicNotions.D7) (i i' : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF i) (D.sp.hypE i') = if i' = i then 1 else 0 := by
  rw [hswap, D.sp.hyp_ef i' i]
  split_ifs <;> simp

theorem hEz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).1, star_zero]

theorem hFz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).2, star_zero]

theorem real_of_emb (D : Formalism.BasicNotions.D7) (τ : D.host.E →+* ℂ) (w : (VS D).V) :
    τ ((VS D).hT w w) = ((τ ((VS D).hT w w)).re : ℂ) := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 : starRingEnd ℂ (τ ((VS D).hT w w)) = τ ((VS D).hT w w) := by
    rw [← hτ, ← hswap]
  have him : (τ ((VS D).hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidef (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0) (τ : D.host.E →+* ℂ) :
    0 ≤ (τ ((VS D).hT w w)).re := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  by_contra hlt
  rw [not_le] at hlt
  have hT0 : (0 : ℝ) < D.sp.T := by exact_mod_cast D.sp.T_prime.pos
  let wv : Fin D.R.rS ⊕ Bool → (VS D).V :=
    Sum.elim (fun a => D.sp.hypE a - D.sp.hypF a) (fun b => if b then w else D.sp.zm)
  let d : Fin D.R.rS ⊕ Bool → ℝ :=
    Sum.elim (fun _ => -2) (fun b => if b then (τ ((VS D).hT w w)).re else -(D.sp.T : ℝ))
  have hoff : ∀ i j, i ≠ j → (VS D).hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef,
        hFE, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, hEz, hFz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF,
          sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          (D.sp.hyp_orthz a').1, (D.sp.hyp_orthz a').2, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hzero_swap D (hE a'),
          hzero_swap D (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hzero_swap D hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ ((VS D).hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff,
        D.sp.hyp_ef, hFE, if_true]
      rw [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, D.sp.zm_norm, map_neg,
          map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of_emb D τ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily (VS D) τ hτ (D.sp.Y_sig 0 τ) wv d hoff hdiag hneg
  have hq : ((D.sp.Y 0).sig τ).2 = D.R.rS + 1 := by rw [D.sp.baseSpace_signature_eq τ]; rfl
  rw [hq] at hc
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isotropic_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0)
    (h0 : (VS D).hT w w = 0) : w = 0 := by
  let τ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have orthW : ∀ y : (VS D).V, (∀ a, (VS D).hT (D.sp.hypE a) y = 0) →
      (∀ a, (VS D).hT (D.sp.hypF a) y = 0) → (VS D).hT D.sp.zm y = 0 → (VS D).hT w y = 0 := by
    intro y hyE hyF hyz
    by_contra hx
    set x := (VS D).hT w y with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hN : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set y' : (VS D).V := star x • y with hy'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ ((VS D).hT y' y')).re := by
      intro n
      set v : (VS D).V := (n : D.host.E) • w - y' with hv
      have hvE : ∀ a, (VS D).hT (D.sp.hypE a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hE a, hyE a]
      have hvF : ∀ a, (VS D).hT (D.sp.hypF a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hF a, hyF a]
      have hvz : (VS D).hT D.sp.zm v = 0 := by
        simp [hv, hy', map_sub, map_smul, hz, hyz]
      have hs := semidef D v hvE hvF hvz τ
      have hyw : (VS D).hT y w = star x := by rw [hswap]
      have e1 : (VS D).hT v v = -(2 * (n : D.host.E)) * (x * star x) + (VS D).hT y' y' := by
        simp only [hv, map_sub, LinearMap.sub_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hy', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ ((VS D).hT v v)).re =
          -(2 * n * Complex.normSq (τ x)) + (τ ((VS D).hT y' y')).re := by
        rw [e1, map_add (f := _), map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ ((VS D).hT y' y')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith

  have hzz : (VS D).hT D.sp.zm D.sp.zm ≠ 0 := by
    rw [D.sp.zm_norm, neg_ne_zero]
    exact_mod_cast D.sp.T_prime.ne_zero
  apply (VS D).nondeg.1 w
  intro x
  set xW : (VS D).V := x - ∑ a, ((VS D).hT (D.sp.hypF a) x • D.sp.hypE a + (VS D).hT (D.sp.hypE a) x • D.sp.hypF a) -
    ((VS D).hT D.sp.zm x / (VS D).hT D.sp.zm D.sp.zm) • D.sp.zm with hxW
  have hWE : ∀ b, (VS D).hT (D.sp.hypE b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ee, D.sp.hyp_ef, hEz]
  have hWF : ∀ b, (VS D).hT (D.sp.hypF b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ff, hFE, hFz]
  have hWz : (VS D).hT D.sp.zm xW = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, (D.sp.hyp_orthz _).1, (D.sp.hyp_orthz _).2, hzz]
  have h1 := orthW xW hWE hWF hWz
  have hwE : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => hzero_swap D (hE a)
  have hwF : ∀ a, (VS D).hT w (D.sp.hypF a) = 0 := fun a => hzero_swap D (hF a)
  have hwz : (VS D).hT w D.sp.zm = 0 := hzero_swap D hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [hxW, map_sub, map_sum, map_add (f := _), map_smul, hwE, hwF, hwz] using h1

theorem weights_are_positive : WPos := by
  intro D w hE hF hz hw
  have pos : ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT w w)).re := by
    intro τ
    refine lt_of_le_of_ne (semidef D w hE hF hz τ) fun h => hw ?_
    apply isotropic_zero D w hE hF hz
    apply τ.injective
    rw [real_of_emb D τ w, ← h, Complex.ofReal_zero, map_zero]
  haveI : Nonempty (D.host.E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) (E := ℂ) (x := (VS D).hT w w)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hsum : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ ((VS D).hT w w)).re :=
    Finset.sum_pos (fun σ _ => pos σ.toRingHom) Finset.univ_nonempty
  rw [← hre] at hsum
  have : ((Algebra.trace ℚ D.host.E ((VS D).hT w w) : ℚ) : ℝ) =
      (algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E ((VS D).hT w w))).re := by simp
  rw [← this] at hsum
  exact_mod_cast hsum

theorem definite_finite : DefFinW := defFinW_of weights_are_positive

end PI.UnitaryGroupMassFormula.CntFormula
end
end

