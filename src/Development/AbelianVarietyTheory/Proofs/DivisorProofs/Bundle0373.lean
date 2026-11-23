module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
section
namespace GlobalTheory.FGDepth.Coord

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

open MvPowerSeries in
private lemma subst_sum_smul_X' {C : Type} [Field C] {σ τ ι : Type} [Fintype ι]
    {b : σ → MvPowerSeries τ C} (hb : HasSubst b) (c : ι → C) (g : ι → σ) :
    subst b (∑ a, c a • (X (g a) : MvPowerSeries σ C)) = ∑ a, c a • b (g a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hb, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hb]

open MvPowerSeries in
private lemma mvIsInt_X_divisor {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (s : σ) : _root_.ReciprocityTheory.PGsh.MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))
  rw [coeff_X]
  split_ifs <;> simp


open MvPowerSeries in
variable {C : Type} [Field C] in
theorem _root_.GlobalTheory.FGDepth.Coord.depth_in_coords : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (u : Fin i → Fin d → C)
    (Φ Ψ : Fin d → MvPowerSeries (Fin d) C),
    (∀ a, _root_.ReciprocityTheory.PGsh.MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ _root_.ReciprocityTheory.PGsh.MvIsInt v (Ψ a) ∧
      constantCoeff (Ψ a) = 0) →
    (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) →
    ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) →
    (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) →
    _root_.GlobalTheory.FGDepth.detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C //
      _root_.ReciprocityTheory.PGsh.MvIsInt v f}, _root_.GlobalTheory.FGDepth.toE (v (_root_.GlobalTheory.FGDepth.derivAt0
        (_root_.GlobalTheory.FGDepth.detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) =>
          subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2))
            f.1))) := by
  intro C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.2
  have hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0 := (_root_.GlobalTheory.FGDepth.isExp_expOf G).1
  have hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G) := hasSubst_of_constantCoeff_zero hex0
  have hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C) :=
    hasSubst_of_constantCoeff_zero hLin0
  have hΦtS : HasSubst fun a => subst t (Φ a) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1

  have hΦt : ∀ a, subst t (Φ a) =
      subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
        (_root_.GlobalTheory.FGDepth.expOf G a) := by
    intro a
    have h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) =
        fun e => subst (fun a => subst t (Φ a)) (G.lg e) := by
      funext e
      rw [← subst_comp_subst_apply hΦ htS, ht]
    rw [h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]
  have ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
      (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e)) := by
    intro e
    rw [subst_comp_subst_apply hexS hLinS]
    calc t e = subst t (X e) := (subst_X htS e).symm
      _ = subst t (subst Φ (Ψ e)) := by rw [(hinv e).2]
      _ = subst (fun a => subst t (Φ a)) (Ψ e) := subst_comp_subst_apply hΦ htS _
      _ = _ := by simp_rw [hΦt]

  have hXb : ∀ b : Fin i, HasSubst fun a : Fin i =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hXd : ∀ b : Fin i, HasSubst fun a : Fin d =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hLinB0 : ∀ (b : Fin i) (e : Fin d),
      constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := by
    intro b e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hLinBS : ∀ b : Fin i, HasSubst fun e =>
      ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)
  have hE0 : ∀ x, constantCoeff
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)
  have hES : HasSubst
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) :=
    hasSubst_of_constantCoeff_zero hE0
  have hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2
  have hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=
    hasSubst_of_constantCoeff_zero hΨ0
  have hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1
  have hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=
    hasSubst_of_constantCoeff_zero hΦ0

  have key : ∀ x : (Σ _ : Fin i, Fin d),
      subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =
      subst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))
        (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C))
          (Ψ x.2)) := by
    rintro ⟨b, e⟩
    have hlin : (fun e' => subst (fun a : Fin i =>
        (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C))
          (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) =
        fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
      funext e'
      exact subst_sum_smul_X' (hXb b) (fun a => u a e') id
    rw [ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin,
      subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]
    congr 1
    funext a
    rw [subst_X hES]
    rfl

  have hround : (fun x : (Σ _ : Fin i, Fin d) => subst
      (fun x : (Σ _ : Fin i, Fin d) =>
        subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =
      X := by
    funext x
    rw [subst_comp_subst_apply (hXd x.1) hΨS]
    simp_rw [subst_X hΨS]
    rw [← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]
  unfold _root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth
  simp_rw [key]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    rw [← subst_comp_subst_apply hΨS hES]
    exact iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΨ0⟩ le_rfl
  · refine le_iInf fun f => ?_
    refine iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΦ0⟩ ?_
    rw [← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]
    rfl

end

end GlobalTheory.FGDepth.Coord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContent
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.DepthLeContent

noncomputable section

section Lead

variable {S τ : Type} [CommRing S]

def Near (k n : ℕ) (P Q : MvPowerSeries τ S) : Prop :=
  (n : ℕ∞) ≤ P.order ∧ (n : ℕ∞) ≤ Q.order ∧ ((k + n : ℕ) : ℕ∞) ≤ (P - Q).order + 1

theorem Near.one (k : ℕ) : Near k 0 (1 : MvPowerSeries τ S) 1 := by
  simp [Near]

theorem Near.mul {k n m : ℕ} {P Q P' Q' : MvPowerSeries τ S} (h : Near k n P Q)
    (h' : Near k m P' Q') : Near k (n + m) (P * P') (Q * Q') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast; exact (add_le_add h1 h1').trans le_order_mul
  · push_cast; exact (add_le_add h2 h2').trans le_order_mul
  · have e : P * P' - Q * Q' = P * (P' - Q') + (P - Q) * Q' := by ring
    rw [e]
    refine le_trans ?_ (add_le_add_left min_order_le_add 1)
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_assoc]
      refine le_trans (le_of_eq ?_) (add_le_add h1 h3')
      push_cast; ring
    · refine le_trans ?_ (add_le_add_left le_order_mul 1)
      rw [add_right_comm]
      refine le_trans (le_of_eq ?_) (add_le_add h3 h2')
      push_cast; ring

theorem Near.prod {σ : Type} {k : ℕ} {a b : σ → MvPowerSeries τ S}
    (h : ∀ s, Near k 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Near k d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa using Near.one k
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
      Finsupp.prod_add_index' (by simp) (by simp [pow_add]), map_add (f := _)]
    exact hf.mul hg
  | single s n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.degree_single]
    induction n with
    | zero => simpa using Near.one k
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (h s)

theorem lead_prod (Y : τ → MvPowerSeries τ S) (hY : ∀ s, 2 ≤ (Y s - X s).order) (α : τ →₀ ℕ) :
    ((α.degree + 1 : ℕ) : ℕ∞) ≤ ((α.prod fun s k => Y s ^ k) - monomial α 1).order := by
  classical
  have hc : ∀ s, Near 2 1 (Y s) (X s) := fun s => by
    have hX : (1 : ℕ∞) ≤ (X s : MvPowerSeries τ S).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    refine ⟨?_, hX, ?_⟩
    · have : Y s = (Y s - X s) + X s := by ring
      rw [this]
      exact le_trans (le_min ((by norm_num : (1 : ℕ∞) ≤ 2).trans (hY s)) hX) min_order_le_add
    · have := add_le_add (hY s) (le_refl (1 : ℕ∞))
      push_cast
      exact this
  have h := (Near.prod hc α).2.2
  have hm : (α.prod fun s e => (X s : MvPowerSeries τ S) ^ e) = monomial α 1 := by
    have := subst_monomial (R := S) (HasSubst.X (S := S) (σ := τ)) α (1 : S)
    rw [subst_self] at this
    simpa using this.symm
  rw [hm] at h
  have h2 : ((α.degree + 1 : ℕ) : ℕ∞) + 1 = ((2 + α.degree : ℕ) : ℕ∞) := by
    push_cast; ring
  exact (ENat.add_le_add_iff_right (by simp)).mp (h2.le.trans h)

end Lead

section Int

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem isInt_mul {τ : Type} {f g : MvPowerSeries τ C} (hf : MvIsInt v f) (hg : MvIsInt v g) :
    MvIsInt v (f * g) := by
  classical
  intro α
  unfold IsIntV
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) (by simp) ?_
  intro p _
  rw [v.map_mul]
  exact add_nonneg (hf _) (hg _)


open Classical in
def intSub (τ : Type) : Subring (MvPowerSeries τ C) where
  carrier := {f | MvIsInt v f}
  mul_mem' := isInt_mul v
  one_mem' := by
    classical
    intro α; unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  add_mem' := by
    intro f g hf hg α; unfold IsIntV; rw [map_add (f := _)]
    exact le_trans (le_min (hf α) (hg α)) (v.map_add _ _)
  zero_mem' := by intro α; unfold IsIntV; simp
  neg_mem' := by intro f hf α; unfold IsIntV; rw [map_neg, v.map_neg]; exact hf α

theorem isInt_smul_X {τ : Type} {c : C} (hc : IsIntV v c) (t : τ) :
    MvIsInt v (c • (X t : MvPowerSeries τ C)) := by
  classical
  intro α; unfold IsIntV
  rw [coeff_smul, coeff_X]
  split_ifs
  · rw [mul_one]; exact hc
  · simp

theorem isInt_prod {σ τ : Type} (L : σ → MvPowerSeries τ C) (hL : ∀ s, MvIsInt v (L s))
    (α : σ →₀ ℕ) : MvIsInt v (α.prod fun s k => L s ^ k) := by
  classical
  show _ ∈ intSub v τ
  unfold Finsupp.prod
  exact prod_mem fun s _ => pow_mem (hL s) _

end Int

theorem coeff_single_exp {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {ex : Fin d → MvPowerSeries (Fin d) C} (h : IsExp G ex) (a b : Fin d) :
    coeff (Finsupp.single b 1) (ex a) = if a = b then 1 else 0 := by
  have e := congrArg (coeff (Finsupp.single b 1)) (h.2 a)
  rw [GlobalTheory.FormalSeries.coeff_single_subst h.1] at e
  simp only [G.lg_lin, smul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, coeff_X] at e
  rw [e]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Finsupp.single_left_inj one_ne_zero, Ne.symm hab]

theorem depth_le_content : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (d n : κ → ℕ) (G : ∀ b, LogFGL v (d b))
    (u : ∀ b, Fin (n b) → Fin (d b) → C) (P : MvPolynomial (Σ b, Fin (n b)) C) (D : ℕ),
    P.IsHomogeneous D → (∀ b, IsSatFrame v (u b)) →
      depth G (ι := fun b => Fin (n b)) u P ≤ content v P := by
  intro C _ _ v κ _ _ d n G u P D hP hu
  classical
  choose l hlint hldual using fun b => GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame C v (n b) (d b) (u b) (hu b)
  have hexp : ∀ b, IsExp (G b) (expOf (G b)) := fun b => (_root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v (d b) (G b)).1
  have hlin0 : ∀ b (e : Fin (d b)), constantCoeff
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) = 0 := by
    intro b e; simp
  have hlin1 : ∀ b (e : Fin (d b)) (y : Σ b, Fin (n b)), coeff (Finsupp.single y 1)
      (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, Fin (n b)) C)) =
        ∑ a, u b a e * if y = ⟨b, a⟩ then 1 else 0 := by
    intro b e y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero, smul_eq_mul]
  set A := expAlong G u with hAdef
  have hA0 : ∀ x, constantCoeff (A x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hlin0 x.1)) (hlin0 x.1)
      ((hexp x.1).1 x.2)
  have hA1 : ∀ x y, coeff (Finsupp.single y 1) (A x) =
      ∑ a, u x.1 a x.2 * if y = ⟨x.1, a⟩ then 1 else 0 := by
    intro x y
    show coeff (Finsupp.single y 1) (subst _ (expOf (G x.1) x.2)) = _
    rw [GlobalTheory.FormalSeries.coeff_single_subst (hlin0 x.1)]
    simp only [coeff_single_exp (G x.1) (hexp x.1), hlin1, smul_eq_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set Y : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (n b)) C :=
    fun y => ∑ e, l y.1 y.2 e • A ⟨y.1, e⟩ with hYdef
  have hY : ∀ y, 2 ≤ (Y y - X y).order := by
    intro y
    rw [GlobalTheory.FormalSeries.two_le_order_iff]
    refine ⟨by simp [hYdef, hA0], fun z => ?_⟩
    rw [map_sub, hYdef]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_smul, hA1, smul_eq_mul, coeff_X,
      Finsupp.single_left_inj one_ne_zero]
    simp_rw [Finset.mul_sum]
    rw [sub_eq_zero]
    have key : ∀ a : Fin (n y.1), ∑ e, l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0)
        = (if y.2 = a then 1 else 0) * if z = ⟨y.1, a⟩ then 1 else 0 := by
      intro a
      rw [← hldual y.1 y.2 a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    have key2 : ∑ e : Fin (d y.1), ∑ a : Fin (n y.1),
        l y.1 y.2 e * (u y.1 a e * if z = ⟨y.1, a⟩ then (1 : C) else 0) = if z = y then 1 else 0 := by
      rw [Finset.sum_comm]
      simp_rw [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact key2
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hA0
  unfold content
  refine le_iInf₂ fun α hα => ?_
  set L : (Σ b, Fin (n b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun y => ∑ e, l y.1 y.2 e • X ⟨y.1, e⟩ with hLdef
  have hLint : ∀ y, MvIsInt v (L y) := fun y =>
    (intSub v _).sum_mem fun e _ => isInt_smul_X v (hlint y.1 y.2 e) _
  set f := α.prod fun y k => L y ^ k with hfdef
  have hfint : MvIsInt v f := isInt_prod v L hLint α
  have hsub : subst A f = α.prod fun y k => Y y ^ k := by
    rw [hfdef, ← coe_substAlgHom hAs, map_finsuppProd]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_pow, hLdef, hYdef, map_sum, map_smul, substAlgHom_X]
  have hord := lead_prod Y hY α
  rw [← hsub] at hord
  have hdeg : ∀ β ∈ P.support, β.degree = D := fun β hβ => by
    have := hP (MvPolynomial.mem_support_iff.mp hβ)
    rw [← this, Finsupp.degree_eq_weight_one]; rfl
  have hval : derivAt0 P (subst A f) = P.coeff α * mfact α := by
    unfold derivAt0
    rw [Finset.sum_eq_single α]
    · rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord (Nat.lt_succ_self _),
        coeff_monomial_same, mul_one]
    · intro β hβ hne
      rw [GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub hord
        (by rw [hdeg β hβ, ← hdeg α hα]; exact Nat.lt_succ_self _), coeff_monomial,
        if_neg hne, mul_zero]
    · intro h; exact absurd hα h
  unfold depth
  refine (iInf_le _ ⟨f, hfint⟩).trans (le_of_eq ?_)
  rw [← hAdef, hval]

end

end GlobalTheory.FGDepth.DepthLeContent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem disc_eq_trivV (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)) : V = trivV N (disc.obj F) := by
  ext n U x
  have h := congrArg
    (fun φ : (disc.obj F).obj (op (SimplexCategory.mk 0)) ⟶ (ofCat (glCat N)).obj n =>
      ConcreteCategory.hom (φ.app U) x)
    (V.naturality (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op)
  simp at h
  show (ConcreteCategory.hom ((V.app n).app U)) x = _
  rw [h]
  generalize (ConcreteCategory.hom ((V.app (op (SimplexCategory.mk 0))).app U)) x = y
  refine CategoryTheory.Functor.ext (fun i => rfl) ?_
  intro i j f
  change (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)).map (𝟙 (0 : Fin 1)) = _
  refine (CategoryTheory.Functor.map_id (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)) 0).trans ?_
  change 𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) =
    eqToHom (rfl : SingleObj.star (GL (Fin N) (Scheme.Γ.obj U)) = _) ≫
      𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) ≫ eqToHom rfl
  erw [Category.id_comp, Category.id_comp]
  exact (eqToHom_refl _ _).symm

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeBaseChangeOfIntegralClosureEtaleStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
  @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_comap_baseChange_atPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleComplexStaircaseLocallyExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComplex_staircase_locally_exact : ∀ (R : Type) [CommRing R] (q e : ℕ) (K : Cx R) (a : ℤ), (∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0) → (∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * e) • y = 0) → (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), e • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = q • y) → (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), q • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = e • y) → (∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b) → ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), (Loc U fun V g => ∃ y : Sec (K.X (n + 1)) V, Sec.map (K.d n (n + 1)) (Sec.res g x) = q • y) → Loc U fun V g => ∃ (u : Sec (K.X (n - 1)) V) (y : Sec (K.X n) V), Sec.res g x = Sec.map (K.d (n - 1) n) u + q • y := by
  first | (exact @GlobalTheory.EtC.staircase_loc) | (exact GlobalTheory.EtC.staircase_loc) | (intros; apply GlobalTheory.EtC.staircase_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g → ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B), EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  first | (exact @GlobalTheory.EtC.etFF_descends_of_isColimit) | (exact GlobalTheory.EtC.etFF_descends_of_isColimit) | (intros; apply GlobalTheory.EtC.etFF_descends_of_isColimit  <;> assumption)
end

