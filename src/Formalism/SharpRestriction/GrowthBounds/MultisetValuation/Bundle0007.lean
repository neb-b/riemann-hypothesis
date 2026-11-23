module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RationalLowerBounds
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmNEqZero
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open scoped Classical

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}


variable (R p) in
def nm_N (x : K) : ℝ := if x = 0 then 0 else (p : ℝ) ^ (-nm_v R p x)

theorem nm_N_zero : nm_N R p (0 : K) = 0 := by
  simp [nm_N]

theorem nm_N_of_ne {x : K} (hx : x ≠ 0) : nm_N R p x = (p : ℝ) ^ (-nm_v R p x) := by
  simp [nm_N, hx]

theorem nm_pR (h : nm_Hyp R p) : (1 : ℝ) < p := by
  exact_mod_cast h.one_lt

theorem nm_N_nonneg (h : nm_Hyp R p) (x : K) : 0 ≤ nm_N R p x := by
  unfold nm_N
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le

theorem nm_N_mul (h : nm_Hyp R p) (x y : K) : nm_N R p (x * y) = nm_N R p x * nm_N R p y := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  by_cases hy : y = 0
  · simp [nm_N, hy]
  rw [nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add,
    Real.rpow_add (zero_lt_one.trans (nm_pR h))]

theorem nm_N_eq_zero (h : nm_Hyp R p) (x : K) : nm_N R p x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  · rw [nm_N_of_ne hx]
    simp only [hx, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'

theorem nm_N_add (h : nm_Hyp R p) (x y : K) : nm_N R p (x + y) ≤ max (nm_N R p x) (nm_N R p y) := by
  by_cases hx : x = 0
  · simp only [hx, zero_add, nm_N_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · simp only [hy, add_zero, nm_N_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, nm_N_zero]
    exact le_max_of_le_left (nm_N_nonneg h x)
  rw [nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]
  have hp1 : (1 : ℝ) ≤ p := (nm_pR h).le
  have hm := nm_v_add h hx hy hxy
  rcases le_total (nm_v R p x) (nm_v R p y) with hle | hle
  · rw [min_eq_left hle] at hm
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · rw [min_eq_right hle] at hm
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))

theorem nm_N_p (h : nm_Hyp R p) : nm_N R p (p : K) = (p : ℝ)⁻¹ := by
  rw [nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]

theorem nm_N_le_one (h : nm_Hyp R p) (x : K) : nm_N R p x ≤ 1 ↔ x ∈ R := by
  by_cases hx : x = 0
  · subst hx
    simp only [nm_N_zero, zero_le_one, true_iff]
    exact R.zero_mem
  rw [nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]
  have e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  rw [e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]

def nm_abs (h : nm_Hyp R p) : AbsoluteValue K ℝ where
  toFun := nm_N R p
  map_mul' := nm_N_mul h
  nonneg' := nm_N_nonneg h
  eq_zero' := nm_N_eq_zero h
  add_le' x y := le_trans (nm_N_add h x y) (max_le_add_of_nonneg (nm_N_nonneg h x) (nm_N_nonneg h y))

theorem nm_extG {K : Type} [Field K] (N : AbsoluteValue K ℝ) (hna : ∀ x y, N (x + y) ≤ max (N x) (N y)) (c : K)
    (hc : 1 < N c) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra K K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ∀ x, ‖algebraMap K K' x‖ = N x := by
  let nK : NormedField K := N.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = N x := fun _ => rfl
  have hnatK : ∀ n : ℕ, N (n : K) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact le_trans (hna _ _) (max_le ih (by simp))
  have hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K) := fun n =>
    map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n
  have hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1 := by
    intro n
    rw [← hcast, UniformSpace.Completion.norm_coe]
    exact hnatK n
  have uC : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC
  let nnC : NontriviallyNormedField (UniformSpace.Completion K) :=
    { (inferInstance : NormedField (UniformSpace.Completion K)) with
      non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }
  let nL : NormedField (AlgebraicClosure (UniformSpace.Completion K)) :=
    spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
  have hext : ∀ z : UniformSpace.Completion K,
      ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖ :=
    fun z => spectralNorm_extends z
  let aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K)) :=
    ((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp
      (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra
  refine ⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩
  · apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro n
    have := hext (n : UniformSpace.Completion K)
    rw [map_natCast] at this
    rw [this]
    exact hnatC n
  · intro x
    show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
      (x : UniformSpace.Completion K)‖ = N x
    rw [hext, UniformSpace.Completion.norm_coe]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_ya (_X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))

def nc_zc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) + Formalism.MainNotions.G.cG L


open Classical in
def nc_Loc (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (_hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  let p := D.what₂.places.resChar w
  let v := Y.vOf u w hg t0
  let Fl := Y.Fl u w hg
  Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s -
              ∑ s ∈ (Fl.TT v).filter IsOddPos, ∑' e : ℕ,
                min (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1)) (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            ∑ s ∈ Fl.TT v, ∑' e : ℕ, (if Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1) then 0 else
              max 0 (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1) - nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
  (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) ∧
  (∀ s ∈ Fl.TT v, ∀ e, 2 * e + 1 ∈ dSet (Fl.TT v) s → Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1))

def nc_De (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  de (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
      ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
    Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0

def nc_Need (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Loc D L X Y K hT u w hg t0 j ∧ nc_De D L X Y K u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

open Classical in
theorem stmtNumE_of (C₀ : ℝ) (h : nc_Need C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform := by
  have two_le : ∀ (p : ℕ) (x : ℝ), 1 ≤ Real.logb (p : ℝ) x → 2 ≤ p := by
    intro p x hx
    by_contra hc
    have hp2 : p < 2 := by omega
    interval_cases p <;> simp [Real.logb] at hx <;> linarith
  have geom : ∀ p : ℕ, 2 ≤ p →
      HasSum (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have hp0 : (0 : ℝ) < p := by linarith
    have hr0 : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
    have hr1 : (1 / (p : ℝ)) ^ 2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (pow_pos hp0 2)]; nlinarith
    have hh := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (p : ℝ))
    have hf : (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) =
        fun i : ℕ => 1 / (p : ℝ) * ((1 / (p : ℝ)) ^ 2) ^ i := by
      funext e
      rw [← pow_mul, ← pow_succ', one_div_pow]
    have hv : Formalism.MainNotions.FormalGroupSystem.gam p = 1 / (p : ℝ) * (1 - (1 / (p : ℝ)) ^ 2)⁻¹ := by
      rw [show (1 : ℝ) - (1 / (p : ℝ)) ^ 2 = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [div_pow, one_pow, sub_div, div_self (pow_ne_zero 2 hp0.ne')], inv_div]
      unfold Formalism.MainNotions.FormalGroupSystem.gam
      rw [← mul_div_assoc, pow_two, ← mul_assoc, one_div_mul_cancel hp0.ne', one_mul]
    rw [hf, hv]
    exact hh
  have minsum : ∀ (p : ℕ), 2 ≤ p → ∀ (a b : ℝ) (C Z : ℕ → ℝ), b ≤ a → 0 ≤ a →
      (∀ e, 0 ≤ C e) → (∀ e, C e ≤ Z e) →
      ∑' e : ℕ, min (a / (p : ℝ) ^ (2 * e + 1)) (C e) -
        ∑' e : ℕ, min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤ Formalism.MainNotions.FormalGroupSystem.gam p * (a - b) := by
    intro p hp a b C Z hba ha hC0 hCZ
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsa : Summable (fun e : ℕ => a / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left a).congr (fun e => mul_one_div a _)
    have hsb : Summable (fun e : ℕ => b / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left b).congr (fun e => mul_one_div b _)
    have hf1 : Summable (fun e : ℕ => min (a / (p : ℝ) ^ (2 * e + 1)) (C e)) :=
      Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (hq e).le) (hC0 e))
        (fun e => min_le_left _ _) hsa
    have hf2 : Summable (fun e : ℕ => min (b / (p : ℝ) ^ (2 * e + 1)) (Z e)) := by
      rcases le_or_gt 0 b with hb | hb
      · exact Summable.of_nonneg_of_le
          (fun e => le_min (div_nonneg hb (hq e).le) ((hC0 e).trans (hCZ e)))
          (fun e => min_le_left _ _) hsb
      · refine hsb.congr (fun e => ?_)
        have hneg : b / (p : ℝ) ^ (2 * e + 1) < 0 := div_neg_of_neg_of_pos hb (hq e)
        exact (min_eq_left (by linarith [hC0 e, hCZ e])).symm
    have hm := hg.mul_left (a - b)
    rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p)]
    refine hasSum_le (fun e => ?_) (hf1.hasSum.sub hf2.hasSum) hm
    show min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤
      (a - b) * (1 / (p : ℝ) ^ (2 * e + 1))
    have hbq : b / (p : ℝ) ^ (2 * e + 1) ≤ a / (p : ℝ) ^ (2 * e + 1) := by
      gcongr <;> exact hba
    have h1 : min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤ min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) :=
      min_le_min_left _ (hCZ e)
    have h2 : min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤
        a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) := by
      rcases le_total (b / (p : ℝ) ^ (2 * e + 1)) (C e) with hh | hh
      · rw [min_eq_left hh]; linarith [min_le_left (a / (p : ℝ) ^ (2 * e + 1)) (C e)]
      · rw [min_eq_right hh, min_eq_right (hh.trans hbq)]; linarith
    have h3 : a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) =
        (a - b) * (1 / (p : ℝ) ^ (2 * e + 1)) := by ring
    linarith
  have gBcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT S1 S2 : Finset (Fin n)), S1 ⊆ TT → S2 = S1 →
      ∀ (A B : Fin n → ℝ) (C Z : Fin n → ℕ → ℝ) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      de ≤ dl →
      Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, B s -
                ∑ s ∈ S1, ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e) - dl ≤
        Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, A s -
          ∑ s ∈ S2, ∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) - de := by
    intro n p hp TT S1 S2 hS hS21 A B C Z dl de hBA hA0 hC0 hCZ hde
    rw [hS21]
    have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p :=
      hasSum_le (fun e => div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg p) _))
        hasSum_zero (geom p hp)
    have key : ∑ s ∈ S1, (∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) -
        ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e)) ≤
        ∑ s ∈ TT, Formalism.MainNotions.FormalGroupSystem.gam p * (A s - B s) :=
      (Finset.sum_le_sum (fun s hs => minsum p hp (A s) (B s) (C s) (Z s) (hBA s (hS hs))
        (hA0 s) (hC0 s) (hCZ s))).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun s hs _ => mul_nonneg hg0 (sub_nonneg.2 (hBA s hs))))
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub] at key
    linarith
  have gAcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT : Finset (Fin n)) (A B : Fin n → ℝ)
      (C Z : Fin n → ℕ → ℝ) (E F : Fin n → ℕ → Prop) (iE : ∀ s e, Decidable (E s e))
      (iF : ∀ s e, Decidable (F s e)) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      (∀ s ∈ TT, ∀ e, F s e → E s e) → de ≤ dl →
      ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) -
          dl ≤
        ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) -
          de := by
    intro n p hp TT A B C Z E F iE iF dl de hBA hA0 hC0 hCZ hFE hde
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsum : ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
        ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
      refine Finset.sum_le_sum (fun s hs => ?_)
      have hle : ∀ e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
            @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
        intro e
        have hbq : B s / (p : ℝ) ^ (2 * e + 1) ≤ A s / (p : ℝ) ^ (2 * e + 1) := by
          gcongr <;> exact hBA s hs
        by_cases hF : F s e
        · simp only [if_pos (hFE s hs e hF), if_pos hF, le_refl]
        · rw [if_neg hF]
          split_ifs
          · exact le_max_right _ _
          · exact max_le (le_max_right _ _) (le_trans (by linarith [hCZ s e]) (le_max_left _ _))
      have h0 : ∀ e : ℕ,
          0 ≤ @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) := by
        intro e
        split_ifs
        · exact le_refl 0
        · exact le_max_left _ _
      have hR : Summable (fun e : ℕ =>
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0)) := by
        refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
          ((hg.summable.mul_left (A s)).congr (fun e => mul_one_div (A s) _))
        · split_ifs
          · exact le_refl 0
          · exact le_max_right _ _
        · split_ifs
          · exact div_nonneg (hA0 s) (hq e).le
          · exact max_le (by linarith [hC0 s e]) (div_nonneg (hA0 s) (hq e).le)
      exact hasSum_le hle (Summable.of_nonneg_of_le h0 hle hR).hasSum hR.hasSum
    linarith
  refine ⟨C₀, ?_⟩
  intro D L X Y K h1 h2 h3 hr hx hS hT hTied u w hg hlog t0 ht0 j hj
  obtain ⟨hLoc, hDe, hPr⟩ := h D L X Y K h1 h2 h3 ⟨hr, hx⟩ hS hT hTied u w hg hlog t0 ht0 j hj
  have hp := two_le _ _ hlog
  dsimp only [nc_Loc] at hLoc
  obtain ⟨hgU, hg0, hya, hal0, hcap, hcap0, hEx⟩ := hLoc
  refine ⟨?_, ?_, hPr⟩
  · rw [hgU]
    unfold Formalism.MainNotions.FormalGroupSystem.gB
    refine gBcmp _ hp _ _ _ ?_ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hx.1
    · ext x
      simp only [Finset.mem_filter]
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · exact hDe
  · rw [hg0]
    unfold Formalism.MainNotions.FormalGroupSystem.gA
    refine gAcmp _ hp _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · intro s hs e he
      exact hEx s hs e he
    · exact hDe

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

