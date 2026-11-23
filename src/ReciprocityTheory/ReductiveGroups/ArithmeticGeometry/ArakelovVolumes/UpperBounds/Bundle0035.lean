module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfO
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def bmul (a b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (mat a τ * mat b τ : Matrix (Fin r) (Fin r) ℂ)

def binv (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_rmul (x a b : Frame X.Ψ r) : rmul (rmul x a) b = rmul x (bmul X a b) := by
  funext τ
  first
    | exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)
    | (ext i j; simp [rmul, bmul, mat, Matrix.mul_assoc])

theorem bmul_mem {a b : Frame X.Ψ r} (ha : a ∈ Bor X.Ψ r) (hb : b ∈ Bor X.Ψ r) :
    bmul X a b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

theorem binv_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : binv X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => hI h⟩
  show ((mat b τ)⁻¹).det ≠ 0
  exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero

theorem rmul_binv (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul x b) (binv X b) = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * (mat b τ)⁻¹ = x τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

theorem lact_rmul (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem lact_lact (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_inv (γ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact, inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

theorem avoid_base (Xa : ArchInM X) (Fl : FlatM X Xa) (j j' : Fin Fl.δ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (hne : γ ≠ 1 ∨ j' ≠ j) (x0 b0 : Frame X.Ψ r) (hb0 : b0 ∈ Bor X.Ψ r)
    (hx : Fl.xs j = rmul x0 b0) (x1 b1 : Frame X.Ψ r) (hb1 : b1 ∈ Bor X.Ψ r)
    (hy : lact γ (Fl.xs j') = rmul x1 b1) (ε : ℝ)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hs1 : ∀ k, Fl.s k x1 = 0) :
    ∀ z ∈ closedBall (0 : V (nd X)) (2 * ε), ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b := by
  intro z hz b hb h1
  have hbc : ∀ c ∈ Bor X.Ψ r, bchar Xa.L c ≠ 0 := by
    intro c hc
    simp only [Bor, Set.mem_setOf_eq] at hc
    unfold bchar
    refine Finset.prod_ne_zero_iff.mpr fun τ _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_
    obtain ⟨hd, ht⟩ := hc τ
    have hT : Matrix.BlockTriangular (mat c τ) id := by
      intro a e h
      exact ht a e h
    rw [Matrix.det_of_upperTriangular hT] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)
  have hzdom : cpt X x0 z ∈ X.dom := hball hz
  have hsz : ∀ k, Fl.s k (cpt X x0 z) = 0 := by
    intro k
    have hv := Fl.s_van k
    simp only [Data.SSgt, Data.SS, Data.IsBddSec, Data.IsSec, Set.mem_setOf_eq] at hv
    have hsec := hv.1.1.1.2.1 (cpt X x0 z) hzdom b hb
    have h0 := hs1 k
    rw [h1, hsec] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hbc b hb)
  have hz0 : z = 0 := hiso z hz hsz
  have hc0 : cpt X x0 0 = x0 := by
    funext τ
    have hm : mat (nmat X 0) τ = 1 := by
      ext a e
      by_cases h : e < a
      · have hne : a ≠ e := ne_of_gt h
        simp only [mat, nmat, Matrix.of_apply, dif_pos h, Matrix.one_apply_ne hne]
        all_goals first | rfl | simp
      · simp only [mat, nmat, Matrix.of_apply, dif_neg h, Matrix.one_apply]
    show mat x0 τ * mat (nmat X 0) τ = x0 τ
    rw [hm, Matrix.mul_one]
    rfl
  have hx0 : rmul (Fl.xs j) (binv X b0) = x0 := by
    rw [hx]
    exact rmul_binv X x0 hb0
  have hcB : bmul X (binv X b0) (bmul X b b1) ∈ Bor X.Ψ r :=
    bmul_mem X (binv_mem X hb0) (bmul_mem X hb hb1)
  have hy' : lact γ (Fl.xs j') = rmul (Fl.xs j) (bmul X (binv X b0) (bmul X b b1)) := by
    rw [hy, h1, hz0, hc0, ← hx0, rmul_rmul X, rmul_rmul X]
  have hj := congrArg (lact γ⁻¹) hy'
  rw [lact_inv] at hj
  have hjj : j = j' := Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hcB hj
  subst hjj
  have hγ1 : γ = 1 := X.Γ_free γ hγ (Fl.xs j) (Fl.xs_mem j) _ hcB hy'
  rcases hne with h | h
  · exact h hγ1
  · exact h rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivD

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma dmin_ne_zero_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  have h' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  intro h0
  have := (h' τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at this
  exact lt_irrefl _ this

private lemma norm_dmin_succ_div_castSucc_pos_of_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
  norm_pos_iff.mpr (div_ne_zero (dmin_ne_zero_of_mem_dom X hx τ _) (dmin_ne_zero_of_mem_dom X hx τ _))

private lemma nfac_pos_of_mem_dom' (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    0 < X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx τ i) _

theorem phla_add (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    phla X (la + la') x = phla X la x + phla X la' x := by
  have hq := norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx
  have hmul : X.nfac (la + la') x = X.nfac la x * X.nfac la' x := by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (hq τ i)]
    congr 1
    simp only [Pi.add_apply, Int.cast_add]
    ring
  unfold phla
  rw [hmul, Real.log_mul (nfac_pos_of_mem_dom' X hx la).ne' (nfac_pos_of_mem_dom' X hx la').ne']
  ring

theorem phla_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (k : ℕ) (la : Wt X.Ψ r) :
    phla X (k • la) x = k * phla X la x := by
  have hq := norm_dmin_succ_div_castSucc_pos_of_mem_dom X hx
  have hpow : X.nfac (k • la) x = X.nfac la x ^ k := by
    unfold Data.nfac
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hq τ i).le]
    congr 1
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    ring
  unfold phla
  rw [hpow, Real.log_pow]
  ring

theorem nfac_sq (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) :
    X.nfac la x ^ 2 = Real.exp (-phla X la x) := by
  unfold phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x ^ 2) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (pow_pos (nfac_pos_of_mem_dom' X hx la) 2)]

theorem pnorm_sq (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) : X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 * Real.exp (-phla X la x) := by
  have h : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  rw [h, mul_pow, nfac_sq X hx la]

variable (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (bb : ℝ)

noncomputable def Ss (z : V (nd X)) : ℝ := ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2

noncomputable def Sw (z : V (nd X)) : ℝ := ∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2

noncomputable def ph0 (z : V (nd X)) : ℝ :=
  phla X Xa.Fp (cpt X x0 z) - Real.log (densF X x0 z) + 1 / 2 * Real.log (Sw X Xa x0 z) -
    bb * rhF X x0 z

theorem Sw_pos {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < Sw X Xa x0 z := by
  obtain ⟨k, hk⟩ := Xa.w_nz _ hz
  unfold Sw
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hk) 2)
    (Finset.single_le_sum (f := fun j => ‖Xa.w j (cpt X x0 z)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ k))

theorem sumL_eq {z : V (nd X)} (hz : z ∈ OmF X x0) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ) :
    ∑ k, X.pnorm Xa.L (P k) (cpt X x0 z) ^ 2 =
      Real.exp (-phla X Xa.L (cpt X x0 z)) * ∑ k, ‖P k (cpt X x0 z)‖ ^ 2 := by
  have hx : cpt X x0 z ∈ X.dom := hz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pnorm_sq X hx]
  ring

private lemma mul_div_exp_mul_rpow_neg_eq_mul_rpow_mul_exp {D f A B T Ss Sw b : ℝ} (hD : 0 < D) (hSs : 0 < Ss) (hSw : 0 < Sw) :
    D * (f / Real.exp (-b) * (Real.exp (-(A + T * B)) * (Real.exp (-B) * Sw) ^ (-T) *
      (Real.exp (-B) * Ss / (Real.exp (-B) * Sw)) ^ (-(T - 1 / 2)))) =
      f * Ss ^ (-(T - 1 / 2)) * Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) := by
  have e1 : Real.exp (-B) * Ss / (Real.exp (-B) * Sw) = Ss / Sw :=
    mul_div_mul_left _ _ (Real.exp_pos _).ne'
  have h1 : Real.exp (-(A + T * B)) * Real.exp (-B * -T) = Real.exp (-A) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Sw ^ (-T) / Sw ^ (-(T - 1 / 2)) = Real.exp (-(1 / 2 * Real.log Sw)) := by
    rw [Real.rpow_def_of_pos hSw, Real.rpow_def_of_pos hSw, ← Real.exp_sub]
    congr 1
    ring
  have h3 : Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) =
      Real.exp (-A) * D * Real.exp (-(1 / 2 * Real.log Sw)) * Real.exp b := by
    rw [show -(A - Real.log D + 1 / 2 * Real.log Sw - b) =
        -A + Real.log D + -(1 / 2 * Real.log Sw) + b by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hD]
  have h4 : f / Real.exp (-b) = f * Real.exp b := by rw [Real.exp_neg, div_inv_eq_mul]
  rw [e1, Real.mul_rpow (Real.exp_pos _).le hSw.le, Real.div_rpow hSs.le hSw.le, ← Real.exp_mul, h4, h3]
  calc _ = D * f * Real.exp b * (Real.exp (-(A + T * B)) * Real.exp (-B * -T)) * Ss ^ (-(T - 1 / 2)) *
        (Sw ^ (-T) / Sw ^ (-(T - 1 / 2))) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem wSk_eq {z : V (nd X)} (hz : z ∈ OmF X x0) (hs : 0 < Ss X Xa Fl x0 z) (F : V (nd X) → ℂ) :
    ENNReal.ofReal (densF X x0 z) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * WSk X Xa Fl (cpt X x0 z)) =
      ENNReal.ofReal (‖F z‖ ^ 2 * Ss X Xa Fl x0 z ^ (-((Xa.T : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb z)) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hSw := Sw_pos X Xa x0 hz
  have hW := sumL_eq X Xa x0 hz Xa.w
  have hS := sumL_eq X Xa x0 hz Fl.s
  have hd : 0 < densF X x0 z := by
    unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.mpr (dmin_ne_zero_of_mem_dom X hx τ _)) _
  unfold Sw at hSw
  unfold Ss at hs
  rw [WSk, if_pos hx, phla_add X hx, phla_nsmul X hx, hW, hS]
  unfold kaF
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos (Real.exp_pos _) hSw),
    ENNReal.ofReal_rpow_of_pos (div_pos (mul_pos (Real.exp_pos _) hs) (mul_pos (Real.exp_pos _) hSw))]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd.le]
  congr 1
  unfold ph0 Ss Sw
  rw [neg_mul]
  exact mul_div_exp_mul_rpow_neg_eq_mul_rpow_mul_exp hd hs hSw

private lemma mul_div_exp_le_pow_mul_rpow_of_exp_neg_mul_le {D f A B n Ss Sw b Cs Cw : ℝ} (hD : 0 < D) (hSs : 0 < Ss) (hSw : 0 < Sw)
    (hn : 1 / 2 ≤ n) (hCs : Real.exp (-B) * Ss ≤ Cs) (hCw : Real.exp (-B) * Sw ≤ Cw) (hf : 0 ≤ f) :
    D * (f / Real.exp (-b) * Real.exp (-(A + n * B))) ≤
      Cs ^ (n - 1 / 2) * Cw ^ (1 / 2 : ℝ) *
        (f * Ss ^ (-(n - 1 / 2)) * Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b))) := by
  have hE := Real.exp_pos (-B)
  have hCs0 : 0 ≤ Cs := le_trans (mul_nonneg hE.le hSs.le) hCs
  have hCw0 : 0 ≤ Cw := le_trans (mul_nonneg hE.le hSw.le) hCw
  have hs' : Real.exp (-B) ≤ Cs / Ss := (le_div_iff₀ hSs).mpr hCs
  have hw' : Real.exp (-B) ≤ Cw / Sw := (le_div_iff₀ hSw).mpr hCw
  have hsplit : Real.exp (-(n * B)) = Real.exp (-B) ^ (n - 1 / 2) * Real.exp (-B) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hE, ← Real.exp_mul]
    congr 1
    ring
  have hk1 : Real.exp (-B) ^ (n - 1 / 2) ≤ Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) := by
    calc Real.exp (-B) ^ (n - 1 / 2) ≤ (Cs / Ss) ^ (n - 1 / 2) :=
          Real.rpow_le_rpow hE.le hs' (by linarith)
      _ = Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) := by
          rw [Real.div_rpow hCs0 hSs.le, Real.rpow_neg hSs.le, div_eq_mul_inv]
  have hk2 : Real.exp (-B) ^ (1 / 2 : ℝ) ≤ Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)) := by
    calc Real.exp (-B) ^ (1 / 2 : ℝ) ≤ (Cw / Sw) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hE.le hw' (by norm_num)
      _ = Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)) := by
          rw [Real.div_rpow hCw0 hSw.le, div_eq_mul_inv, ← Real.rpow_neg hSw.le,
            Real.rpow_def_of_pos hSw]
          congr 2
          ring
  have h3 : Real.exp (-(A - Real.log D + 1 / 2 * Real.log Sw - b)) =
      Real.exp (-A) * D * Real.exp (-(1 / 2 * Real.log Sw)) * Real.exp b := by
    rw [show -(A - Real.log D + 1 / 2 * Real.log Sw - b) =
        -A + Real.log D + -(1 / 2 * Real.log Sw) + b by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hD]
  have h4 : f / Real.exp (-b) = f * Real.exp b := by rw [Real.exp_neg, div_inv_eq_mul]
  have h5 : Real.exp (-(A + n * B)) = Real.exp (-A) * Real.exp (-(n * B)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h3, h4, h5, hsplit]
  have hprod := mul_le_mul hk1 hk2 (by positivity)
    (mul_nonneg (Real.rpow_nonneg hCs0 _) (Real.rpow_nonneg hSs.le _))
  have hc : 0 ≤ D * f * Real.exp b * Real.exp (-A) := by positivity
  calc _ = D * f * Real.exp b * Real.exp (-A) *
        (Real.exp (-B) ^ (n - 1 / 2) * Real.exp (-B) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ D * f * Real.exp b * Real.exp (-A) *
        (Cs ^ (n - 1 / 2) * Ss ^ (-(n - 1 / 2)) *
          (Cw ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2 * Real.log Sw)))) := mul_le_mul_of_nonneg_left hprod hc
    _ = _ := by ring

theorem weightedDensity_bound {z : V (nd X)} (hz : z ∈ OmF X x0) (hs : 0 < Ss X Xa Fl x0 z) (H : V (nd X) → ℂ)
    {Cs Cw : ℝ} (hCs : ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 ≤ Cs)
    (hCw : ∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2 ≤ Cw) (hn : (1 / 2 : ℝ) ≤ (nd X : ℝ)) :
    ENNReal.ofReal (densF X x0 z) * (ENNReal.ofReal (‖H z‖ ^ 2 / kaF X x0 bb z) * weightFunctionOnFrames X Xa (cpt X x0 z)) ≤
      ENNReal.ofReal (Cs ^ ((nd X : ℝ) - 1 / 2) * Cw ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (‖H z‖ ^ 2 * Ss X Xa Fl x0 z ^ (-((nd X : ℝ) - 1 / 2)) *
          Real.exp (-ph0 X Xa x0 bb z)) := by
  have hx : cpt X x0 z ∈ X.dom := hz
  have hSw := Sw_pos X Xa x0 hz
  have hd : 0 < densF X x0 z := by
    unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.mpr (dmin_ne_zero_of_mem_dom X hx τ _)) _
  rw [sumL_eq X Xa x0 hz Fl.s] at hCs
  rw [sumL_eq X Xa x0 hz Xa.w] at hCw
  unfold Sw at hSw
  unfold Ss at hs
  have hCs0 : 0 < Cs := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hs) hCs
  have hCw0 : 0 < Cw := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hSw) hCw
  rw [weightFunctionOnFrames, phla_add X hx, phla_nsmul X hx]
  unfold kaF
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd.le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold ph0 Ss Sw
  rw [neg_mul]
  exact mul_div_exp_le_pow_mul_rpow_of_exp_neg_mul_le hd hs hSw hn hCs hCw (sq_nonneg _)

end UpDivD

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

