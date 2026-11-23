module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostBounds_two_mul_rpow_log_sq_le (eps : ℝ) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 2 * x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 4 * eps / 5) (by positivity)).bound
    (c := 1 / 2) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg h2.le _)] at h1
  have e : x ^ eps = x ^ (eps / 5) * x ^ (4 * eps / 5) := by
    rw [← Real.rpow_add h2]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos h2 _
  rw [e]
  nlinarith

theorem hostBounds_log_of_sqrt_exp_lt {a y : ℝ} (h : Real.sqrt (Real.exp a) < y) :
    a / 2 ≤ Real.log y := by
  have h0 : 0 < Real.sqrt (Real.exp a) := Real.sqrt_pos.mpr (Real.exp_pos a)
  have h1 := Real.log_le_log h0 h.le
  rwa [Real.log_sqrt (Real.exp_pos a).le, Real.log_exp] at h1

private theorem hostBounds_rd (R : Ranks) (H : Host R) :
    1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have hq0 : (1 : ℝ) ≤ H.q := by exact_mod_cast H.hyp.1.one_le
  have hd0 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.hyp.2.1.one_le
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hqd : (1 : ℝ) ≤ (H.q : ℝ) * H.d := one_le_mul_of_one_le_of_one_le hq0 hd0
  have hs1 : 1 ≤ Real.sqrt ((H.q : ℝ) * H.d) := Real.one_le_sqrt.mpr hqd
  have hs2 : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ (H.q : ℝ) * H.d by positivity)
    nlinarith
  obtain ⟨hrd1, hrd2, -⟩ := factRd R H
  have he0 : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
  have hB : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlo : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨(one_le_mul_of_one_le_of_one_le hlo (Real.one_le_sqrt.mpr hd0)).trans hrd1, hrd2.trans ?_⟩
  have : (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) :=
    mul_le_mul (by linarith) hs2 (Real.sqrt_nonneg _) hS0.le
  rwa [mul_assoc]

theorem hostBounds_ez {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.2.2.2.2.2.2.2.2.1

theorem hostBounds_one_le_log_div {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H)
    (hx : Real.exp C8 ≤ s.x) : 1 ≤ Real.log s.x / s.J := by
  rw [one_le_div (lt_of_lt_of_le one_pos s.one_le_J)]
  exact h.2.2.2.2.2.2.2.2.1.trans ((Real.le_log_iff_exp_le (by linarith [s.one_lt_alt])).mpr hx)

private theorem hostBounds_win {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    s.x ^ (s.ez / 5) ≤ Y ^ (s.eps / 5) ∧ Y ^ (s.eps / 5) ≤ s.x ^ (s.eps / 5) ∧
      (Real.log s.x / s.J) ^ 2 ≤ Real.log Y ^ 2 ∧ Real.log Y ^ 2 ≤ Real.log s.x ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hJ : 0 < s.J := lt_of_lt_of_le one_pos s.one_le_J
  have he := s.eps_pos
  have hp : 0 < s.x ^ (1 / s.J) := Real.rpow_pos_of_pos hx0 _
  have hY : 0 < Y := hp.trans_le h1
  have hl : Real.log s.x / s.J ≤ Real.log Y := by
    have := Real.log_le_log hp h1
    rw [Real.log_rpow hx0] at this
    calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
      _ ≤ _ := this
  have hl0 : 0 ≤ Real.log s.x / s.J := div_nonneg (Real.log_pos hx1).le hJ.le
  refine ⟨?_, Real.rpow_le_rpow hY.le h2 (by positivity), pow_le_pow_left₀ hl0 hl 2,
    pow_le_pow_left₀ (hl0.trans hl) (Real.log_le_log hY h2) 2⟩
  have e : s.x ^ (s.ez / 5) = (s.x ^ (1 / s.J)) ^ (s.eps / 5) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; unfold Scale.ez; ring
  rw [e]
  exact Real.rpow_le_rpow hp.le h1 (by positivity)

theorem hostBounds : ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C8 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → s.x ^ (s.ez / 5) / 2 ≤ Real.log H.q ∧ Real.log H.q ≤ s.x ^ (s.eps / 5) ∧ s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2 ≤ Real.log H.d ∧ Real.log H.d ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ 1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ Real.log H.rdE ≤ s.L ∧ Real.log H.pde ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log H.pde' ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  intro eps C8 he _ hC
  obtain ⟨x0, hx0⟩ := hostBounds_two_mul_rpow_log_sq_le eps he
  refine ⟨x0, fun s R H hse hx _ hH => ?_⟩
  subst hse
  obtain ⟨⟨Y, hW, hq, -, hq1, hq2, hd, -, hd1, hd2, -, -, hNY⟩, -, -, ⟨hp, hp'⟩, -⟩ := hH
  obtain ⟨w1, w2, w3, w4⟩ := hostBounds_win hW
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have p1 : 0 < s.x ^ (s.ez / 5) := Real.rpow_pos_of_pos hxp _
  have v1 : s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 :=
    mul_le_mul w1 w3 (sq_nonneg _) (p1.le.trans w1)
  have v2 : Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_le_mul w2 w4 (sq_nonneg _) (Real.rpow_pos_of_pos hxp _).le
  have hq0 : (0 : ℝ) < H.q := by exact_mod_cast hq.pos
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have lq : Real.log H.q ≤ Y ^ (s.eps / 5) := (Real.log_le_iff_le_exp hq0).mpr hq2
  have ld : Real.log H.d ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 := (Real.log_le_iff_le_exp hd0).mpr hd2
  have lq' : Y ^ (s.eps / 5) / 2 ≤ Real.log H.q := hostBounds_log_of_sqrt_exp_lt hq1
  have ld' : Y ^ (s.eps / 5) * Real.log Y ^ 2 / 2 ≤ Real.log H.d := hostBounds_log_of_sqrt_exp_lt hd1
  have hN : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by linarith
  obtain ⟨hrd1, hrd3⟩ := hostBounds_rd R H
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by positivity
  have hpl : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 →
      Real.log p ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    intro p hpp hle
    have h1 := Real.log_le_log (by exact_mod_cast hpp.pos) hle
    rw [Real.log_rpow hNpos] at h1
    have h2 := mul_le_mul_of_nonneg_left hN (show 0 ≤ C8 by linarith)
    linarith
  exact ⟨by linarith, lq.trans w2, by linarith, ld.trans v2, hN, hrd1, (factRd R H).2.1,
    ((Real.log_le_log (by linarith) hrd3).trans hN).trans (hx0 _ hx),
    hpl _ H.pde_prime hp, hpl _ H.pde'_prime hp'⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace ColSharp

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

noncomputable def colUp (i : ℕ) : Fn X 0 →ₗ[ℂ] Fn X i :=
  Nat.rec (motive := fun i => Fn X 0 →ₗ[ℂ] Fn X i) LinearMap.id (fun i g => KT X i ∘ₗ g) i

theorem colUp_eq (i : ℕ) (φ : Fn X 0) : colUp X i φ = Formalism.ThetaLiftIndependence.chainOpM X.C.wt X.C.Kmap i φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show KT X i (colUp X i φ) = _
    rw [ih]; rfl

theorem colT_eq (φ : Fn X 0) : colT X φ = colUp X D.R.m φ := (colUp_eq X _ φ).symm

theorem emb_mem (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem fold_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (l : List X.A.vT) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ ∈ X.fm.Fi i := by
  induction l with
  | nil => exact hφ
  | cons v l ih => exact hF.1 i hi v _ ih

theorem Uprod_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) : Uprod X i w φ ∈ X.fm.Fi i := fold_mem hF hi _ hφ

theorem Upow_mem (hF : FormsStable X) (w : D.what₂.places.Pl) (n : ℕ) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : (Uprod X 0 w ^ n) φ ∈ X.fm.Fi 0 := by
  induction n with
  | zero => exact hφ
  | succ n ih => rw [pow_succ']; exact Uprod_mem hF (Nat.zero_le _) w ih

theorem colUp_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : colUp X i φ ∈ X.fm.Fi i := by
  induction i with
  | zero => exact hφ
  | succ i ih => exact hF.2.2 i hi _ (ih (Nat.le_of_succ_le hi))

theorem scalar_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) :
    ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ s := by
  have h : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) := by
    have : ((D.R.t + 1 : ℕ) : ℝ) = ((2 * s : ℕ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  rw [h, Real.rpow_natCast]; push_cast; rfl

theorem fold_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (l : List X.A.vT) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X (i + 1) v).comp g) LinearMap.id : Fn X (i + 1) →ₗ[ℂ] Fn X (i + 1)) (KT X i φ) =
      (X.A.T : ℂ) ^ (s * l.length) •
        KT X i ((l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.foldr_cons, LinearMap.comp_apply, LinearMap.comp_apply, ih, map_smul,
      h4 i hi v _ (fold_mem hF hi.le l hφ), scalar_eq hs, smul_smul, ← pow_add, List.length_cons, Nat.mul_succ]

theorem Uprod_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    Uprod X (i + 1) w (KT X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card) • KT X i (Uprod X i w φ) := by
  rw [← Finset.length_toList]; exact fold_comm hF h4 hs hi _ hφ

theorem Uprod_colUp (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    Uprod X i w (colUp X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card * i) • colUp X i (Uprod X 0 w φ) := by
  induction i with
  | zero => simp [colUp]
  | succ i ih =>
    have hi' : i < D.R.m := hi
    show Uprod X (i + 1) w (KT X i (colUp X i φ)) = _ • KT X i (colUp X i (Uprod X 0 w φ))
    rw [Uprod_comm hF h4 hs hi' w (colUp_mem hF hi'.le hφ), ih hi'.le, map_smul, smul_smul, ← pow_add,
      Nat.mul_succ, Nat.add_comm (s * _)]

theorem chain_into (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s)
    (w : D.what₂.places.Pl) (e : ℕ)
    (hU : ∀ i, i < D.R.m → Into X w (fun φ => tpow X e • Uprod X (i + 1) w (KT X i φ))
      (X.fm.S i w) (X.fm.S (i + 1) w)) {i : ℕ} (hi : i ≤ D.R.m) :
    Into X w (fun φ => (X.A.T : ℂ) ^ (i * e + s * (VVT X w).card * ∑ j ∈ Finset.range (i + 1), j) •
      colUp X i ((Uprod X 0 w ^ i) φ)) (X.fm.S 0 w) (X.fm.S i w) := by
  induction i with
  | zero => intro x hx; exact ⟨x, hx, by simp [colUp]⟩
  | succ i ih =>
    have hi' : i < D.R.m := hi
    intro x hx
    obtain ⟨y, hy, hy'⟩ := ih hi'.le x hx
    obtain ⟨z, hz, hz'⟩ := hU i hi' y hy
    refine ⟨z, hz, ?_⟩
    have hm := Upow_mem hF w i (emb_mem X 0 x)
    have key := Uprod_colUp hF h4 hs hi w hm
    have e1 : colUp X (i + 1) ((Uprod X 0 w ^ i) (X.fm.emb 0 x)) =
      KT X i (colUp X i ((Uprod X 0 w ^ i) (X.fm.emb 0 x))) := rfl
    rw [hz']
    beta_reduce at hy' ⊢
    rw [hy', map_smul, map_smul, ← e1, key, pow_succ' (Uprod X 0 w) i, Module.End.mul_apply, tpow,
      smul_smul, smul_smul, ← pow_add, ← pow_add, Finset.sum_range_succ _ (i + 1)]
    congr 2
    ring

theorem card_VVT {w : D.what₂.places.Pl} (h : X.fm.seenP w = true) : (VVT X w).card = (tops D).card := by
  unfold VVT
  rw [if_pos h]
  refine Finset.card_bij (fun v _ => X.fm.tauOf w v) (fun v hv => (Finset.mem_filter.1 hv).2)
    (fun a _ b _ hab => (X.fm.tauOf w).injective hab) (fun τ hτ => ?_)
  exact ⟨(X.fm.tauOf w).symm τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hτ⟩, by simp⟩

theorem expT_nonneg (hW : WtBounds X) (w : D.what₂.places.Pl) : 0 ≤ expT X w := by
  refine mul_nonneg (Int.natCast_nonneg _) (Finset.sum_nonneg fun v hv => hW.1 _ ?_)
  unfold VVT at hv
  split_ifs at hv
  · exact (Finset.mem_filter.1 hv).2
  · simp at hv

theorem val_pow {w : D.what₂.places.Pl} (hw : OverT X w) (k : ℕ) :
    D.what₂.places.val w ((X.A.T : D.what₂.LL) ^ k) = (((D.what₂.places.ramIdx w * k : ℕ) : ℤ) : WithTop ℤ) := by
  have h := D.what₂.places.val_resChar w
  rw [show D.what₂.places.resChar w = X.A.T from hw] at h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1

theorem quot_mem {w : D.what₂.places.Pl} (hw : OverT X w) {c : D.what₂.LL} {n : ℤ}
    (hc : D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ)) (a b : ℕ)
    (h : ((D.what₂.places.ramIdx w * b : ℕ) : ℤ) ≤ n) :
    c * (X.A.T : D.what₂.LL) ^ a * ((X.A.T : D.what₂.LL) ^ b)⁻¹ ∈ Ow D w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hc, val_pow hw, val_pow hw]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  have : (0 : ℤ) ≤ ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) := Int.natCast_nonneg _
  exact_mod_cast (by omega : (0 : ℤ) ≤ n + ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) + -((D.what₂.places.ramIdx w * b : ℕ) : ℤ))

theorem loss_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) (w : D.what₂.places.Pl) :
    ((D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      s * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) = (D.R.m : ℝ) * ET X w := by
  unfold ET
  by_cases h : X.fm.seenP w = true
  · rw [if_pos h, if_pos h, card_VVT h]
    unfold ETpi
    have h1 : ((D.R.t : ℝ) + 1) = 2 * s := by exact_mod_cast hs
    have h2 : ((∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) * 2 = ((D.R.m : ℝ) + 1) * D.R.m := by
      have := Finset.sum_range_id_mul_two (D.R.m + 1)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    rw [h1]
    generalize (∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) = S at h2 ⊢
    push_cast
    linear_combination ((s : ℝ) * ((tops D).card : ℝ) / 2) * h2
  · have : VVT X w = ∅ := by unfold VVT; rw [if_neg h]
    rw [if_neg h, if_neg h, this]
    simp

end ColSharp


open ColSharp in
theorem levelChainSharpColumnValuation_of_stability : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u),
    FormsStable X → LevelChainUOperatorCommutation X → UKSharp X → WtBounds X → Conclusion5Sharp X := by
  intro D u X hF h4 hU hW w hw c n hc hn x' hx'
  obtain ⟨x, hx, hxx⟩ := hx'
  obtain ⟨s0, hs0⟩ := D.R.t_odd
  have hs : D.R.t + 1 = 2 * (s0 + 1) := by omega
  obtain ⟨y, hy, hy'⟩ := chain_into hF h4 hs w _ (hU w hw) (le_refl D.R.m) x hx.1
  rw [← loss_eq (X := X) hs w] at hn
  set b := D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      (s0 + 1) * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j with hb
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (expT_nonneg hW w)
  have hmem := quot_mem hw hc a b (by exact_mod_cast hn)
  refine ⟨(⟨_, hmem⟩ : Ow D w) • y, (X.fm.S D.R.m w).smul_mem _ hy, ?_⟩
  have hT : (X.A.T : ℂ) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast X.A.T_prime.ne_zero)
  beta_reduce at hy' ⊢
  rw [Subring.smul_def, LinearMap.map_smulₛₗ, hy', hxx, colT_eq, ha, LinearMap.smul_apply, map_smul,
    smul_smul, smul_smul, zpow_natCast]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  field_simp

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogLevelGroupLeAndLevelLarge
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem natCard_GL_zmod_le (r g : ℕ) (hg : 0 < g) :
    Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r * r) := by
  haveI : NeZero g := ⟨hg.ne'⟩
  have h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  have h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r) := by
    show Nat.card (Fin r → Fin r → ZMod g) = _
    simp [Nat.card_fun, pow_mul]
  exact h2 ▸ h1

theorem log_levelGroup_le_and_level_large : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, lam0 (Fm.D x i) ≤ x ^ (15 : ℝ) ∧ 8 * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.r : ℝ) / ((min ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) : ℕ) : ℝ) ≤ 1 / 3 ∧ 1 ≤ (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := poly_sizes_ranks_weights eps Fm
  refine ⟨max x0 8, fun x hx hx1 i => ?_⟩
  obtain ⟨hCt, hf, hm, hk, -, -, -, hLx, -, hL1, hL2, hb, -⟩ :=
    hx0 x (le_trans (le_max_left _ _) hx) hx1 i
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLe := Fm.L_eps x i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have hb1 : 1 ≤ L.sc.b := le_trans (Real.one_le_rpow h1x (by linarith)) hb
  have h2m := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by omega
    exact_mod_cast this
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrk' : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
  have hg8 : ∀ j, (D.R.k : ℝ) ^ 8 ≤ (D.host.g j : ℝ) := fun j =>
    le_trans (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hb1) 8) (hG j j).1
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) ^ 8 := by positivity
  have hgpos : ∀ j, 0 < D.host.g j := fun j => by
    have := lt_of_lt_of_le hkpos (hg8 j)
    exact_mod_cast this
  have hlog : ∀ j, Real.log (D.host.g j : ℝ) ≤ x := fun j => by
    refine (hG j j).2.2.trans ?_
    unfold szTh Scale.L
    rw [hLx, hLe, ← Real.rpow_add h0x]
    calc x ^ (eps / 100 + eps) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  refine ⟨?_, ?_, hb1⟩
  · have hc : D.what₂.restRowsFiniteGroupCard ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by
      rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_pow, pow_mul _ (D.R.r * D.R.r),
        pow_mul _ (D.R.r * D.R.r)]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 0)) _)
        (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 1)) _)
    have hc' : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤
        ((D.host.g 0 : ℝ) * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by exact_mod_cast hc
    have hp : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos
    have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast hgpos 0
    have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast hgpos 1
    have hr5 : (D.R.r : ℝ) ≤ 2 * x ^ (5 : ℝ) := by linarith
    unfold lam0
    refine (Real.log_le_log hp hc').trans ?_
    rw [Real.log_pow, Real.log_mul hg0.ne' hg1.ne']
    push_cast
    have hl0 : 0 ≤ Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
      add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    have hl2 : Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) ≤ 2 * x := by
      linarith [hlog 0, hlog 1]
    have e5 : x ^ (5 : ℝ) = x ^ 5 := by exact_mod_cast Real.rpow_natCast x 5
    have e3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
    have e15 : x ^ (15 : ℝ) = x ^ 15 := by exact_mod_cast Real.rpow_natCast x 15
    rw [e5] at hr5
    rw [e3] at hf
    rw [e15]
    calc (D.R.r : ℝ) * D.R.r * D.R.f * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ))
        ≤ (2 * x ^ 5) * (2 * x ^ 5) * x ^ 3 * (2 * x) := by gcongr
      _ = 8 * x ^ 14 := by ring
      _ ≤ x * x ^ 14 := by gcongr
      _ = x ^ 15 := by ring
  · have hmin : (D.R.k : ℝ) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
      push_cast
      exact le_min (hg8 0) (hg8 1)
    rw [div_le_iff₀ (lt_of_lt_of_le hkpos hmin)]
    have h1 : 8 * (D.R.f : ℝ) * D.R.r ≤ 8 * (D.R.k : ℝ) * (2 * D.R.k) := by gcongr
    have h2 : (5 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 6 := by gcongr
    have h3 : (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by ring
    have h4 : (5 : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (D.R.k : ℝ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NuRowNonnegLeTenMul
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem nuRow_zero_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (hk : 0 < D.R.k) :
    nuRow D u j τ 0 ≤ ((((D.hcW u τ).u ⟨0, hk⟩ : ℚ)) : ℝ) + wSz D j τ := by
  unfold nuRow srcPar
  rw [dite_eq_left hk]
  have h1 : 1 ≤ D.R.N j := by unfold Ranks.N; omega
  have h1' : (1 : ℝ) ≤ D.R.N j := by exact_mod_cast h1
  have h2 : (0 : ℝ) ≤ D.R.N (j - 1) := Nat.cast_nonneg _
  push_cast
  linarith

theorem nuRow_nonneg_le_ten_mul : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ nuRow (Fm.D x i) u j τ l ∧ nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.HCEntries.entries eps Fm
  refine ⟨x0, fun x hx hx1 i u j hj τ l hl => ?_⟩
  obtain ⟨hw, hu, -⟩ := h x hx hx1 i
  obtain ⟨-, hw3, hwe⟩ := hw j hj τ
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have h3 := (abs_le.1 (hu u τ ⟨0, hk⟩)).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

end GlobalTheory
end

