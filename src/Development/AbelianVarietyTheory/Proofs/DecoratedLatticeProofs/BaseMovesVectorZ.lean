module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix

noncomputable section

namespace GlobalTheory.MiTop.MoveZ

section Two

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem pr_e (q : SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [map_one, mul_one] at h
  rw [← h, q.pr_sec]

theorem e_mul_sec (q : SplitPt D k) (x : k) : q.e * q.sec x = q.sec x := by
  rw [← q.sec_pr, q.pr_sec]

theorem sec_mul_sec (q : SplitPt D k) (x y : k) : q.sec (x * y) = q.sec x * q.sec y := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, e_mul_sec] at h
  exact h

def chg (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) : k' →+* k where
  toFun x := q.pr (q'.sec x)
  map_one' := by
    have h1 := q'.sec_pr 1
    rw [map_one, mul_one] at h1
    rw [h1, ← h, pr_e]
  map_mul' x y := by rw [sec_mul_sec, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]

theorem sec_chg (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') : q.sec (chg q q' h x) = q'.sec x := by
  change q.sec (q.pr (q'.sec x)) = _
  rw [q.sec_pr, h, e_mul_sec]

theorem chg_pr (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (a : AE D) : chg q q' h (q'.pr a) = q.pr a := by
  change q.pr (q'.sec (q'.pr a)) = _
  rw [q'.sec_pr, ← h, map_mul, pr_e, one_mul]

theorem chg_le (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') :
    valuation k (chg q q' h x) ≤ 1 ↔ valuation k' x ≤ 1 := by
  have h1 := q.int_iff (chg q q' h x)
  rw [sec_chg, ← q'.int_iff] at h1
  exact h1

theorem chg_lt (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') (hx : valuation k (chg q q' h x) < 1) :
    valuation k' x < 1 := by
  by_cases h0 : x = 0
  · subst h0; simp
  by_contra hn
  have h1 : valuation k' x⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hn)
  have h2 := (chg_le q q' h x⁻¹).2 h1
  have h3 : chg q q' h x * chg q q' h x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  have h4 : valuation k (chg q q' h x * chg q q' h x⁻¹) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left h2 zero_le').trans_lt (by rwa [mul_one])
  rw [h3, map_one] at h4
  exact lt_irrefl _ h4

theorem unif_ratio (q : SplitPt D k) (q' : SplitPt D k') {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (h : q.e = q'.e) (Ψ) (ψ : AddChar k Circle)
    (ψ' : AddChar k' Circle) (hψ : (ofSplit q).IsChar Ψ ψ) (hψ' : (ofSplit q').IsChar Ψ ψ')
    (hc : GlobalTheory.SplitWeil.HasConductor ψ 1) (ϖ : kˣ) (ϖ' : k'ˣ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (hu' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ')
    (hz : ∀ z : 𝓞 D.host.E, (ψ (((ϖ⁻¹ : kˣ) : k) * (ofSplit q).pr (z : D.host.E)) : ℂ) =
      ψ' (((ϖ'⁻¹ : k'ˣ) : k') * (ofSplit q').pr (z : D.host.E))) :
    valuation k ((ϖ : k) * chg q q' h ((ϖ'⁻¹ : k'ˣ) : k') - 1) < 1 := by
  have hϖ : valuation k (ϖ : k) < 1 := (hu _).2 le_rfl
  have hone : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hc 1).2 le_rfl y (by simpa using hy)
  have hcomp : ∀ x : k', ψ (chg q q' h x) = ψ' x := fun x => Subtype.ext (by
    have a := hψ (chg q q' h x)
    have b := hψ' x
    rw [show (ofSplit q).ι (chg q q' h x) = (ofSplit q').ι x from sec_chg q q' h x] at a
    exact a.trans b.symm)
  set a := chg q q' h ((ϖ'⁻¹ : k'ˣ) : k') with ha
  have hint : valuation k ((ϖ : k) * a) ≤ 1 := by
    have e1 : chg q q' h (chg q' q h.symm (ϖ : k)) = (ϖ : k) := by
      change chg q q' h (q'.pr (q.sec _)) = _
      rw [chg_pr, q.pr_sec]
    have h1 := (hu' _).1 (chg_lt q q' h (chg q' q h.symm (ϖ : k)) (by rw [e1]; exact hϖ))
    rw [← e1, ha, ← map_mul, chg_le, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    exact mul_inv_le_one_of_le₀ h1 zero_le'
  set d : k := a - ((ϖ⁻¹ : kˣ) : k) with hd
  have hdϖ : (ϖ : k) * d = (ϖ : k) * a - 1 := by rw [hd, mul_sub, Units.mul_inv]
  have hdint : valuation k ((ϖ : k) * d) ≤ 1 := by
    rw [hdϖ]; exact Valuation.map_sub_le _ hint (by simp)
  have hkill : ∀ y : k, valuation k y ≤ 1 → ψ (d * y) = 1 := fun y hy => by
    obtain ⟨z, hz1⟩ := q.exists_int_approx he (u := y) hy
    have h1 : ψ (d * q.pr (incA D (z : D.host.E))) = 1 := by
      have h2 : ψ (((ϖ⁻¹ : kˣ) : k) * q.pr (incA D (z : D.host.E))) = ψ (a * q.pr (incA D (z : D.host.E))) := by
        rw [ha, ← chg_pr q q' h, ← map_mul, hcomp, chg_pr]
        exact Subtype.ext (hz z)
      rw [hd, sub_mul, AddChar.map_sub_eq_div, h2, div_self']
    have h3 : ψ (d * (y - q.pr (incA D (z : D.host.E)))) = 1 := by
      refine hone _ ?_
      rw [map_mul]
      refine le_trans (mul_le_mul_of_nonneg_left ((hu _).1 hz1) zero_le') ?_
      rw [← map_mul, mul_comm]; exact hdint
    rw [show d * y = d * q.pr (incA D (z : D.host.E)) + d * (y - q.pr (incA D (z : D.host.E))) by ring,
      AddChar.map_add_eq_mul, h1, h3, mul_one]
  have hd1 : valuation k d ≤ 1 := by
    by_cases h0 : d = 0
    · rw [h0]; simp
    have := (hc d).1 fun y hy => by
      rw [show y = d * (y * d⁻¹) by field_simp]
      refine hkill _ ?_
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ hy zero_le'
    simpa using this
  rw [← hdϖ, map_mul]
  exact (mul_le_mul_of_nonneg_left hd1 zero_le').trans_lt (by rwa [mul_one])

theorem exists_theta (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (t : k)
    (ht : valuation k (t - 1) < 1) :
    ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ toEAf D q.e * θ = toEAf D (q.sec t) := by
  have h1 : toEAf D (q.sec (t - 1)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (q.pr_mem_iff (q.sec (t - 1))).1 (by rw [q.pr_sec]; exact ht.le)
    rwa [← map_mul, e_mul_sec] at this
  obtain ⟨s, hs⟩ : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, s.1 = toEAf D (q.sec (t - 1)) := ⟨⟨_, h1⟩, rfl⟩
  refine ⟨(1 + s).1, (1 + s).2, ?_, ?_⟩
  · have h2 : Formalism.L2.DIV.resS D.host.F PP s = 0 :=
      (q.resS_eq_zero_iff he s).2 (by rw [hs, q.prF_toEAf, q.pr_sec]; exact ht)
    rw [Subtype.coe_eta, (Formalism.L2.DIV.resS D.host.F PP).map_add, h2, (Formalism.L2.DIV.resS D.host.F PP).map_one, add_zero]
  · have h1 := q.sec_pr 1
    rw [map_one, mul_one] at h1
    have h2 : q.e * (1 + q.sec (t - 1)) = q.sec t := by
      rw [mul_add, mul_one, e_mul_sec, ← h1, ← map_add (f := _), add_sub_cancel]
    have h3 : (1 + s).1 = toEAf D (1 + q.sec (t - 1)) := by
      rw [Subring.coe_add, OneMemClass.coe_one, hs]
      exact ((congrArg₂ (· + ·) (toEAf D).map_one rfl).symm).trans ((toEAf D).map_add _ _).symm
    exact (congrArg (toEAf D q.e * ·) h3).trans (((toEAf D).map_mul _ _).symm.trans (congrArg (toEAf D) h2))

theorem pow_sub_one_lt {t : k} (ht : valuation k (t - 1) < 1) (n : ℕ) : valuation k (t ^ n - 1) < 1 := by
  have h1 : valuation k t ≤ 1 := by
    rw [show t = (t - 1) + 1 by ring]
    exact Valuation.map_add_le _ ht.le (by simp)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
    refine Valuation.map_add_lt _ ?_ ht
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right h1 zero_le').trans_lt (by rwa [one_mul])

theorem e_mul_of_prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x y : Formalism.IndefR.Datum.EAf D) (s : k) (h : q.prF he x = s * q.prF he y) : toEAf D q.e * x = toEAf D (q.sec s) * y := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj x
  obtain ⟨b, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj y
  rw [q.prF_toEAf, q.prF_toEAf] at h
  rw [← map_mul, ← map_mul, ← q.sec_pr, h, sec_mul_sec, q.sec_pr, ← mul_assoc, mul_comm (q.sec s), e_mul_sec]

end Two

theorem map_inv_mulVec {R k n : Type} [CommRing R] [CommRing k] [Fintype n] [DecidableEq n] (π : R →+* k) (A : GL n R)
    (z col : n → R) (s : k) (h : ∀ r, π (z r) = s * π ((A.val *ᵥ col) r)) (r : n) :
    π (((A⁻¹).val *ᵥ z) r) = s * π (col r) := by
  have e : col = (A⁻¹).val *ᵥ (A.val *ᵥ col) := by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  conv_rhs => rw [e]
  generalize A.val *ᵥ col = w at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def elem {K : Type} [CommRing K] {r : ℕ} (a b : Fin r) (h : a ≠ b) (y : K) : GL (Fin r) K :=
  ⟨transvection a b y, transvection a b (-y), by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem edgeSum_elem {K : Type} [CommRing K] {r κ : ℕ} (a b : Fin r) (h : a ≠ b) (hab : GlobalTheory.chainEdge κ a b) (y : K)
    [DecidableRel (GlobalTheory.chainEdge κ (r := r))] : Formalism.L2.DIV.edgeSum (GlobalTheory.chainEdge κ) (elem a b h y) = y := by
  have key : ∀ i j : Fin r, (if GlobalTheory.chainEdge κ i j then (elem a b h y).val i j else 0) = if i = a ∧ j = b then y else 0 := by
    intro i j
    change (if _ then transvection a b y i j else 0) = _
    by_cases hE : GlobalTheory.chainEdge κ i j
    · have hij : i ≠ j := fun e => by have := hE.1; omega
      rw [if_pos hE, transvection, Matrix.add_apply, one_apply_ne hij, zero_add, single_apply]
      simp only [eq_comm]
    · rw [if_neg hE, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hE hab
  unfold Formalism.L2.DIV.edgeSum
  simp only [key]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem isPat_elem {K : Type} [CommRing K] {r ρ κ : ℕ} (a b : Fin r) (h : a ≠ b) (hab : GlobalTheory.SymRes.FreePos ρ κ a.val b.val)
    (y : K) : GlobalTheory.SymRes.IsPat ρ κ (elem a b h y) := by
  intro i j hij
  change transvection a b y i j = _
  rw [transvection, Matrix.add_apply, single_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hij hab

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem sc_even {c : Comm D} {v : VCom c} (G : GLoc v) (n : ℕ) : G.sc (2 * n) = G.sc 0 * (ofSplit G.q).xi ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, G.sc_step, ih, pow_succ, mul_assoc]

theorem sc_mul_mu {c : Comm D} {v : VCom c} (G : GLoc v) (μ lam : D.host.E) (hμ : μ * lam = -D.host.xi0 ^ (D.R.m / 2))
    (ζ₀ : Fin c.Lz.rank → D.host.E) (hτ : ∀ j h, v.τ j h *ᵥ ζ₀ = lam • (c.bes j 0 h).ζ)
    (hz : G.z₀ = fun r => (ofSplit G.q).pr (ζ₀ r)) : G.sc 0 * (ofSplit G.q).pr μ = 1 := by
  have hs := G.hs
  have hodd := G.S.odd
  have h : G.s + 2 * 0 + 2 = D.R.m := by omega
  let π : D.host.E →+* G.k := G.q.pr.comp (incA D)
  have hπ : (ofSplit G.q).pr = π := rfl
  have h1 := G.tau h
  rw [hz, hπ] at h1
  have h2 : ∀ i, π lam * π ((c.bes G.s 0 h).ζ i) = -((ofSplit G.q).xi * G.sc G.s) * π ((c.bes G.s 0 h).ζ i) := fun i => by
    have a := congrFun h1 i
    have b := π.map_mulVec (v.τ G.s h) ζ₀ i
    rw [hτ] at b
    exact ((map_mul π _ _).symm.trans b).trans a
  have h3 : ∃ i, (c.bes G.s 0 h).ζ i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have a := G.hz_unit G.s 0 h
    have b : (c.B G.s 0 h).ζ = 0 := funext hn
    rw [Place.hz, b, hπ] at a
    simp at a
  obtain ⟨i, hi⟩ := h3
  have h4 := mul_right_cancel₀ ((map_ne_zero π).2 hi) (h2 i)
  have hxi : (ofSplit G.q).xi = π D.host.xi0 := rfl
  have hne : π D.host.xi0 ≠ 0 := (map_ne_zero π).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have h5 := congrArg π hμ
  have h6 : G.sc G.s = G.sc 0 * π D.host.xi0 ^ G.S.ρ := by
    have := sc_even G G.S.ρ
    rwa [show 2 * G.S.ρ = G.s by omega] at this
  rw [map_mul, h4, map_neg, map_pow, hxi, h6, show D.R.m / 2 = G.S.ρ + 1 by omega] at h5
  rw [hπ]
  refine mul_right_cancel₀ (pow_ne_zero (G.S.ρ + 1) hne) ?_
  linear_combination (-1 : G.k) * h5


end GlobalTheory.MiTop.MoveZ


end
