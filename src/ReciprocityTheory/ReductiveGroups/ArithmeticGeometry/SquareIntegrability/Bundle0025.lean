module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousPointNormSqQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbel
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

private theorem sum_inner_ob_smul_e {ι : Type} [Fintype ι]
    (K : Submodule ℝ (EuclideanSpace ℂ ι)) (a : EuclideanSpace ℂ ι)
    (ha : a ∈ K) : ∑ i, (inner ℝ ((Col.ob K) i) (⟨a, ha⟩ : K)) • (Col.e K i) = a := by
  have h := congrArg (fun w : K => (w : EuclideanSpace ℂ ι)) ((Col.ob K).sum_repr' ⟨a, ha⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem cab_core (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound) (hA : PropAStatement)
    (hS : GSupStatement) (hI : IsSplit P I) (c : ℕ) (hc : c ≤ DF) (σ : E →+* ℂ)
    (ξ : Vsp X.dim) (hξ1 : ‖ξ‖ = 1) (hξI : ∀ a ∈ I, Hf ξ a = 0)
 :
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 := by
  classical
  have hK := Col.hK_of hI
  set η := Col.wmap (IR I) ξ with hη
  have hη1 : ‖η‖ ≤ 1 := by rw [hη, cab_norm_wmap_xi hK hξI, hξ1]
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < P.q := by linarith
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat : ∀ γ ∈ lat (Col.YB hI hP P.q).b, γ ≠ 0 →
      |P.R0| ≤ Real.sqrt (P.q * Real.pi) * ‖γ‖ := by
    intro γ hγ hne
    have hl : γ ∈ Col.GB X I := by rw [← Col.lat_bB hI hP]; exact hγ
    obtain ⟨x, hx, rfl⟩ := Col.mem_GB.1 hl
    have hx' : x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := hx
    have hreal : ∀ a ∈ IR I, (Hf x a).im = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem y hy => exact hx'.2 y hy
      | zero => simp [Hf]
      | add y w _ _ hy hw =>
        have h1 : Hf x (y + w) = Hf x y + Hf x w := by
          simp only [Hf, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_add]
        rw [h1, Complex.add_im, hy, hw, add_zero]
      | smul r y _ hy =>
        have h1 : Hf x (r • y) = (r : ℂ) * Hf x y := by
          simp only [Hf, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Complex.real_smul] <;> ring
        simp [h1, hy]
    have hz : ∀ k, (Col.z (IR I) k x).im = 0 := fun k => hreal _ (Col.ob (IR I) k).2
    have hp1 : Col.p1 (IR I) x ∈ IR I := by
      have hsum : Col.p1 (IR I) x = ∑ k, (Col.z (IR I) k x).re • Col.e (IR I) k := by
        simp only [Col.p1]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hzk : Col.z (IR I) k x = ((Col.z (IR I) k x).re : ℂ) := by
          apply Complex.ext <;> simp [hz k]
        conv_lhs => rw [hzk]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
      rw [hsum]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Col.ob (IR I) k).2
    have hnorm : ‖Col.wmap (IR I) x‖ = ‖x - Col.p1 (IR I) x‖ := by
      first | rw [Col.norm_wmap (Col.hK_of hI)] | rw [Col.norm_wmap]
      rw [Col.p2]
    have hxI : x ∉ I := by
      intro hxI
      apply hne
      have hxK : x ∈ IR I := Submodule.subset_span hxI
      have hp : Col.p1 (IR I) x = x := by
        conv_rhs => rw [← sum_inner_ob_smul_e (IR I) x hxK]
        simp only [Col.p1]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hzk : Col.z (IR I) k x =
            ((inner ℝ ((Col.ob (IR I)) k) (⟨x, hxK⟩ : IR I) : ℝ) : ℂ) := by
          apply Complex.ext
          · simp only [Complex.ofReal_re, Submodule.coe_inner]
            simp [Col.z, Col.e, Hf, real_inner_eq_re_inner, PiLp.inner_apply, mul_comm]
          · simpa using hz k
        rw [hzk, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        all_goals rfl
      have h0 : ‖Col.wmap (IR I) x‖ = 0 := by rw [hnorm, hp, sub_self, norm_zero]
      exact norm_eq_zero.mp h0
    have ht := hI.thick x hx'.1 hx'.2 hxI
    have hth : |P.R0| ≤ Real.sqrt (P.q * Real.pi) * P.th := by
      have hq : (0 : ℝ) < P.q := by
        have := P.hq
        exact_mod_cast (by omega : 0 < P.q)
      have hf1 : (1 : ℝ) ≤ PT.f E := by
        have h2 : 1 ≤ PT.f E := le_trans (Nat.one_le_pow _ _ (by have := P.hm1; omega)) P.hmf
        exact_mod_cast h2
      have hRR : (1 : ℝ) ≤ RR (E := E) := by
        have := P.hrd
        show (1 : ℝ) ≤ PT.rd E ^ 7
        exact one_le_pow₀ (by linarith)
      have hRR3 : (1 : ℝ) ≤ RR (E := E) ^ 3 := one_le_pow₀ hRR
      have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hc : 1 ≤ Real.pi * PT.f E * RR (E := E) ^ 3 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hpi hf1) hRR3
      rw [Par.th, th, ← Real.sqrt_mul (show (0 : ℝ) ≤ P.q * Real.pi by positivity), ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      have heq : (P.q : ℝ) * Real.pi * (PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q) =
          (Real.pi * PT.f E * RR (E := E) ^ 3) * P.R0 ^ 2 := by
        first | (field_simp; ring) | field_simp
      rw [heq]
      exact le_mul_of_one_le_left (sq_nonneg _) hc
    calc |P.R0| ≤ Real.sqrt (P.q * Real.pi) * P.th := hth
      _ ≤ Real.sqrt (P.q * Real.pi) * ‖Col.wmap (IR I) x‖ := by
        gcongr
        calc P.th ≤ Metric.infDist x (IR I) := ht
          _ ≤ dist x (Col.p1 (IR I) x) := Metric.infDist_le_dist_of_mem hp1
          _ = ‖Col.wmap (IR I) x‖ := by rw [dist_eq_norm, hnorm]
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (Col.YB hI hP P.q) P.q c |P.R0| P.hq (Col.YB_coc hI hP P.q) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly η c) (cabPoly_deg η c)
  have hJ := cab_J_le η hη1 c P.q P.hq
  rw [Fintype.card_fin] at hJ
  have hl2' : (Col.YB hI hP P.q).l2 P.q β ≤ 6 * (c.factorial * (2 / (P.q * Real.pi)) ^ c * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  set Bsq : ℝ := 12 * (5.12 : ℝ) ^ (Col.gB (IR I)) * c.factorial * (2 / (P.q * Real.pi)) ^ c with hBsq
  have hsup : ∀ t, (Col.YB hI hP P.q).ptN2 P.q β t ≤ Bsq := by
    intro t
    have := cab_sup hS (Col.YB hI hP P.q) P.q c hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    rwa [Fintype.card_fin] at this
  have hBsq0 : 0 ≤ Bsq := by rw [hBsq]; positivity
  set B := Real.sqrt Bsq with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2 := by
    intro t; rw [hBdef, Real.sq_sqrt hBsq0]; exact hsup t
  have hT2 : ∀ c' v, ‖Col.Tc X I P.q β c' v‖ ≤ B * Real.exp (P.q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(P.q * Real.pi * ‖Col.uc (IR I) v - Col.uc (IR I) (cabOut c' : Vsp X.dim)‖ ^ 2)) := by
    intro c' v
    have := Col.norm_Tc_le hI hB0 hBβ c' v
    rw [Col.uQ_out] at this
    refine this.trans (le_of_eq ?_)
    rw [show cabOut c' = Quotient.out c' from rfl]; ring_nf
  set s' : (Fin 1 → Vsp X.dim) → ℂ := Col.colS X I P.q β with hs'
  have hs'mem : s' ∈ X.Sec P.q 1 := Col.colS_mem hI hP hGT hB0 hBβ hβ
  have hsPd : Differentiable ℂ (Col.sP X I P.q β) := by
    have h1 : Differentiable ℂ s' := hs'mem.1
    let D : Vsp X.dim →L[ℂ] (Fin 1 → Vsp X.dim) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ _
    have : Col.sP X I P.q β = s' ∘ D := by funext v; rfl
    rw [this]; exact h1.comp D.differentiable
  refine ⟨s', hs'mem, ?_, ?_⟩
  · intro xs hxs
    set F0 := Col.F0 I P.q β with hF0
    set R : Vsp X.dim → ℂ := fun v => Col.sP X I P.q β v - F0 v with hR
    have hF0d : Differentiable ℂ F0 := differentiable_zeroModeLift I P.q β hβ.1
    have hRd : Differentiable ℂ R := hsPd.sub hF0d
    have hsplit : Col.sP X I P.q β = F0 + R := by funext v; simp [hR]
    have hd1 : d1 s' c xs = iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs :=
      iteratedFDeriv_single_column (contDiff_of_differentiable_fd hsPd c) xs
    have hmain : iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ :=
      cab_main hK σ hξI β hβ.1 hjet F0 hF0d (fun v hv => zeroModeLift_on_part hI P.q β σ v hv) xs
        (fun k => (hxs k).1)
    have hadd : iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs =
        iteratedFDeriv ℂ c F0 0 xs + iteratedFDeriv ℂ c R 0 xs := by
      rw [hsplit, iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF0d c).contDiffAt
        (contDiff_of_differentiable_fd hRd c).contDiffAt]
      rfl
    rw [hd1, hadd, hmain, add_sub_cancel_left]
    obtain ⟨g', hg', hs, hle⟩ := cab_sum_nz hP hGT hI
    have hbd := cab_R hI hP hGT hβ B hB0 (Col.summable_Tc hI hP hGT hB0 hBβ) hT2
    have htd := cab_tail_deriv R hRd c xs (fun k => (hxs k).2.le) P.q hq0 B hB0 _ hs hbd
    refine htd.trans ?_
    have hstep : B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        ∑' a : cabNZ X I, Real.exp (-(Real.pi / 2 * P.q *
          ‖Col.uc (IR I) (cabOut (a : Col.Qc X I) : Vsp X.dim)‖ ^ 2)) ≤
        B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
          (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0 (E := E) P.q P.R0))) := by
      gcongr
    refine hstep.trans ?_
    have hnum := cab_numeric c (Col.gB (IR I)) X.gA g' (dstar (E := E) P.m) P.q (t0 (E := E) P.q P.R0) hq2 hGle hg'
      (threshold_ge_log_bound P hc) (threshold_ge_rank_log_two P)
    refine hnum.trans (le_of_eq ?_)
    simp only [Par.eps1]
  · have h4 := Col.l2_colS_le_four_mul hI hP hGT hβ hB0 hBβ
    have hJ1 := cab_J_one P (G := Col.gB (IR I)) hc
    have hl2Y : (Col.YB hI hP P.q).l2 P.q β ≤ 6 := by
      have := hl2'; rw [Fintype.card_fin] at this; nlinarith
    have hK6 := twentyfour_le_constant P
    have hf1 : (1 : ℝ) ≤ (c.factorial : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
      nlinarith
    have hK6p : 0 < P.K6 := by linarith
    rw [inv_mul_le_iff₀ hK6p]
    have : P.K6 ≤ P.K6 * (c.factorial : ℝ) ^ 2 := le_mul_of_one_le_right hK6p.le hf1
    have : X.l2 P.q s' ≤ 4 * (Col.YB hI hP P.q).l2 P.q β := h4
    linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EpsilonLeHalf
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

theorem epsilon_le_half {E : Type} [Field E] [NumberField E] {X : PT E} {DF : ℕ} (P : Par X DF) :
    P.eps1 ≤ 1 / 2 := by
  have h6 := P.C6
  have hr0 : (0:ℝ) ≤ X.r := Nat.cast_nonneg _
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg hr0 (Real.log_natCast_nonneg _)
  have hrest : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  have e1 := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have p2 : (2.7:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr; linarith
  have p3 : (2.7:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr; linarith
  have hl43 : Real.log 4.3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), e2]
    norm_num at p2
    linarith
  have hl14 : Real.log 7 + Real.log 2 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num), e3]
    norm_num at p3
    linarith
  have hds : (dstar (E := E) P.m : ℝ) * Real.log 4.3 ≤ 2 * dstar (E := E) P.m := by
    have h := mul_le_mul_of_nonneg_left hl43 (Nat.cast_nonneg (α := ℝ) (dstar (E := E) P.m))
    linarith
  have key : (7:ℝ) * 2 ^ X.gA * (4.3:ℝ) ^ dstar (E := E) P.m =
      Real.exp (Real.log 7 + X.gA * Real.log 2 + dstar (E := E) P.m * Real.log 4.3) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  unfold Par.eps1
  rw [key, ← Real.exp_add]
  have half : (1:ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [half, Real.exp_le_exp]
  linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

