module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorHeightBound
public import ReciprocityTheory.SemistableReduction.Bundle0025

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintChain
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_chain (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) ∧
    (∃ e, e ∈ 𝒜 c d.wF ∧ e ≠ 0 ∧ d.HintIS c sg (fun P => Real.log (d.nrm c d.wF e P))) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.G2 (d.ta2 c) P)) := by
  haveI := hd.graded c
  obtain ⟨Bw, hBw⟩ := d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl
    ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))
  obtain ⟨Be, hBe⟩ := d.hint_bdd sg c
    (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  obtain ⟨Bt, hBt⟩ := d.hint_bdd sg c
    (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨B2, hB2⟩ := d.hint_bdd sg c
    (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  obtain ⟨k, hk⟩ := d.hint_thp_ne hd c
  obtain ⟨Bh, hBh⟩ := d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl
    ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))
  have hwm := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  have hem := hd.et_mem c
  have he0 := hd.et_ne c
  have htm := hd.firstSectionMem c
  have ht0 := hd.firstSectionNeZero c
  have h2m := hd.secondSectionMem c
  have h20 := hd.secondSectionNeZero c
  have hhm := hd.thp_mem k c
  have hn1 : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1r : (d.n1 : ℝ) = d.i * d.g0 := by simp [Data.n1]
  have hn1r1 : (1 : ℝ) ≤ d.n1 := by exact_mod_cast hn1
  have hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc := by
    rw [hn1r]; field_simp
  have hq : 1 ≤ 2 - 2 * d.cc * d.g0 := by linarith [hd.ccg0]
  have IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖) := d.hint_intU hd h c sg

  obtain ⟨ht1m, ht10, ht1l⟩ := d.hint_pow hd htm ht0 d.n1 hn1
  obtain ⟨he2m, he20, he2l⟩ := d.hint_pow hd hem he0 2 two_pos
  obtain ⟨hwpm, hwp0, hwpl⟩ := d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)
  have hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
    simp only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]; abel
  have hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL) := by
    rw [← hW1]; exact SetLike.mul_mem_graded ht1m he2m
  have hf10 := hd.mul_ne_zero c ht1m he2m ht10 he20
  have Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
      (d.w (d.jc c) c ^ (2 * d.n1)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)
  have E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) +
      2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
        (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd ht1m he2m ht10 he20 P
    rw [hW1, ht1l, he2l] at h1
    have h2 := d.hint_log_line hd hwpm hwp0 hf1m hf10 P
    rw [hwpl] at h2
    push_cast at h1 h2
    linarith
  have I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) +
        d.cc * d.tableLineDegreeTwo := by
    intro P; rw [← d.hint_log_be hd c P]; exact hI2be c P

  have Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0)
      (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0))
        (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) /
          (2 - 2 * d.cc * d.g0))) (fun P hP => ?_) _ (d.hint_log_le hd hem he0 hBe)
    have e1 := E1 P
    have lt := d.hint_log_le hd htm ht0 hBt P hP
    have lt2 := mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)
    have ib2 := mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)
    have hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
        d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) := by rw [hκ]
    have hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0 := by linarith
    rw [← sub_nonneg]
    have : ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y +
        -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0) := by
      intro x y z; ring
    rw [this, sub_nonneg, div_le_iff₀ hqp]
    nlinarith

  have Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0)
      (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)))
      (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)
    have := I2 P
    linarith

  have It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0)
      (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _
      (d.hint_log_le hd htm ht0 hBt)
    have e1 := E1 P
    have le := d.hint_log_le hd hem he0 hBe P hP
    have hnp : (0 : ℝ) < d.n1 := by linarith
    have : ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 =
        (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1 := by
      intro x y; field_simp; ring
    rw [this, div_le_iff₀ hnp]
    nlinarith

  obtain ⟨hwqm, hwq0, hwql⟩ := d.hint_pow hd hwm hw0 (d.D + 4) (by omega)
  have hW2 : d.wF + d.G2 = (d.D + 4) • d.wL := by rw [Data.G2]; abel
  have hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL) := by
    rw [← hW2]; exact SetLike.mul_mem_graded hhm h2m
  have hf20 := hd.mul_ne_zero c hhm h2m hk h20
  have Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c)
      (d.w (d.jc c) c ^ (d.D + 4)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)
  have E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ +
        ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd hhm h2m hk h20 P
    rw [hW2] at h1
    have h2 := d.hint_log_line hd hwqm hwq0 hf2m hf20 P
    rw [hwql] at h2
    linarith
  refine ⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _
      (d.hint_log_le hd hhm hk hBh)
    have e2 := E2 P
    have l2 := d.hint_log_le hd h2m h20 hB2 P hP
    linarith
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _
      (d.hint_log_le hd h2m h20 hB2)
    have e2 := E2 P
    have l2 := d.hint_log_le hd hhm hk hBh P hP
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SumLeSqrtCardMul
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem card_support_le {R : Type*} [CommSemiring R] {D N n n' : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) (hu : UDegLE n' Q) :
    Q.support.card ≤
      (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) := by
  classical
  let fx : (UXVar D N →₀ ℕ) → (Fin (D + 2) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i))
  let fu : (UXVar D N →₀ ℕ) → (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ) := fun s =>
    Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))
  have hmaps : ∀ s ∈ Q.support, (fun s => (fx s, fu s)) s ∈
      (Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n') := by
    intro s hs
    simp only [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
    constructor
    · simpa [fx, xDeg] using hx s hs
    · have := hu s hs
      simp only [fu, Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_option, Option.elim]
      unfold uDeg at this ⊢
      omega
  have hinj : Set.InjOn (fun s => (fx s, fu s)) Q.support := by
    intro s _ t _ hst
    simp only [Prod.mk.injEq] at hst
    ext v
    rcases v with p | i
    · have := congrArg (fun f => f (some p)) hst.2
      simpa [fu] using this
    · have := congrArg (fun f => f i) hst.1
      simpa [fx] using this
  calc Q.support.card ≤ ((Finset.univ.finsuppAntidiag n) ×ˢ (Finset.univ.finsuppAntidiag n')).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = _ := by
      rw [Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
        Finset.card_finsuppAntidiag_nat_eq_choose]
      simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_option, Fintype.card_prod]
      congr 1
      · rw [show D + 2 + n - 1 = n + D + 1 by omega]
        exact Nat.choose_symm_of_eq_add (by omega)
      · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega]
        exact Nat.choose_symm_of_eq_add (by omega)

noncomputable def Ey {D N : ℕ} (y : Fin (N + 1) → ℂ) :
    MvPolynomial (UXVar D N) ℂ →ₐ[ℂ] MvPolynomial (Fin (D + 2) × Fin (N + 1)) ℂ :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))

theorem sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (a : α → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  calc ∑ i ∈ s, a i ≤ |∑ i ∈ s, a i| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ s, a i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (s.card * ∑ i ∈ s, a i ^ 2) := Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _

theorem coeff_Ey_le {D N n n' : ℕ} (R : MvPolynomial (UXVar D N) ℂ) (hx : XHom n R)
    (hu : UDegLE n' R) (y : Fin (N + 1) → ℂ) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    ‖AddMonoidAlgebra.coeff (Ey y R) β‖ ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 R *
      Real.sqrt ((n + D + 1).choose (D + 1) *
        (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) * (∑ j, ‖y j‖) ^ n := by
  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality _ (Ey y R)).2 β
  set z := ReciprocityTheory.MultiplicativeHeights.torusPoint θ with hzdef
  have hz : ∀ p, ‖z p‖ = 1 := by
    intro p
    simp only [hzdef, ReciprocityTheory.MultiplicativeHeights.torusPoint]
    rw [Complex.norm_exp]
    simp
  set Y := ∑ j, ‖y j‖ with hY
  set pt : UXVar D N → ℂ := fun v => eval z (Sum.elim X (fun i => ∑ j, X (i, j) * C (y j)) v)
    with hpt
  have hev : eval z (Ey y R) = eval pt R := by
    have := congrArg (fun φ => φ R)
      (MvPolynomial.comp_aeval (R := ℂ) (Sum.elim X fun i => ∑ j, X (i, j) * C (y j))
        (aeval z))
    simp only [AlgHom.comp_apply] at this
    calc eval z (Ey y R) = aeval z (Ey y R) := by simp
      _ = _ := this
      _ = eval pt R := by simp [hpt]
  have hpt1 : ∀ p, ‖pt (Sum.inl p)‖ = 1 := fun p => by simp [hpt, hz]
  have hpt2 : ∀ i, ‖pt (Sum.inr i)‖ ≤ Y := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hpt, Sum.elim_inr, map_sum, map_mul, eval_X, eval_C]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, hz, one_mul]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmono : ∀ α ∈ R.support, ‖∏ v, pt v ^ α v‖ ≤ Y ^ n := by
    intro α hα
    rw [norm_prod, Fintype.prod_sum_type]
    simp only [norm_pow, hpt1, one_pow, Finset.prod_const_one, one_mul]
    calc ∏ i, ‖pt (Sum.inr i)‖ ^ α (Sum.inr i) ≤ ∏ i, Y ^ α (Sum.inr i) :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpt2 i) _
      _ = Y ^ n := by rw [Finset.prod_pow_eq_pow_sum, ← hx α hα]; rfl
  have hcard := card_support_le R hx hu
  calc ‖AddMonoidAlgebra.coeff (Ey y R) β‖ ≤ ‖eval z (Ey y R)‖ := hθ
    _ = ‖∑ α ∈ R.support, AddMonoidAlgebra.coeff R α * ∏ v, pt v ^ α v‖ := by rw [hev, eval_eq']
    _ ≤ ∑ α ∈ R.support, ‖AddMonoidAlgebra.coeff R α‖ * Y ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmono α hα) (norm_nonneg _)
    _ = (∑ α ∈ R.support, ‖AddMonoidAlgebra.coeff R α‖) * Y ^ n := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt R.support.card * ReciprocityTheory.MultiplicativeHeights.polyL2 R) * Y ^ n := by
        gcongr
        exact sum_le_sqrt_card_mul _ _
    _ ≤ _ := by
        rw [mul_comm (Real.sqrt _) (ReciprocityTheory.MultiplicativeHeights.polyL2 R)]
        gcongr
        unfold ReciprocityTheory.MultiplicativeHeights.polyL2; positivity

end ReciprocityTheory.ChartRestriction.G.T0
end

