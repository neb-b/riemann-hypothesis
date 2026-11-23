module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.EllipticTermsContributionProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk

theorem mk_out {F : Type} [Field F] (q : PG F) : ((q.out : GL (Fin 2) F) : PG F) = q := Quotient.out_eq' q

theorem elliptic_lower_left_ne_zero (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := by
  intro e
  rw [Matrix.trace_fin_two, det_eq, e] at hh
  nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def disc (h : GL (Fin 2) ℝ) : ℝ := 4 * h.val.det - h.val.trace ^ 2

def fpC (h : GL (Fin 2) ℝ) : ℂ :=
  (((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + Complex.I * ((Real.sqrt (disc h) / (2 * h 1 0) : ℝ) : ℂ)

theorem fpC_im (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : (fpC h).im ≠ 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  simp only [fpC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_ne_zero (Real.sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)

def fp (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P := ⟨fpC h, fpC_im h hh⟩

theorem fp_eq (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) :
    ((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ) = 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 = ((disc h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  have hD : ((disc h : ℝ) : ℂ) = 4 * (((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ))
      - (((h 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ)) ^ 2 := by
    simp only [disc, Matrix.trace_fin_two, det_eq]; push_cast; ring
  have hz : 2 * ((h 1 0 : ℝ) : ℂ) * fpC h = (((h 0 0 : ℝ) : ℂ) - ((h 1 1 : ℝ) : ℂ)) + Complex.I * ((Real.sqrt (disc h) : ℝ) : ℂ) := by
    simp only [fpC]; push_cast; field_simp
  have h4 : (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ)) = 0 := by
    rw [show (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ))
      = (2 * ((h 1 0 : ℝ) : ℂ) * fpC h) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * (2 * ((h 1 0 : ℝ) : ℂ) * fpC h)
        - 4 * ((h 1 0 : ℝ) : ℂ) * ((h 0 1 : ℝ) : ℂ) by ring, hz]
    linear_combination ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs - hD
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hr')
  · exact h5

theorem fix_comm (h g : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • fp h hh = fp h hh := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have e00 := congrArg (fun M : GL (Fin 2) ℝ => M 0 0) hc
  have e10 := congrArg (fun M : GL (Fin 2) ℝ => M 1 0) hc
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have e00' : ((g 0 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 0 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e00
  have e10' : ((g 1 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e10
  have hQ := fp_eq h hh
  apply Subtype.ext
  rw [coe_smul, div_eq_iff (den_ne g (fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * (((g 0 0 : ℝ) : ℂ) * fpC h + ((g 0 1 : ℝ) : ℂ))
    = ((h 1 0 : ℝ) : ℂ) * (fpC h * (((g 1 0 : ℝ) : ℂ) * fpC h + ((g 1 1 : ℝ) : ℂ)))
  linear_combination e00' - fpC h * e10' - ((g 1 0 : ℝ) : ℂ) * hQ

theorem tr_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.trace = D.σ v g.val.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add (f := _)]; rfl

theorem det_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.det = D.σ v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl

end UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk.EllipticTermsContribution in
theorem UpperTheory.Esk.elliptic_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B4 → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.Fcen → UpperTheory.Esk.F3 := by
  intro hB1a _ hB1c hB4 hC1 hE0a hE0c _ hMult hFcen F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  obtain ⟨_, c2, c3, _, c5, c6⟩ := hE0c F I Gf ι D k a hyp
  have htr : γ.out.val.trace ≠ 0 := by
    obtain ⟨i, hi⟩ := c5 γ ω hTe
    exact (c6 γ ω i hi).1
  have hTv : ∀ v, (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := fun v => by
    rw [tr_r, det_r]; exact hT v
  let z0 : D.Xs := fun v => fp (D.r v γ.out) (hTv v)
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  have memS : ∀ g : PG F, g ∈ S → g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    intro g hg
    rw [hS, MulAction.mem_stabilizer_iff] at hg
    exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS : ∀ g : PG F, g ∈ S → g • z0 = z0 := by
    intro g hg
    obtain ⟨h1, -⟩ := memS g hg
    have hc : g.out * γ.out = γ.out * g.out := by
      apply hFcen F γ.out g.out htr
      rw [mk_out, mk_out]; exact h1
    rw [← mk_out g, Dat.mk_smulX]
    funext v
    exact fix_comm _ _ (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hfin := (hC (ω, z0) s hs hsc).1
  have hSfin : (S : Set (PG F)).Finite := hfin.subset fun g hg => ⟨(memS g hg).2, fun v => by
      show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v)
      rw [fixS g hg, hB1c.2.1]⟩
  have hSF : Finite S := hSfin.to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f : I → P → ℂ := fun v w => q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) =
      D.Te a γ.out (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v γ.out • z v) * j1 (k v) (D.r v γ.out) (z v))
    rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod]
    unfold Dat.orb
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, tr_r, det_r]
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
      have e : ∑ _ : S, c = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
      rw [← e]; exact hasSum_fintype _⟩
  have hP : Pres S (volume : Measure D.Xs) := fun g => (hE0a F I Gf D hyp.ax).2.2.1 (g : PG F)
  have hinv : ∀ (g : S) (z : D.Xs), D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    intro g z
    obtain ⟨h1, h2⟩ := memS g g.2
    have := c2 g γ (ω, z)
    have e : (g : PG F) • ((ω, z) : D.Y) = (ω, g • z) := Prod.ext h2 rfl
    rw [h1, e] at this
    exact this
  have hmeas : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (c3 γ).comp measurable_prodMk_left
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) := by
    rw [show (fun z : D.Xs => c • D.kk k a γ (ω, z)) = fun z => c • (D.Te a γ.out (D.rep ω) * ∏ v, f v (z v)) from
      funext fun z => by rw [hu]]
    exact (hint.const_mul _).smul c
  obtain ⟨-, heq⟩ := (hC1 (↥S) D.Xs volume hP (fun _ => c) β hcut hβ).2 _ hmeas hinv hintc
  rw [← heq]
  simp_rw [hu]
  rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, Complex.real_smul]
  simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HolomorphicOnHalfPlaneFinsetSum
section
open MeasureTheory Matrix

namespace UpperTheory.Esk.FormsStableLemmas

open UpperTheory.Esk

theorem extendHalfPlane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) :
    ext1 (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := by
  funext t
  unfold ext1
  split_ifs <;> simp

theorem holomorphic_on_half_plane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  unfold Hol1
  rw [extendHalfPlane_finset_sum]
  exact (DifferentiableOn.sum h).congr fun t _ => by simp [Finset.sum_apply]

theorem holomorphic_on_half_plane_add (f g : P → ℂ) (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.add hg

theorem holomorphic_on_half_plane_const_mul (c : ℂ) (f : P → ℂ) (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have : ext1 (fun t => c * f t) = fun t => c * ext1 f t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.const_mul c

theorem holomorphic_on_half_plane_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1
  rw [this]
  exact differentiableOn_const 0

theorem nrm_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z := by
  unfold nrm
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (abs_nonneg _) _

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

omit [Fintype I] in
theorem op_apply {ι : Type} [Fintype ι] (a : ι → Gf) (f : X I × Gf → ℂ) (p : X I × Gf) :
    Dat.Op a f p = ∑ i, f (p.1, p.2 * a i) := rfl

theorem isForm_zero (k : I → ℕ) : D.IsForm k 0 := by
  refine ⟨fun _ => ⟨continuous_const, fun _ _ => holomorphic_on_half_plane_zero⟩, ?_, ?_, ?_⟩
  · intro γ z x
    simp
  · intro z x h
    simp
  · exact ⟨0, fun z x => by simp⟩

theorem isForm_add (k : I → ℕ) (f g : X I × Gf → ℂ) (hf : D.IsForm k f) (hg : D.IsForm k g) :
    D.IsForm k (f + g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun x => ⟨(hf.hol x).1.add (hg.hol x).1,
      fun z v => holomorphic_on_half_plane_add _ _ ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩
  · intro γ z x
    simp [Pi.add_apply, hf.aut, hg.aut, mul_add]
  · intro z x h
    simp [Pi.add_apply, hf.lev, hg.lev, mul_add]
  · obtain ⟨C₁, h₁⟩ := hf.bdd
    obtain ⟨C₂, h₂⟩ := hg.bdd
    refine ⟨C₁ + C₂, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    calc ‖(f + g) (z, x)‖ * nrm k z ≤ (‖f (z, x)‖ + ‖g (z, x)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖f (z, x)‖ * nrm k z + ‖g (z, x)‖ * nrm k z := add_mul _ _ _
      _ ≤ C₁ + C₂ := add_le_add (h₁ z x) (h₂ z x)

theorem isForm_smul (k : I → ℕ) (c : ℂ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) :
    D.IsForm k (c • f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun x => ⟨continuous_const.mul (hf.hol x).1,
      fun z v => holomorphic_on_half_plane_const_mul c _ ((hf.hol x).2 z v)⟩
  · intro γ z x
    simp [Pi.smul_apply, hf.aut]
    ring
  · intro z x h
    simp [Pi.smul_apply, hf.lev]
    ring
  · obtain ⟨C, h⟩ := hf.bdd
    refine ⟨‖c‖ * C, fun z x => ?_⟩
    have := h z x
    have hc := norm_nonneg c
    calc ‖(c • f) (z, x)‖ * nrm k z = ‖c‖ * (‖f (z, x)‖ * nrm k z) := by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left this hc

def S (k : I → ℕ) : Submodule ℂ (X I × Gf → ℂ) where
  carrier := {f | D.IsForm k f}
  add_mem' {f g} hf hg := isForm_add D k f g hf hg
  zero_mem' := isForm_zero D k
  smul_mem' c f hf := isForm_smul D k c f hf

theorem M_eq (k : I → ℕ) : D.M k = S D k := Submodule.span_eq (S D k)

theorem mem_M (k : I → ℕ) (f : X I × Gf → ℂ) : f ∈ D.M k ↔ D.IsForm k f := by
  rw [M_eq]; rfl

open Classical in
theorem isForm_op (k : I → ℕ) {ι : Type} [Fintype ι] (a : ι → Gf) (ha : D.Good a)
    (f : X I × Gf → ℂ) (hf : D.IsForm k f) : D.IsForm k (Dat.Op a f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨?_, fun z v => ?_⟩
    · simp only [op_apply]
      exact continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1
    · simp only [op_apply]
      exact holomorphic_on_half_plane_finset_sum Finset.univ (fun i t => f (Function.update z v t, x * a i))
        (fun i _ => (hf.hol (x * a i)).2 z v)
  · intro γ z x
    simp only [op_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hf.aut]
  · intro z x h
    simp only [op_apply]
    exact ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h
  · obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Fintype.card ι * C, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    simp only [op_apply]
    calc ‖∑ i, f (z, x * a i)‖ * nrm k z ≤ (∑ i, ‖f (z, x * a i)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) hn
      _ = ∑ i, ‖f (z, x * a i)‖ * nrm k z := Finset.sum_mul _ _ _
      _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC z (x * a i)
      _ = Fintype.card ι * C := by simp

theorem main (k : I → ℕ) : (∀ f, f ∈ D.M k ↔ D.IsForm k f) ∧
    ∀ (ι : Type) [Fintype ι] (a : ι → Gf), D.Good a → ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k := by
  refine ⟨mem_M D k, fun ι _ a ha f hf => ?_⟩
  rw [mem_M] at hf ⊢
  exact isForm_op D k a ha f hf

end UpperTheory.Esk.FormsStableLemmas

theorem UpperTheory.Esk.forms_stable_under_operators_proof : UpperTheory.Esk.FormsStableUnderOperators :=
  fun _ _ _ _ _ _ D _ k => UpperTheory.Esk.FormsStableLemmas.main D k
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSumBoundedProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace UpperTheory.Esk

namespace KernelSumBound

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num) h.le) (by positivity)
  · exact le_rfl

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w := by
  unfold Kap
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

theorem bound (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (C₀ : ℝ)
    (hk : ∀ (γ : PG F) (y : D.Y), ‖D.kk k a γ y‖ ≤ C₀ * Kap k y.2 (γ • y.2 : D.Xs))
    (hsupp : ∀ (γ : PG F) (ω : D.Om), D.Te a γ.out (D.rep ω) ≠ 0 →
      ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H))
    (y : D.Y) (B : ℝ)
    (hB : ∀ ω' : D.Om, ∑' γ : {γ : PG F // γ • y.1 = ω'},
      ENNReal.ofReal (Kap k y.2 (γ.1 • y.2 : D.Xs)) ≤ ENNReal.ofReal B) :
    ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
  classical
  have hpt : ∀ γ : PG F, ‖D.kk k a γ y‖ₑ ≤ ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := by
    intro γ
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have hz : D.kk k a γ y = 0 := by
        simp only [Dat.kk, Dat.kt, h0, zero_mul]
      rw [hz, enorm_zero]
      exact zero_le
    · obtain ⟨i, hi⟩ := hsupp γ y.1 h0
      calc ‖D.kk k a γ y‖ₑ = ENNReal.ofReal ‖D.kk k a γ y‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (C₀ * Kap k y.2 (γ • y.2 : D.Xs)) := ENNReal.ofReal_le_ofReal (hk γ y)
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)) :=
            ENNReal.ofReal_mul' (Kap_nonneg k _ _)
        _ = Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
            (Set.indicator_of_mem
              (show γ ∈ {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)
              (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)))).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a j : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ)
            (fun _ _ => zero_le) (Finset.mem_univ i)
  have hsub : ∀ i : ι, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal B := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    exact hB ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)
  calc ∑' γ : PG F, ‖D.kk k a γ y‖ₑ
      ≤ ∑' γ : PG F, ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑ i, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : ι, ENNReal.ofReal C₀ * ENNReal.ofReal B := Finset.sum_le_sum fun i _ => hsub i
    _ = Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end KernelSumBound

end UpperTheory.Esk

theorem UpperTheory.Esk.kernel_sum_bounded_proof : UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.E2 := by
  intro h0c h0d hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨-, -, -, ⟨C₀, hC₀⟩, hsupp, -⟩ := h0c F I Gf ι D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, -⟩ := h0d F I Gf D hyp.ax
  have key : ∀ T : ℝ, ∀ y ∈ D.abelian₂ T, ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≤
      Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal (max C 0 * (1 + T))) := by
    intro T y hy
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hpos : 0 < D.HtY s y := lt_of_lt_of_le hc₀ hcs
    have hle : D.HtY s y ≤ T := hy s hs
    refine UpperTheory.Esk.KernelSumBound.bound D k a C₀ hC₀ hsupp y (max C 0 * (1 + T)) fun ω' => ?_
    refine (hC y s hs hcs ω' y.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left C 0) (by linarith) (by linarith) (le_max_right C 0)
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal), fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := hT y
    have hfin : ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) (key T₀ y (hT₀ T₀ le_rfl))
    exact (ENNReal.summable_toReal hfin).congr fun γ => toReal_enorm _
  · refine (key T y hy).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
    all_goals rfl
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.OrbitCoverProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.OrbitCoverLemmas

variable {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]


omit [Countable G] [MeasurableSpace Y] in
theorem orbit_tsum_smul (u : Y → ℝ) (g : G) (y : Y) :
    ∑' h : G, u (h • g • y) = ∑' h : G, u (h • y) := by
  simp only [smul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => u (h • y))

theorem exists_cut (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y))
    (hs : ∀ y, Summable fun g : G => u (g • y)) : ∃ b : Y → ℝ, IsCut G b := by
  have hsE : (fun y => ∑' g : G, u (g • y)) =
      fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal := by
    funext y
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]
    exact tsum_nonneg fun g => h0 _
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [hsE]
    exact (Measurable.tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos : ∀ y, 0 < ∑' g : G, u (g • y) := by
    intro y
    obtain ⟨g, hg⟩ := hpos y
    exact lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y),
    ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩
  have : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) =
      fun g => u (g • y) / ∑' h : G, u (h • y) := by
    funext g; rw [orbit_tsum_smul]
  show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1
  rw [this, ← div_self (hspos y).ne']
  exact (hs y).hasSum.div_const _

theorem cover (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) :
    ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S :=
  _root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc

end UpperTheory.Esk.OrbitCoverLemmas

theorem UpperTheory.Esk.orbit_cover_proof : UpperTheory.Esk.C2 := by
  intro G Y _ _ _ _
  exact ⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs,
    fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩
end
end

