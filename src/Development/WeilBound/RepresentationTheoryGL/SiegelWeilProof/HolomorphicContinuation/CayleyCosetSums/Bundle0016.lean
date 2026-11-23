module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CRSecB
section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reL : Mn n →L[ℝ] Mn n := (1 / 2 : ℂ) • (ContinuousLinearMap.id ℝ (Mn n) + cT)

def imL : Mn n →L[ℝ] Mn n := (-(Complex.I / 2)) • (ContinuousLinearMap.id ℝ (Mn n) - cT)

theorem reL_apply (V : Mn n) : reL V = reP V := rfl

theorem imL_apply (V : Mn n) : imL V = imaginary V := rfl

theorem contDiff_fM (a0 : Mn n) : ContDiff ℝ ⊤ (fM a0) := by
  have h1 : ContDiff ℝ ⊤ (fun V : Mn n => (1 : Mn n) + imaginary V) := contDiff_const.add imL.contDiff
  unfold fM
  refine reL.contDiff.add (ContDiff.const_smul _ ?_)
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const h1) h1) contDiff_const

theorem fM_line (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) (t : ℝ) :
    fM a0 (V0 + t • dV) = (V0 + Complex.I • (a0 * a0ᴴ)) +
      t • (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) +
      (t ^ 2) • (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ)) := by
  have hr : reP (V0 + t • dV) = V0 + t • reP dV := by
    rw [← reL_apply, map_add (f := _), map_smul, reL_apply, reL_apply, reP_of_herm h0]
  have hi : imaginary (V0 + t • dV) = t • imaginary dV := by
    rw [← imL_apply, map_add (f := _), map_smul, imL_apply, imL_apply, imaginaryPart_of_isHermitian h0, zero_add]
  unfold fM
  rw [hr, hi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul]
  module

theorem fderiv_fM (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) :
    fderiv ℝ (fM a0) V0 dV = reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ) := by
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  have hl := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const dV).const_add V0
  rw [one_smul] at hl
  have hd' : HasFDerivAt (fM a0) (fderiv ℝ (fM a0) V0) (V0 + (0 : ℝ) • dV) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt (0 : ℝ) hl
  have h1 := (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ))
  have h2 := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).pow 2).smul_const
    (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ))
  have h3 := ((hasDerivAt_const (0 : ℝ) (V0 + Complex.I • (a0 * a0ᴴ))).add h1).add h2
  simp only [one_smul, zero_add] at h3
  have h4 : HasDerivAt (fun t : ℝ => fM a0 (V0 + t • dV)) (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) 0 := by
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [fM_line a0 V0 dV h0 t, Pi.add_apply, Pi.pow_apply]
    · norm_num
  exact hc.unique h4

theorem herm_zero_of (H1 H2 : Mn n) (h1 : H1ᴴ = H1) (h2 : H2ᴴ = H2) (h : H1 + Complex.I • H2 = 0) :
    H1 = 0 ∧ H2 = 0 := by
  have hc : H1 - Complex.I • H2 = 0 := by
    have := congrArg conjTranspose h
    rw [conjTranspose_add, conjTranspose_smul, h1, h2, conjTranspose_zero] at this
    rw [sub_eq_add_neg, ← neg_smul]
    simpa using this
  have h2H1 : H1 + H1 = 0 := by
    calc H1 + H1 = (H1 + Complex.I • H2) + (H1 - Complex.I • H2) := by abel
      _ = 0 := by rw [h, hc, add_zero]
  have hH1 : H1 = 0 := by
    have : (2 : ℂ) • H1 = 0 := by rw [two_smul]; exact h2H1
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  refine ⟨hH1, ?_⟩
  rw [hH1, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero

theorem fderiv_fM_inj (a0 V0 : Mn n) (h0 : V0ᴴ = V0) (ha : a0.det ≠ 0) :
    Function.Injective (fderiv ℝ (fM a0) V0) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ (fM a0) V0)).2 fun dV hdV => ?_
  rw [fderiv_fM a0 V0 dV h0] at hdV
  have hH2 : (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)ᴴ = a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul, imaginaryPart_isHermitian,
      Matrix.mul_assoc]
    simp
  obtain ⟨hr, hi⟩ := herm_zero_of _ _ (reP_herm dV) hH2 hdV
  have hu : IsUnit a0.det := isUnit_iff_ne_zero.mpr ha
  have huH : IsUnit a0ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr ha).star
  have hB : (2 : ℂ) • imaginary dV = 0 := by
    have := congrArg (fun M => a0⁻¹ * M * (a0ᴴ)⁻¹) hi
    simp only [Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huH, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hB' : imaginary dV = 0 := (smul_eq_zero.mp hB).resolve_left two_ne_zero
  rw [← reP_add_imP dV, hr, hB', smul_zero, add_zero]

end PositivityTheory.Rg.Sw.HSt.CRSec
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CosetSumApply
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

def trm (Ht : G → ℝ≥0) (f : G → ℂ) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x

theorem lift_mR (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  unfold lift
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem resG_mR (F : G → ℂ) (g : G) (y : GR n) : resG ι F g (mR y) = F (g * ι y) := lift_mR _ _

theorem termSplit (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (z : ℂ) (x : G) :
    ∃ (y₀ : GR n) (C : ℂ), ∀ y : GR n, trm Ht f s₀ z (x * ι y) = C * fz m e (z - s₀) (mR (y₀ * y)) := by
  obtain ⟨x₀, y₀, S, r, hr, hx, hh⟩ := h.split x
  refine ⟨y₀, ((r : ℝ) : ℂ) ^ (z - s₀) * S, fun y => ?_⟩
  have hxy : x * ι y = x₀ * ι (y₀ * y) := by rw [hx, mul_assoc, ← map_mul]
  unfold trm
  rw [hxy, (hh _).1, (hh _).2, hS n m e (z - s₀) (y₀ * y), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (Vac.hLoc_nonneg _)]
  ring

theorem fz_mul_k (hS : SecFz) (w : ℂ) (y k : GR n) (hk : k ∈ KR n) :
    fz m e w (mR (y * k)) = fz m e w (mR y) * F0 m 0 e k := by
  obtain ⟨h1, h2⟩ := (mult n m 0 e).1 y k hk
  rw [hS n m e w (y * k), hS n m e w y, h1, h2]
  ring

theorem cosetSum_apply (Φ : G → ℂ) (x : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Φ x = ∑' q : GlobalTheory.Eis.Cosets Pp Γ, Φ (((q.out : Γ) : G) * x) := rfl

theorem klaw (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) :
    ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k := by
  intro z hz g y k hk
  have hfar : ∀ z' : ℂ, t < z'.re → Ê z' (g * ι (y * k)) = Ê z' (g * ι y) * F0 m 0 e k := by
    intro z' hz'
    rw [(h.far z' hz').2, (h.far z' hz').2, cosetSum_apply, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    obtain ⟨y₀, C, hC⟩ := termSplit hS h z' (((q.out : Γ) : G) * g)
    have e1 : ((q.out : Γ) : G) * (g * ι (y * k)) = ((q.out : Γ) : G) * g * ι (y * k) := by rw [mul_assoc]
    have e2 : ((q.out : Γ) : G) * (g * ι y) = ((q.out : Γ) : G) * g * ι y := by rw [mul_assoc]
    change trm Ht f s₀ z' _ = trm Ht f s₀ z' _ * _
    rw [e1, e2, hC, hC, ← mul_assoc y₀ y k, fz_mul_k hS _ _ _ hk]
    ring
  obtain ⟨σ, hσ⟩ := h.hR.1
  have hpre : IsPreconnected U := rightConn U h.hU h.hR
  have hA1 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι (y * k))) U := (h.hol _).analyticOnNhd h.hU
  have hA2 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι y) * F0 m 0 e k) U :=
    ((h.hol _).mul_const _).analyticOnNhd h.hU
  set z₀ : ℂ := ((max σ t + 1 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ U := hσ (by simp [z₀, GlobalTheory.Cont.rightOf]; linarith [le_max_left σ t])
  have hev : (fun z => Ê z (g * ι (y * k))) =ᶠ[𝓝 z₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
    have ho : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : z₀ ∈ {z : ℂ | t < z.re} := by simp [z₀]; linarith [le_max_right σ t]
    filter_upwards [ho.mem_nhds hm] with z hz using hfar z hz
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hpre hz₀ hev hz

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarLoc
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous JJ_conjTranspose)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := PositivityTheory.Rg.Sw.LVs.HolB.JJ_sq

theorem JJ_inv : (JJ n)⁻¹ = -JJ n :=
  Matrix.inv_eq_right_inv (by rw [mul_neg, JJ_mul_self, neg_neg])

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp only [sig, JJ_inv, neg_mul, neg_neg]

def IsLie (X : M2 n) : Prop := Xᴴ = JJ n * X * JJ n

theorem isLie_first_direction (Z : M2 n) : IsLie (dir1 Z) := by
  unfold IsLie dir1
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2, add_comm]

theorem isLie_second_direction (Z : M2 n) : IsLie (dir2 Z) := by
  unfold IsLie dir2
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [h2, neg_smul, ← smul_neg, neg_sub]

theorem lie_dir (Z : M2 n) (b : Bool) : IsLie (if b then dir1 Z else dir2 Z) := by
  cases b
  · exact isLie_second_direction Z
  · exact isLie_first_direction Z

def Ju (n : ℕ) : (M2 n)ˣ where
  val := JJ n
  inv := -JJ n
  val_inv := by rw [mul_neg, JJ_mul_self, neg_neg]
  inv_val := by rw [neg_mul, JJ_mul_self, neg_neg]

theorem cE_conjTranspose {X : M2 n} (hX : IsLie X) (s : ℝ) : (cE X s)ᴴ = JJ n * cE X (-s) * -JJ n := by
  unfold cE
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hX]
  have h : s • (JJ n * X * JJ n) = (Ju n : M2 n) * ((-s) • X) * ((Ju n)⁻¹ : (M2 n)ˣ) := by
    simp only [Ju, Units.inv_mk, Units.val_mk, Matrix.mul_neg, Matrix.mul_smul, neg_smul]
    rw [Matrix.neg_mul, neg_neg, Matrix.smul_mul]
  rw [h, Matrix.exp_units_conj]
  rfl

theorem inG_cE {X : M2 n} (hX : IsLie X) (s : ℝ) : InG (cE X s) := by
  unfold InG
  rw [cE_conjTranspose hX]
  calc JJ n * cE X (-s) * -JJ n * JJ n * cE X s = JJ n * (cE X (-s) * cE X s) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, JJ_mul_self, neg_neg, Matrix.one_mul, Matrix.mul_neg]
    _ = JJ n := by rw [← cE_add, neg_add_cancel, cE_zero, Matrix.mul_one]

theorem cE_eq_exp (X : M2 n) (s : ℝ) : NormedSpace.exp ((s : ℂ) • X) = cE X s := by
  unfold cE; rw [Complex.coe_smul]

def gam {X : M2 n} (hX : IsLie X) (t : ℝ) : GR n :=
  ⟨⟨cE X t, cE X (-t), by rw [← cE_add, add_neg_cancel, cE_zero], by rw [← cE_add, neg_add_cancel, cE_zero]⟩,
    inG_cE hX t⟩

theorem curveGR' {X : M2 n} (hX : IsLie X) : Continuous (gam hX) ∧ gam hX 0 = 1 ∧
    (∀ s t, gam hX (s + t) = gam hX s * gam hX t) ∧ ∀ t, mR (gam hX t) = cE X t := by
  refine ⟨?_, ?_, ?_, fun t => rfl⟩
  · refine Continuous.subtype_mk ?_ _
    rw [Units.continuous_iff]
    exact ⟨cE_continuous X, (cE_continuous X).comp continuous_neg⟩
  · apply Subtype.ext; apply Units.ext; exact cE_zero X
  · intro s t; apply Subtype.ext; apply Units.ext; exact cE_add X s t

end PositivityTheory.Rg.Sw.HSt.FL

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt.FL

theorem curveGR : CurveGR := by
  intro n Z b
  obtain ⟨h1, h2, h3, h4⟩ := curveGR' (lie_dir Z b)
  exact ⟨gam (lie_dir Z b), h1, h2, h3, fun t => by rw [h4, cE_eq_exp]⟩

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicScalarSection
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def holomorphicScalarSection (m : ℕ) (e : ℤ) (x : M2 n) : ℂ := x.det ^ e * (u1 x).det ^ (-(m : ℤ))

def WM (x : M2 n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) - zOfE x * u2 x

def CauchyRiemannFacts : Prop :=
  (∀ (n m : ℕ) (e : ℤ) (y : GR n), F0 m 0 e y = holomorphicScalarSection m e (mR y)) ∧
  ∀ (n : ℕ) (x : M2 n), x.det ≠ 0 → (u1 x).det ≠ 0 →
    DifferentiableAt ℂ zOfE x ∧ (∀ (m : ℕ) (e : ℤ), DifferentiableAt ℂ (holomorphicScalarSection m e) x) ∧
    (∀ Q, fderiv ℂ zOfE x (x * lowQ Q) = 0 ∧ ∀ (m : ℕ) (e : ℤ), fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0) ∧
    (∀ R, fderiv ℂ zOfE x (x * sig (lowQ R)) = WM x * Rᴴ * (u1 x)⁻¹) ∧
    (InG x → (WM x).det ≠ 0)

end PositivityTheory.Rg.Sw.HSt.CR
end
end

