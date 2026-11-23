module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
section
noncomputable section

open Matrix GlobalTheory.HolDict ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open scoped ContDiff

namespace GlobalTheory.HolDict.GS

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem contDiffOn_det {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) : ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf _ _

theorem contDiffOn_minv {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, (f x).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((contDiffOn_det f hf).inv hd).mul (contDiffOn_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem contDiffOn_mmul {m : Type} [Fintype m] (f g : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

theorem contDiffOn_Lm {n : ℕ} (f : E → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, ∀ k, lminor (f x) k ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => Lm (f x) i j) s := by
  simp only [Lm, Matrix.of_apply]
  split_ifs with h1 h2
  · refine ContDiffOn.neg ?_
    simp only [wv, vecMul, dotProduct]
    refine ContDiffOn.sum fun k _ => (hf _ _).mul ?_
    exact contDiffOn_minv (fun x => lb (f x) i) (fun a b => hf _ _) (fun x hx => hd x hx (Fin.castSucc i)) _ _
  · exact contDiffOn_const
  · exact contDiffOn_const

end Smooth

variable {n : ℕ}

theorem Lm_conj_diag (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) :
    Lm A * A * (Lm A)ᴴ = diagonal fun a => (Lm A * A) a a := by
  have hU : (Lm A * A).BlockTriangular id := fun a c h => Lm_mul_up A hM a c h
  have hL : ((Lm A)ᴴ).BlockTriangular id := fun a c h => by
    rw [conjTranspose_apply, Lm_up A c a h, star_zero]
  have hD := hU.mul hL
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  ext a c
  rcases lt_trichotomy a c with h | h | h
  · rw [diagonal_apply_ne _ h.ne, ← hH, conjTranspose_apply, hD (show id a < id c from h), star_zero]
  · subst h
    rw [diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [conjTranspose_apply, Lm_diag, star_one, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hU (show id b < id a from h), zero_mul]
      · rw [hL (show id a < id b from h), mul_zero]
    · simp
  · rw [diagonal_apply_ne _ h.ne', hD (show id c < id a from h)]

theorem lminor_succ (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    lminor A a.succ = lminor A a.castSucc * (Lm A * A) a a := by
  have key : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (Lm A * A) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have hN : ((Lm A)ᵀ).BlockTriangular id := fun a c h => Lm_up A c a h
    have h1 := FrameDegreeData.lminor_conj (A := A) hN i
    have h2 : (Lm A)ᵀᵀ * A * ((Lm A)ᵀ).map (starRingEnd ℂ) = Lm A * A * (Lm A)ᴴ := rfl
    rw [h2, Lm_conj_diag A hA hM] at h1
    simp only [transpose_apply, Lm_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
    rw [← h1, lminor, FrameDegreeData.det_sub_upper _ (blockTriangular_diagonal _)]
    simp only [diagonal_apply_eq]
  rw [key, key]
  exact Fin.prod_univ_castSucc (n := a) _

theorem diag_real (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    (((Lm A * A) a a).re : ℂ) = (Lm A * A) a a := by
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  rw [Lm_conj_diag A hA hM] at hH
  have := congrFun (congrFun hH a) a
  rw [conjTranspose_apply, diagonal_apply_eq] at this
  exact Complex.conj_eq_iff_re.mp this

theorem minor_ne {q : ℕ} {A : Mt n} (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) (k : Fin (n + 1)) :
    lminor A k ≠ 0 := fun h0 => by
  have := h k
  rw [h0] at this
  simp at this

theorem diag_pos {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re)
    (a : Fin n) : 0 < sgn q a * ((Lm A * A) a a).re := by
  have h1 := h a.succ
  have h2 := h a.castSucc
  rw [lminor_succ A hA (minor_ne h) a, ← diag_real A hA (minor_ne h) a, Complex.re_mul_ofReal] at h1
  simp only [Fin.val_succ, psgn, Finset.prod_range_succ, Fin.val_castSucc] at h1 h2
  have e : (∏ x ∈ Finset.range a, sgn q x) * sgn q a * ((lminor A a.castSucc).re * ((Lm A * A) a a).re) =
      ((∏ x ∈ Finset.range a, sgn q x) * (lminor A a.castSucc).re) * (sgn q a * ((Lm A * A) a a).re) := by ring
  rw [e] at h1
  exact (pos_iff_pos_of_mul_pos h1).mp h2

def fac (q : ℕ) (A : Mt n) : Mt n :=
  diagonal (fun a : Fin n => (((Real.sqrt (sgn q a * ((Lm A * A) a a).re))⁻¹ : ℝ) : ℂ)) * (Lm A * A)

theorem fac_spec {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) :
    UpT (fac q A) ∧ ((fac q A)⁻¹)ᴴ * A * (fac q A)⁻¹ = diagonal fun a : Fin n => ((sgn q a : ℝ) : ℂ) := by
  set d : Fin n → ℝ := fun a => ((Lm A * A) a a).re with hd
  set r : Fin n → ℝ := fun a : Fin n => Real.sqrt (sgn q a * d a) with hr
  have hpos : ∀ a : Fin n, 0 < sgn q a * d a := diag_pos A hA h
  have hr0 : ∀ a, r a ≠ 0 := fun a => (Real.sqrt_pos.mpr (hpos a)).ne'
  have hr2 : ∀ a : Fin n, r a * r a = sgn q a * d a := fun a => Real.mul_self_sqrt (hpos a).le
  have hd0 : ∀ a, d a ≠ 0 := fun a h0 => by have := hpos a; rw [h0] at this; simp at this
  have hD : Lm A * A * (Lm A)ᴴ = diagonal fun a => (d a : ℂ) := by
    rw [Lm_conj_diag A hA (minor_ne h)]
    congr 1
    funext a
    exact (diag_real A hA (minor_ne h) a).symm
  have hone : fac q A * ((Lm A)ᴴ * diagonal fun a => ((r a / d a : ℝ) : ℂ)) = 1 := by
    rw [fac, Matrix.mul_assoc, ← Matrix.mul_assoc (Lm A * A), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    have h1 := hr0 a
    have h2 := hd0 a
    change (((r a)⁻¹ : ℝ) : ℂ) * _ = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  refine ⟨⟨(Matrix.isUnit_det_of_right_inverse hone).ne_zero, fun a c hc => ?_⟩, ?_⟩
  · rw [fac, diagonal_mul, Lm_mul_up A (minor_ne h) a c hc, mul_zero]
  · rw [Matrix.inv_eq_right_inv hone, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    have e : ∀ X Y : Mt n, X * Lm A * A * ((Lm A)ᴴ * Y) = X * (Lm A * A * (Lm A)ᴴ) * Y := fun X Y => by
      simp only [Matrix.mul_assoc]
    rw [e, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have h2 := hd0 a
    have h3 := hr2 a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    linear_combination h3

theorem contDiffOn_fac {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (q : ℕ) (f : E → Mt n)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hA : ∀ x ∈ s, (f x)ᴴ = f x)
    (h : ∀ x ∈ s, ∀ i : Fin (n + 1), 0 < psgn q i * (lminor (f x) i).re) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fac q (f x) i j) s := by
  have hU := contDiffOn_mmul (fun x => Lm (f x)) f
    (contDiffOn_Lm f hf fun x hx => minor_ne (h x hx)) hf
  simp only [fac, diagonal_mul]
  refine ContDiffOn.mul ?_ (hU i j)
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn
    (f := fun x => (Real.sqrt (sgn q i * ((Lm (f x) * f x) i i).re))⁻¹) ?_
  refine ContDiffOn.inv (ContDiffOn.sqrt (contDiffOn_const.mul
    (Complex.reCLM.contDiff.comp_contDiffOn (hU i i))) fun x hx => (diag_pos _ (hA x hx) (h x hx) i).ne')
    fun x hx => (Real.sqrt_pos.mpr (diag_pos _ (hA x hx) (h x hx) i)).ne'

theorem smooth_gramSchmidt : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ →
    ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧
      ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧
        Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  intro n Hm q x₀ ⟨_, h0⟩
  have hdet : IsUnit x₀.det := by
    have := congrArg Matrix.det h0
    rw [det_mul, det_diagonal] at this
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    rw [hz, mul_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) this.symm
    unfold sgn
    split_ifs <;> simp
  have hHm : ∀ X : Mt n, X = x₀ᴴ * Hm * x₀ → (x₀⁻¹)ᴴ * X * x₀⁻¹ = Hm := by
    rintro X rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv _ hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hH : Hmᴴ = Hm := by
    rw [← hHm _ h0.symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    ext a
    simp [sgn]
  have hA : ∀ x : Mt n, (-(xᴴ * Hm * x))ᴴ = -(xᴴ * Hm * x) := fun x => by
    simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  refine ⟨fun x i j => fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)) i j, ?_, fun x hx => ?_⟩
  · refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    refine contDiffOn_fac q (fun x => -((Matrix.of x)ᴴ * Hm * Matrix.of x)) (fun a b => ?_) (fun x _ => hA _)
      (fun x (hx : Matrix.of x ∈ frDom Hm q) => hx.2) i j
    simp only [Matrix.neg_apply]
    have hx : ∀ a b : Fin n, ContDiff ℝ ∞ fun x : Fin n → Fin n → ℂ => x a b := fun a b => by fun_prop
    refine (contDiffOn_mmul _ _ (contDiffOn_mmul _ (fun _ => Hm) (fun a b => ?_) fun _ _ => contDiffOn_const)
      (fun a b => (hx a b).contDiffOn) a b).neg
    exact (Complex.conjCLE.contDiff.comp (hx b a)).contDiffOn
  · obtain ⟨h1, h2⟩ := fac_spec _ (hA (Matrix.of x)) hx.2
    refine ⟨h1, ?_⟩
    change (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹)ᴴ * Hm *
      (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹) = Hm
    generalize (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ = γ at h2 ⊢
    have h3 : γᴴ * ((Matrix.of x)ᴴ * Hm * Matrix.of x) * γ = x₀ᴴ * Hm * x₀ := by
      rw [h0, ← diagonal_neg, ← h2]
      simp
    refine Eq.trans ?_ (hHm _ h3)
    simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HolDict.GS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernel
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem _root_.GlobalTheory.LogDR.spanForms_eq_bot_of_lt_card : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ)
    (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ), _root_.GlobalTheory.LogDR.IsCoord x → n < a →
    _root_.GlobalTheory.LogDR.spanForms M H a = ⊥ := by
  intro K _ n x M H a hx hlt
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli hsp.ge
  haveI : FiniteDimensional K Ω[K⁄ℤ] := Module.Finite.of_basis b
  have hr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  unfold _root_.GlobalTheory.LogDR.spanForms
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro η ⟨c, -, v, -, rfl⟩
  have hdep : ¬ LinearIndependent K v := fun hv => by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, hr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ _ hdep, smul_zero]
  rfl

end GlobalTheory.LogDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorCommuteLevelFiniteGroup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

end GlobalTheory.HeckeKeepsGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationQuaternionNormOneSplitStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_quaternion_normOne_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_nrm_one | exact GlobalTheory.QSA.strongApprox_nrm_one | (intros; apply GlobalTheory.QSA.strongApprox_nrm_one <;> assumption)
end

