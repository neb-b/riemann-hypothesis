module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsBasisLieOfOrthogonal
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis


open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in
    intro n G hG
    obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
    let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := HCSS.lieOf G
        add_mem' := fun {X Y} hX hY => hadd X Y hX hY
        zero_mem' := fun t => by simpa using hG.one_mem
        smul_mem' := fun r X hX => hsmul r X hX }
    let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
    have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
      FiniteDimensional.complexToReal _
    obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
    have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
    have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
      intro i
      obtain ⟨X, hX, hXe⟩ := heW i
      have : vecOf.symm (e i) = X := by
        rw [← hXe]; simp
      rw [this]; exact hX
    have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
      intro X hX
      have h := hexp _ (hmemW X hX)
      have h2 := congrArg (vecOf (n := n)).symm h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa using h2
    refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
    · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
        (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
    · intro X hX
      exact ⟨_, hexpM X hX⟩
    · intro k hk
      have hkG : k ∈ G := hk.1
      have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
      let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
      have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
      have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
        have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
        simpa [f] using this)
      refine ⟨_, hO, fun i => ?_⟩
      have h := hexp _ (hfW i)
      have h2 := congrArg (vecOf (n := n)).symm h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa [f] using h2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.HCForm

theorem skew_of_diag {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : Module.End ℂ E) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ x, |(⟪T x, x⟫_ℂ + ⟪x, T x⟫_ℂ).re| ≤ A * ‖x‖ ^ 2) (u v : E) :
    |(⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
  set R : E → E → ℝ := fun u v => (⟪T u, v⟫_ℂ + ⟪u, T v⟫_ℂ).re with hR
  have hsym : ∀ u v, R v u = R u v := by
    intro u v
    simp only [hR, Complex.add_re]
    rw [← inner_conj_symm (T v) u, ← inner_conj_symm v (T u)]
    simp only [Complex.conj_re]
    ring
  have hpol : ∀ u v, 4 * R u v = R (u + v) (u + v) - R (u - v) (u - v) := by
    intro u v
    have := hsym u v
    simp only [hR, map_add (f := _), map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re] at this ⊢
    linarith
  have hhalf : ∀ u v, |R u v| ≤ A * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have h1 := abs_le.mp (h (u + v))
    have h2 := abs_le.mp (h (u - v))
    have hp := parallelogram_law_with_norm ℂ u v
    have e := hpol u v
    have hp' : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by nlinarith
    have hb : A * ‖u + v‖ ^ 2 + A * ‖u - v‖ ^ 2 = 2 * A * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      rw [← mul_add, hp']; ring
    change |R u v| ≤ _
    have g1 : R (u + v) (u + v) ≤ A * ‖u + v‖ ^ 2 := h1.2
    have g2 : -(A * ‖u + v‖ ^ 2) ≤ R (u + v) (u + v) := h1.1
    have g3 : R (u - v) (u - v) ≤ A * ‖u - v‖ ^ 2 := h2.2
    have g4 : -(A * ‖u - v‖ ^ 2) ≤ R (u - v) (u - v) := h2.1
    rw [abs_le]
    constructor <;> nlinarith
  change |R u v| ≤ _
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hR]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [hR]
  have hs : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hscale : R (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v) = ‖v‖ * ‖u‖ * R u v := by
    simp only [hR, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hb := hhalf (((‖v‖ : ℝ) : ℂ) • u) (((‖u‖ : ℝ) : ℂ) • v)
  rw [hscale, norm_smul, norm_smul, abs_mul, abs_of_pos (mul_pos ht hs)] at hb
  simp only [Complex.norm_real, norm_norm] at hb
  have hst : 0 < ‖v‖ * ‖u‖ := mul_pos ht hs
  have : ‖v‖ * ‖u‖ * |R u v| ≤ ‖v‖ * ‖u‖ * (A * ‖u‖ * ‖v‖) := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hst

theorem nelson_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {d : ℕ}
    (X : Fin d → Module.End ℂ E) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A)
    (hs : ∀ i x, |2 * (⟪X i x, x⟫_ℂ).re| ≤ A * (⟪x, x⟫_ℂ).re)
    (V : Submodule ℂ E) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (⟪(l.map X).prod u, (l.map X).prod u⟫_ℂ).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (⟪u, u⟫_ℂ).re := by
  have hsq : ∀ x : E, Real.sqrt (⟪x, x⟫_ℂ).re = ‖x‖ := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
    exact Real.sqrt_sq (norm_nonneg x)
  have hskew : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ A * ‖u‖ * ‖v‖ := by
    intro i
    refine skew_of_diag (X i) A hA ?_
    intro x
    have e : (⟪X i x, x⟫_ℂ + ⟪x, X i x⟫_ℂ).re = 2 * (⟪X i x, x⟫_ℂ).re := by
      rw [Complex.add_re, ← inner_conj_symm x (X i x), Complex.conj_re]
      ring
    have n : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [e, ← n]
    exact hs i x
  obtain ⟨C, hC, hb⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth X c hc A hA hskew V hV
  refine ⟨C, hC, fun l u hu => ?_⟩
  rw [hsq, hsq]
  exact hb l u hu

theorem nelson_form : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ)
    (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y)
    (hconj : ∀ x y, Q y x = star (Q x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M)
    (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l)
    (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V),
    ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V,
      Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤
        C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  intro M _ _ Q hadd hsmul hconj hpos d X c hc A hA hs V _ hV
  have hzero : ∀ x, Q x 0 = 0 := by
    intro x
    have := hsmul 0 x 0
    simpa using this
  have hzero' : Q 0 0 = 0 := hzero 0
  let core : InnerProductSpace.Core ℂ M :=
    { inner := Q
      conj_inner_symm := fun x y => by
        change star (Q y x) = Q x y
        rw [hconj x y, star_star]
      re_inner_nonneg := fun x => by
        change 0 ≤ (Q x x).re
        rcases eq_or_ne x 0 with rfl | hx
        · simp [hzero']
        · exact (hpos x hx).le
      add_left := fun x y z => by
        change Q (x + y) z = Q x z + Q y z
        rw [hconj z (x + y), hadd, star_add, ← hconj, ← hconj]
      smul_left := fun x y r => by
        change Q (r • x) y = star r * Q x y
        rw [hconj y (r • x), hsmul, star_mul', ← hconj]
      definite := fun x hx => by
        by_contra hne
        have h0 : Q x x = 0 := hx
        have := hpos x hne
        simp [h0] at this }
  letI : NormedAddCommGroup M := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ M := InnerProductSpace.ofCore core.toCore
  exact nelson_inner X c hc A hA hs V hV

end GlobalTheory.CompanionTheory.HCForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem deriv_nonneg_of_nonneg_right {e : ℝ → ℝ} {e' : ℝ} (h : HasDerivAt e e' 0) (h0 : e 0 = 0)
    (hpos : ∀ t, 0 < t → 0 ≤ e t) : 0 ≤ e' := by
  refine ge_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t ht)

theorem isBoundedBilinearMap_re_form {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : H → H → ℂ) (Mb : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y))
    (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) :
    IsBoundedBilinearMap ℝ (fun p : H × H => (Q p.1 p.2).re) := by
  have hsmulR : ∀ (c : ℝ) (x y : H), Q x (c • y) = (c : ℂ) * Q x y := fun c x y => by
    rw [← hsmul, Complex.coe_smul]
  have haddL : ∀ x₁ x₂ y, Q (x₁ + x₂) y = Q x₁ y + Q x₂ y := fun x₁ x₂ y => by
    rw [hconj, hadd, star_add, ← hconj, ← hconj]
  have hsmulL : ∀ (c : ℝ) (x y : H), Q (c • x) y = (c : ℂ) * Q x y := fun c x y => by
    rw [hconj, hsmulR, star_mul', ← hconj, show star (c : ℂ) = c from Complex.conj_ofReal c]
  refine ⟨fun x₁ x₂ y => ?_, fun c x y => ?_, fun x y₁ y₂ => ?_, fun c x y => ?_, ?_⟩
  · simp only [haddL, Complex.add_re]
  · simp only [hsmulL, Complex.re_ofReal_mul, smul_eq_mul]
  · simp only [hadd, Complex.add_re]
  · simp only [hsmulR, Complex.re_ofReal_mul, smul_eq_mul]
  · refine ⟨max Mb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x y => ?_⟩
    rw [Real.norm_eq_abs]
    calc |(Q x y).re| ≤ ‖Q x y‖ := Complex.abs_re_le_norm _
      _ ≤ Mb * ‖x‖ * ‖y‖ := hbd x y
      _ ≤ max Mb 1 * ‖x‖ * ‖y‖ := by gcongr; exact le_max_left _ _

theorem abs_two_re_form_dRep_le : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  intro n G H _ _ π hG hrep Q Mb a hadd hsmul hconj hbd hgrow X hX x hx
  have hB := isBoundedBilinearMap_re_form Q Mb hadd hsmul hconj hbd
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 :=
    (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hx hX).1
  have hv0 : π (NormedSpace.exp ((0 : ℝ) • X)) x = x := by
    rw [zero_smul, NormedSpace.exp_zero, hrep.1]
    rfl
  set d := dRep π X x with hd
  set f : ℝ → ℝ := fun t => (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re with hf_def
  have hf : HasDerivAt f (2 * (Q d x).re) 0 := by
    have h1 := (hB.hasFDerivAt (π (NormedSpace.exp ((0 : ℝ) • X)) x, π (NormedSpace.exp ((0 : ℝ) • X)) x)).comp_hasDerivAt
      (0 : ℝ) (hv.prodMk hv)
    rw [hB.deriv_apply] at h1
    simp only [hv0] at h1
    have e : (Q x d).re + (Q d x).re = 2 * (Q d x).re := by
      rw [hconj d x, Complex.star_def, Complex.conj_re]
      ring
    rw [e] at h1
    exact h1
  have hf0 : f 0 = (Q x x).re := by
    simp only [hf_def, hv0]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t * mnorm X) * (Q x x).re) (a * mnorm X * (Q x x).re) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t * mnorm X) (a * 1 * mnorm X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul a).mul_const (mnorm X)
    have h3 := (h2.exp).mul_const (Q x x).re
    simpa using h3
  have up : 2 * (Q d x).re ≤ a * mnorm X * (Q x x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hf) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX t x
      rw [abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  have hfn : HasDerivAt (fun t : ℝ => f (-t)) (2 * (Q d x).re * -1) 0 := by
    have hf' : HasDerivAt f (2 * (Q d x).re) (-(0 : ℝ)) := by rwa [neg_zero]
    exact hf'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have low : -(a * mnorm X * (Q x x).re) ≤ 2 * (Q d x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hfn) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX (-t) x
      rw [abs_neg, abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  rw [abs_le]
  exact ⟨low, up⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

