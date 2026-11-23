module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
section
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.OM.SchDiff

section general

variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ n F) :=
  hF.iteratedFDeriv_right (by norm_cast)

theorem fderiv_iter_comm {F : X → V} (hF : ContDiff ℝ ∞ F) (h : X) (n : ℕ) (a : X) :
    fderiv ℝ (iteratedFDeriv ℝ n F) a h = iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a := by
  induction n generalizing a with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF 0).differentiable (by simp) a)]
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    ext m
    have hK := contDiff_iter hF n
    have hK' : ContDiff ℝ ∞ (fderiv ℝ (iteratedFDeriv ℝ n F)) := hK.fderiv_right (by norm_cast)
    have hd := hK'.differentiable (by simp) a
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF (n + 1)).differentiable (by simp) a), iteratedFDeriv_succ_apply_left,
      ← funext ih]
    simp only [iteratedFDeriv_succ_apply_left]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
    have hs := (hK.contDiffAt (x := a)).isSymmSndFDerivAt (by simp)
    simp [hs.eq h (m 0)]

theorem taylor_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) (a h : X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ segment ℝ a (a + h), ‖iteratedFDeriv ℝ (n + 2) F b‖ ≤ M) :
    ‖iteratedFDeriv ℝ n F (a + h) - iteratedFDeriv ℝ n F a
      - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a‖ ≤ M * ‖h‖ * ‖h‖ := by
  have h1 : ∀ b ∈ segment ℝ a (a + h),
      ‖fderiv ℝ (iteratedFDeriv ℝ n F) b - fderiv ℝ (iteratedFDeriv ℝ n F) a‖ ≤ M * ‖h‖ := by
    intro b hb
    have h2 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ (n + 1) F) (C := M)
      (fun x _ => (contDiff_iter hF (n + 1)).differentiable (by simp) x)
      (fun x hx => by rw [norm_fderiv_iteratedFDeriv]; exact hM x hx)
      (left_mem_segment _ _ _) hb
    have h3 : ‖b - a‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment hb
    rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h2.trans (by gcongr)
  have h4 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ n F)
      (fun x _ => (contDiff_iter hF n).differentiable (by simp) x) h1
      (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [add_sub_cancel_left, fderiv_iter_comm hF] at h4
  exact h4

end general

section family

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iter_slice {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p, y)) x =
      (iteratedFDeriv ℝ n F (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have h1 : (fun y => F (p, y)) = (fun q => F ((p, 0) + q)) ∘ ContinuousLinearMap.inr ℝ P E := by
    funext y; simp
  have h2 : ContDiff ℝ ∞ (fun q => F ((p, 0) + q)) := hF.comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by norm_cast; simp),
    iteratedFDeriv_comp_add_left]
  simp

theorem seminorm_remainder {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0)) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (R (z + v) - R z - D v) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hb k (n + 2)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC z (by simp) 0)
  refine ⟨C, fun v hv => SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_⟩
  have hG : ContDiff ℝ ∞ (fun b => fderiv ℝ F b ((v, 0) : P × E)) :=
    (hF.fderiv_right (m := ∞) (by norm_cast)).clm_apply contDiff_const
  have e1 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      iteratedFDeriv ℝ n (R (z + v)) x - iteratedFDeriv ℝ n (R z) x - iteratedFDeriv ℝ n (D v) x := by
    have : ⇑(R (z + v) - R z - D v) = ⇑(R (z + v)) - ⇑(R z) - ⇑(D v) := by
      funext y; simp
    rw [this, iteratedFDeriv_sub_apply (f := ⇑(R (z + v)) - ⇑(R z)) (((R (z + v)).smooth n).sub ((R z).smooth n)).contDiffAt
      ((D v).smooth n).contDiffAt, iteratedFDeriv_sub_apply ((R (z + v)).smooth n).contDiffAt
      ((R z).smooth n).contDiffAt]
  have e2 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      (iteratedFDeriv ℝ n F ((z, x) + (v, 0)) - iteratedFDeriv ℝ n F (z, x)
        - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b ((v, 0) : P × E)) (z, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
    rw [e1, hR, hR, hD, iter_slice hF, iter_slice hF, iter_slice hG]
    ext m
    simp
  rcases eq_or_lt_of_le (show 0 ≤ ‖x‖ ^ k by positivity) with h0 | h0
  · rw [← h0, zero_mul]; positivity
  have h3 := taylor_iter hF n (z, x) (v, 0) (M := C / ‖x‖ ^ k) (by positivity) (by
    rintro b ⟨s, t, hs, ht, hst, rfl⟩
    have : s • (z, x) + t • ((z, x) + (v, (0 : E))) = (z + t • v, x) := by
      obtain rfl : s = 1 - t := by linarith
      ext <;> simp <;> module
    rw [this, le_div_iff₀ h0, mul_comm]
    apply hC
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
    nlinarith [norm_nonneg v])
  have h4 : ‖((v, 0) : P × E)‖ = ‖v‖ := by simp [Prod.norm_def]
  rw [h4] at h3
  have h5 : ‖iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x‖ ≤ C / ‖x‖ ^ k * ‖v‖ * ‖v‖ := by
    rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) h3
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one _ _ _
  calc _ ≤ ‖x‖ ^ k * (C / ‖x‖ ^ k * ‖v‖ * ‖v‖) := by gcongr
    _ = _ := by field_simp

theorem hasFDerivAt_family {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0))
    (T : SchwartzMap E ℂ →L[ℂ] ℂ) (L : P →L[ℝ] ℂ) (hL : ∀ v, L v = T (D v)) :
    HasFDerivAt (fun p => T (R p)) L z := by
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (by
      change Continuous fun f => ‖T f‖
      fun_prop)
  choose B hB using seminorm_remainder hF z hb R D hR hD
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun v : P => ‖v‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * ∑ i ∈ S, |B i.1 i.2|) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : P) one_pos] with v hv
  rw [mem_closedBall_zero_iff] at hv
  have h1 := hC (R (z + v) - R z - D v)
  have h2 : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (R (z + v) - R z - D v) ≤
      (∑ i ∈ S, |B i.1 i.2|) * ‖v‖ ^ 2 := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => (hB i.1 i.2 v hv).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i : ℕ × ℕ => |B i.1 i.2|)
      (fun _ _ => abs_nonneg _) hi)
  rw [hL, ← map_sub, ← map_sub, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine le_trans h1 ?_
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  gcongr

theorem bound_mul_translate {A : P × E → ℂ} (hA : Function.HasTemperateGrowth A) (s : SchwartzMap E ℂ)
    (l : P →L[ℝ] E) (z : P) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : P × E => A q * s (q.2 + l q.1)) (p, x)‖ ≤ C := by
  obtain ⟨N, C₀, hC₀, hN⟩ := hA.norm_iteratedFDeriv_le_uniform n
  set L : P × E →L[ℝ] E := ContinuousLinearMap.snd ℝ P E + l ∘L ContinuousLinearMap.fst ℝ P E with hL
  have hLq : ∀ q : P × E, L q = q.2 + l q.1 := fun q => rfl
  set c : ℝ := 1 + (‖z‖ + 1) + ‖l‖ * (‖z‖ + 1) with hc
  set S : ℝ := 2 ^ (k + N) * ((Finset.Iic (k + N, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) s with hS
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) * S,
    fun p hp x => ?_⟩
  have hp' : ‖p‖ ≤ ‖z‖ + 1 := by
    have := norm_add_le z (p - z)
    rw [add_sub_cancel] at this
    linarith
  have hx : ‖x‖ ≤ ‖x + l p‖ + ‖l‖ * (‖z‖ + 1) := by
    have h1 := norm_sub_le (x + l p) (l p)
    rw [add_sub_cancel_right] at h1
    have h2 : ‖l p‖ ≤ ‖l‖ * (‖z‖ + 1) := (l.le_opNorm p).trans (by gcongr)
    linarith
  have hl0 : 0 ≤ ‖l‖ * (‖z‖ + 1) := by positivity
  have hq : 1 + ‖(p, x)‖ ≤ c * (1 + ‖x + l p‖) := by
    have h1 : ‖(p, x)‖ ≤ ‖p‖ + ‖x‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by simp)
    have h2 : 1 * ‖x + l p‖ ≤ c * ‖x + l p‖ := by
      gcongr
      have := norm_nonneg z
      linarith
    linarith
  have hx' : ‖x‖ ≤ c * (1 + ‖x + l p‖) := by
    have := norm_snd_le (p, x)
    linarith
  have hs : ContDiff ℝ ∞ (⇑s ∘ L) := (s.smooth ⊤).comp L.contDiff
  have h1 := norm_iteratedFDeriv_mul_le hA.1 hs (p, x) (n := n) (by norm_cast; simp)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  have h2 : ‖iteratedFDeriv ℝ (n - i) (⇑s ∘ L) (p, x)‖ ≤
      ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i) := by
    rw [L.iteratedFDeriv_comp_right (s.smooth ⊤) _ (by generalize n - i = j; exact_mod_cast le_top)]
    simpa [hLq] using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ (n - i) s (L (p, x))) (fun _ => L)
  have h3 : (1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, n)) le_rfl (Nat.sub_le _ _) s _
  have h4 := hN i hi' (p, x)
  have hc0 : 0 ≤ c := by positivity
  calc _ ≤ (c * (1 + ‖x + l p‖)) ^ k * ((n.choose i : ℝ) * (C₀ * (c * (1 + ‖x + l p‖)) ^ N) *
        (‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i))) := by
        gcongr
        exact h4.trans (by gcongr)
    _ = (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) *
        ((1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖) := by
        simp only [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

end family

theorem temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

variable {κ : Type} [Fintype κ]

end GlobalTheory.CompanionTheory.OM.SchDiff

namespace GlobalTheory.CompanionTheory.OM

open SchDiff

end GlobalTheory.CompanionTheory.OM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoxFunMemSB
section
noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacDbl

theorem boxFun_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inl) (by fun_prop)).mul
    (h₂.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  have hK : IsCompact ((fun p : (κ → R) × (κ' → R) => Sum.elim p.1 p.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) := by
    refine (IsCompact.prod h₁.2 h₂.2).image (continuous_pi ?_)
    rintro (i | i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra hne
  obtain ⟨e₁, e₂⟩ := mul_ne_zero_iff.1 hne
  refine hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ e₁, subset_tsupport _ e₂⟩, ?_⟩
  funext i
  rcases i with i | i <;> rfl

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end

end GlobalTheory.CompanionTheory.VacDbl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WittOrbit

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem int_mul {l m n : Type} [Fintype m] {X : Matrix l m E} {Y : Matrix m n E} (hX : ∀ i j, X i j ∈ A)
    (hY : ∀ i j, Y i j ∈ A) : ∀ i j, (X * Y) i j ∈ A := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by
  intro i j
  rw [Matrix.map_apply]
  exact hs _ (hX i j)

theorem map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]

theorem map_mul' {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul

end

end GlobalTheory.CompanionTheory.WittOrbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew
section
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem goodChar_of_hasConductor (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by
  have hcoe : ∀ z, (Circle.coeHom.compAddChar χ) z = 1 ↔ χ z = 1 := fun z => by
    show ((χ z : Circle) : ℂ) = 1 ↔ _
    exact Circle.coe_eq_one
  refine ⟨fun x => ?_, IsNonarchimedeanLocalField.isCompact_closedBall k 1, Valuation.isOpen_integer,
    fun x => ?_, fun U hU => ?_, fun x => ?_⟩
  · show ‖((χ x : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  · have key : (∀ y ∈ 𝒪[k], (Circle.coeHom.compAddChar χ) (x * y) = 1) ↔
        ∀ y, ValuativeRel.valuation k y ≤ ValuativeRel.valuation k x → χ y = 1 := by
      simp only [hcoe]
      constructor
      · intro H y hy
        by_cases hx : x = 0
        · have h0 : ValuativeRel.valuation k y = 0 := by
            rw [hx, map_zero] at hy
            exact le_antisymm hy zero_le'
          rw [(Valuation.zero_iff _).1 h0, AddChar.map_zero_eq_one]
        · have hmem : x⁻¹ * y ∈ 𝒪[k] := by
            rw [Valuation.mem_integer_iff, map_mul]
            calc ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k y
                ≤ ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k x :=
                  mul_le_mul_of_nonneg_left hy zero_le'
              _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          have h1 := H _ hmem
          rwa [mul_inv_cancel_left₀ hx] at h1
      · intro H y hy
        apply H
        rw [map_mul]
        calc ValuativeRel.valuation k x * ValuativeRel.valuation k y
            ≤ ValuativeRel.valuation k x * 1 :=
              mul_le_mul_of_nonneg_left ((Valuation.mem_integer_iff _ _).1 hy) zero_le'
          _ = ValuativeRel.valuation k x := mul_one _
    rw [key, hχ x, Valuation.mem_integer_iff, map_mul]
    constructor
    · intro hle
      calc ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k x
          ≤ ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k (c : k) :=
            mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    · intro hle
      calc ValuativeRel.valuation k x
          = ValuativeRel.valuation k ((c : k) * (((c⁻¹ : kˣ) : k) * x)) := by
            rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = ValuativeRel.valuation k (c : k) *
            ValuativeRel.valuation k (((c⁻¹ : kˣ) : k) * x) := map_mul _ _ _
        _ ≤ ValuativeRel.valuation k (c : k) * 1 := by
            rw [map_mul]
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = ValuativeRel.valuation k (c : k) := mul_one _
  · obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
    obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    obtain ⟨ϖ, hϖ⟩ := ValuativeRel.valuation_surjective (K := k) δ
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := k)
      (γ : ValuativeRel.ValueGroupWithZero k)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hz
      exact γ.ne_zero hz.symm
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖ
      exact hδ0.ne hϖ
    refine ⟨Units.mk0 (z * ϖ) (mul_ne_zero hz0 hϖ0), fun y hy => hγ ?_⟩
    have hy' : ValuativeRel.valuation k y ≤ 1 := (Valuation.mem_integer_iff _ _).1 hy
    show ValuativeRel.valuation k (z * ϖ * y) < γ
    rw [map_mul, map_mul, hz, hϖ]
    calc (γ : ValuativeRel.ValueGroupWithZero k) * δ * ValuativeRel.valuation k y
        ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hy' zero_le'
      _ = γ * δ := mul_one _
      _ < γ * 1 := mul_lt_mul_of_pos_left hδ1 (zero_lt_iff.2 γ.ne_zero)
      _ = γ := mul_one _
  · by_cases hx : ValuativeRel.valuation k x ≤ 1
    · exact ⟨1, by simp, by simpa [Valuation.mem_integer_iff] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨(Units.mk0 x hx0)⁻¹, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, Units.val_mk0, Valuation.map_inv]
        exact (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).2 (le_of_lt (not_le.1 hx))
      · rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0]
        exact one_mem _

theorem exists_goodChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by
  intro k _ _ _ _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine ⟨?_, fun ψ hψc hψn hψ1 => ?_⟩
  · obtain ⟨-, ⟨χ, -, -, hχ⟩, -⟩ := GlobalTheory.SplitWeil.conductor_exists k
    exact ⟨_, goodChar_of_hasConductor χ 1 hχ⟩
  · let χ : AddChar k Circle :=
      { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψn x)⟩
        map_zero_eq_one' := Circle.ext (by simp)
        map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
    have hχψ : Circle.coeHom.compAddChar χ = ψ := AddChar.ext _ _ fun x => rfl
    have hχc : Continuous χ := hψc.subtype_mk _
    have hχ1 : χ ≠ 1 := by
      intro h1
      apply hψ1
      rw [← hχψ, h1]
      exact AddChar.ext _ _ fun x => by simp
    obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
    exact ⟨c, hχψ ▸ goodChar_of_hasConductor χ c hc⟩

end GlobalTheory.CompanionTheory.VacLoc.GoodInh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.IdxAd.Unif

theorem resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by
  intro F _ _ v
  have hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) =
      (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr hS
  have hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F] := fun hx =>
    (GroundTheory.Global.mem_valuationInteger_iff v _).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)
  refine ⟨?_, ?_⟩
  · have h := GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
    rw [← h]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  · obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
    have hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      GroundTheory.Global.valued_of_irreducible v hq
    have hq0 : (q : v.adicCompletion F) ≠ 0 := fun h => hq.ne_zero (Subtype.ext h)
    have hp : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff e.symm).2 hq
    refine ⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩
    have ht : Valued.v (t : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.2 t.ne_zero
    set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha
    have hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) :
        v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval,
        ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]
      simp
    refine ⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · simp [mul_assoc]
    · rw [ha, Int.natAbs_neg]

end GlobalTheory.CompanionTheory.IdxAd.Unif
end

