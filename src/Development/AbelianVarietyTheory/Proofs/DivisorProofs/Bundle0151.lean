module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseJetVanishingMemPow
section
open Polynomial

namespace GlobalTheory

theorem hasseJet_vanishing_mem_pow (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w)
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  classical
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w
    have := hL 0 hN0 u w
    simpa using this
  let φ : A →+* k :=
    { toFun := Δ 0
      map_one' := h01
      map_mul' := hmul0
      map_zero' := map_zero _
      map_add' := map_add _ }
  have hφ : ∀ u, φ u = Δ 0 u := fun _ => rfl
  have halg : ∀ l c, Δ l (algebraMap k A c) = c * Δ l 1 := by
    intro l c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨algebraMap k A c, ?_⟩
    rw [hφ, halg, h01, mul_one]
  set Q : Ideal A := RingHom.ker φ with hQdef
  have hQmax : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hQmem : ∀ u, u ∈ Q ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    rw [Finset.sum_range_succ, Finset.sum_range_one] at this
    norm_num [h01] at this
    first | exact this | linear_combination -this
  have hvan : ∀ j, ∀ u ∈ Q ^ j, ∀ l < N, l < j → Δ l u = 0 := by
    intro j
    induction j with
    | zero => intro u _ l _ hl; omega
    | succ j ih =>
      intro u hu
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun r => ∀ l < N, l < j + 1 → Δ l r = 0) hu ?_ ?_
      · intro a ha b hb l hl hlj
        rw [hL l hl]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p < l + 1 := Finset.mem_range.mp hp
        by_cases hpj : p < j
        · rw [ih a ha p (by omega) hpj, zero_mul]
        · have : l - p = 0 := by omega
          rw [this, (hQmem b).mp hb, mul_zero]
      · intro a b ha hb l hl hlj
        rw [map_add (f := _), ha l hl hlj, hb l hl hlj, add_zero]
  set x : A := π - algebraMap k A (Δ 0 π) with hx
  have hx0 : Δ 0 x = 0 := by rw [hx, map_sub, halg, h01, mul_one, sub_self]
  have hx1 : Δ 1 x = 1 := by rw [hx, map_sub, halg, h11, mul_zero, sub_zero, hπ]
  have hxQ : x ∈ Q := (hQmem x).mpr hx0
  have hxpow : ∀ j < N, Δ j (x ^ j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using h01
    | succ j ih =>
      intro hj
      rw [pow_succ, hL (j + 1) hj, Finset.sum_eq_single j]
      · rw [ih (by omega), show j + 1 - j = 1 by omega, hx1, one_mul]
      · intro p hp hpj
        have hp' := Finset.mem_range.mp hp
        by_cases hlt : p < j
        · rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) hlt, zero_mul]
        · have : p = j + 1 := by omega
          subst this
          rw [Nat.sub_self, hx0, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  have hxQ2 : x ∉ Q ^ 2 := by
    intro h
    have := hvan 2 x h 1 hN1 (by norm_num)
    rw [hx1] at this
    exact one_ne_zero this
  obtain ⟨J, hJ⟩ : Q ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)
  have hJQ : Q ⊔ J = ⊤ := by
    by_contra hne
    have hle : J ≤ Q := by
      have := hQmax.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    apply hxQ2
    have : Ideal.span {x} ≤ Q ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self x)
  have hdec : ∀ j, Q ^ j ≤ Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
    intro j
    have htop : J ^ j ⊔ Q = ⊤ := by
      rw [sup_comm]
      exact Ideal.sup_pow_eq_top hJQ
    calc Q ^ j = Q ^ j * (J ^ j ⊔ Q) := by rw [htop, Ideal.mul_top]
      _ = Q ^ j * J ^ j ⊔ Q ^ j * Q := Ideal.mul_sup _ _ _
      _ = Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
        rw [← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]
      _ ≤ _ := le_rfl
  refine ⟨Q, hQmax, hQmem, fun f hf => ?_⟩
  have key : ∀ j ≤ N, f ∈ Q ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hdec j (ih (by omega)))
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hzv : Δ j z = 0 := hvan (j + 1) z hz j (by omega) (by omega)
      have hfj : Δ j f = 0 := hf j (by omega)
      have ha : Δ 0 a = 0 := by
        rw [← hyz, map_add (f := _), hzv, add_zero, mul_comm a, hL j (by omega),
          Finset.sum_eq_single j] at hfj
        · rwa [hxpow j (by omega), Nat.sub_self, one_mul] at hfj
        · intro p hp hpj
          have hp' := Finset.mem_range.mp hp
          rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) (by omega), zero_mul]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [← hyz]
      refine Ideal.add_mem _ ?_ hz
      rw [pow_succ, mul_comm a]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxQ j) ((hQmem a).mpr ha)
  exact key N le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

theorem hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr

theorem sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by
  intro V _ _ _ B _ _ _ om ρ h X l h1 h2 h3 Θ hd hc
  have sep : ∀ b b' : B, (∀ x, l x b = l x b') → b = b' := fun b b' hb => by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact h2 _ 0 le_rfl fun x => by rw [map_sub, hb, sub_self, norm_zero]
  have lsm : ∀ x (r : ℝ) (b : B), l x (r • b) = r • l x b := fun x r b => ((l x).restrictScalars ℝ).map_smul r b
  have key : ∀ f ∈ Θ, ∃ D : V →L[ℝ] B, (∀ z, D z ∈ Θ) ∧
      ∀ v, HasFDerivAt (fun w => ρ w f) (((ρ v).restrictScalars ℝ).comp D -
        (om v).smulRight (((π : ℂ) * I) • ρ v f)) v := by
    intro f hf
    choose g hg hg' using hc f hf
    have hgd : ∀ x z, l x (g z) = fderiv ℝ (fun v => l x (ρ v f)) 0 z := by
      intro x z
      refine (hg' z x).unique ?_
      have a1 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
      have a2 : HasFDerivAt (fun v => l x (ρ v f)) (fderiv ℝ (fun v => l x (ρ v f)) 0) ((0 : ℝ) • z) := by
        rw [zero_smul]; exact (hd f hf x 0).hasFDerivAt
      exact a2.comp_hasDerivAt (0 : ℝ) a1
    let D0 : V →ₗ[ℝ] B :=
      { toFun := g
        map_add' := fun z z' => sep _ _ fun x => by rw [map_add (f := _), hgd, hgd, hgd, map_add (f := _)]
        map_smul' := fun r z => sep _ _ fun x => by rw [RingHom.id_apply, lsm, hgd, hgd, map_smul] }
    let D : V →L[ℝ] B := LinearMap.toContinuousLinearMap D0
    have hD : ∀ z, D z = g z := fun z => rfl
    refine ⟨D, fun z => hg z, hasFDerivAt_of_norming l h1 h2 _ _ ?_ ?_⟩
    · refine continuous_clm_apply.2 fun z => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      have a1 := h.2.2.2 (D z)
      have a2 := h.2.2.2 f
      exact a1.sub ((om.continuous.clm_apply continuous_const).smul (a2.const_smul _))
    · intro x v
      obtain ⟨a, x', hx⟩ := h3 x v
      have e : (fun w => l x (ρ w f)) =
          fun w => cexp (-(π * I) * (om v (w - v) : ℝ)) * (a * l x' (ρ (w - v) f)) := by
        funext w
        rw [← hx, h.2.1, add_sub_cancel, map_smul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        simp
      have b0 : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v := (hasFDerivAt_id v).sub_const v
      have b1 : HasFDerivAt (fun w => l x' (ρ (w - v) f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) v := by
        have a2 : HasFDerivAt (fun v => l x' (ρ v f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) (v - v) := by
          rw [sub_self]; exact (hd f hf x' 0).hasFDerivAt
        simpa [Function.comp_def] using HasFDerivAt.comp (f := fun w : V => w - v) v a2 b0
      have b2 : HasFDerivAt (fun w : V => ((om v (w - v) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om v)) v := by
        simpa [Function.comp_def] using (Complex.ofRealCLM.comp (om v)).hasFDerivAt.comp v b0
      have b3 := ((b2.const_mul (-(π * I) : ℂ)).cexp).mul (b1.const_mul a)
      rw [e]
      refine b3.congr_fderiv ?_
      ext z
      simp [← hgd, h.1, hD, lsm, hx]
      ring
  have ind : ∀ n : ℕ, ∀ f ∈ Θ, ContDiff ℝ n fun v => ρ v f := by
    intro n
    induction n with
    | zero => intro f _; exact contDiff_zero.2 (h.2.2.2 f)
    | succ n ih =>
      intro f hf
      obtain ⟨D, hD, hF⟩ := key f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun v => (hF v).differentiableAt, by simp, fun z => ?_⟩
      simp only [(hF _).fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      exact (ih _ (hD z)).sub ((om.contDiff.clm_apply contDiff_const).smul ((ih f hf).const_smul _))
  intro f hf
  exact contDiff_infty.2 fun n => ind n f hf

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagComplementPosDefFactorizationStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_flag_complement_posDef_factorization : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  first | exact @GlobalTheory.schur_complement_step_cpx | exact GlobalTheory.schur_complement_step_cpx | (intros; apply GlobalTheory.schur_complement_step_cpx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagUnipotentMatrixExistsSparseStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  first | exact @GlobalTheory.isotropic_unipotent_column_relations | exact GlobalTheory.isotropic_unipotent_column_relations | (intros; apply GlobalTheory.isotropic_unipotent_column_relations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormConstMulInner
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem gaussian_selfPairing_pos (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (∫ x, GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x *
      starRingEnd ℂ (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x)) = (r : ℂ) := by
  refine ⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩
  · rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    have : 0 < Real.pi / (2 * Real.pi) := by positivity
    positivity
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem hermitian_form_eq_smul_l2 : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hherm hpos hid
  set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀
  obtain ⟨r, hr, hs⟩ := gaussian_selfPairing_pos n
  have hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ) := by
    have := hherm h₀ h₀
    apply Complex.ext
    · simp
    · have h2 : (B h₀ h₀).im = -(B h₀ h₀).im := by
        conv_lhs => rw [this]
        simp
      simp; linarith
  refine ⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩
  have key := hid h₀ h' h₀ h
  rw [hs, hb] at key
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linear_combination key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormEqCombinationOfSelfAdjointIdentityStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w)) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) →
    ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  first | exact @GlobalTheory.herm_form_identity | exact GlobalTheory.herm_form_identity | (intros; apply GlobalTheory.herm_form_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearranged
section
namespace GlobalTheory.CovNum

open Formalism.NormVectorIdentities.Items

theorem hsLogRho_bounds (D : ℕ) (n Λ δ h l₀ : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hΛ : 1 ≤ Λ)
    (hδ : 1 ≤ δ)
    (hl : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀) :
    0 ≤ hsLogRho 26 n D 1 Λ δ h ∧
      hsLogRho 26 n D 1 Λ δ h ≤ l₀ + 26 * Real.log (2 + |h|) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hh : 0 ≤ |h| := abs_nonneg h
  have h1 : 1 ≤ n * D * δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hD') hδ
  have h2 : 1 ≤ n * D * δ * (2 + |h| + Real.log Λ) :=
    one_le_mul_of_one_le_of_one_le h1 (by linarith)
  have h3 : n * D * δ * (2 + |h| + Real.log Λ)
      ≤ (n * D * δ * (1 + Real.log Λ)) * (2 + |h|) := by
    rw [mul_assoc (n * D * δ)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hL hh]
  have h4 : Real.log (n * D * δ * (2 + |h| + Real.log Λ))
      ≤ Real.log (n * D * δ * (1 + Real.log Λ)) + Real.log (2 + |h|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) h3
  have h5 := Real.log_nonneg h2
  unfold hsLogRho
  rw [mul_one]
  constructor <;> linarith

theorem deg_lower_of_claim : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  intro T D n Λ β ΛD ΛT J δ h d deg z l₀ hT hD hn hΛ hβ hΛD hΛT hδ hd hz hz2 hP hl hc
  obtain ⟨hρ0, hρ⟩ := hsLogRho_bounds D n Λ δ h l₀ hD hn hΛ hδ hl
  obtain ⟨-, -, hc⟩ := hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 < β := by linarith
  have e1 : Real.log (Real.exp (hsLogRho 26 n D 1 Λ δ h) * T)
      = hsLogRho 26 n D 1 Λ δ h + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have e2 : Real.log (2 * Real.exp (hsLogRho 26 n D 1 Λ δ h) * Real.sqrt β)
      = Real.log 2 + hsLogRho 26 n D 1 Λ δ h + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβ0.le]
  rw [e1, e2, le_div_iff₀ hd] at hc
  unfold hsZ hsR at hc
  generalize hsLogRho 26 n D 1 Λ δ h = ρ at hρ0 hρ hc
  generalize ((Nat.choose (T - 1) D : ℕ) : ℝ) * δ = P at hP hc ⊢
  generalize hsG D n = g at hc ⊢
  have hb := Real.log_nonneg hβ
  have hLD := Real.log_nonneg hΛD
  have hLT := Real.log_nonneg hΛT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  generalize Real.log (2 + |h|) = L at hρ ⊢
  have hdP : d ≤ 2 * P := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have hdef : d - P ≤ 2 * z * P := by nlinarith
  set A := (T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 26 * (D : ℝ) ^ 2 * (ρ + Real.log T)
    - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) with hA
  set B := (T : ℝ) * (Real.log 2 + ρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e3 : ((1 - (1 - P / d)) * A - (1 - P / d) * B) * d = P * A - (d - P) * B := by
    field_simp
    ring
  rw [e3] at hc
  have h6 : (d - P) * B ≤ 2 * z * P * B := mul_le_mul_of_nonneg_right hdef hB0
  have h7 : 0 ≤ (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ) :=
    mul_nonneg (by positivity) (by linarith)
  have h8 : P * (A - 2 * z * B - (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ))
      ≤ P * (A - 2 * z * B) := mul_le_mul_of_nonneg_left (by linarith) hP0
  refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
  rw [hA, hB]
  ring

end GlobalTheory.CovNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquationStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_components_of_cone_integral_equation : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 → ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.homogeneous_components_of_integral_equation | exact GlobalTheory.homogeneous_components_of_integral_equation | (intros; apply GlobalTheory.homogeneous_components_of_integral_equation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ] (f g : MvPolynomial σ Ω) (D : ℕ), f ≠ 0 → f.totalDegree ≤ D → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  first | exact @GlobalTheory.hypersurface_diff_isPreirreducible | exact GlobalTheory.hypersurface_diff_isPreirreducible | (intros; apply GlobalTheory.hypersurface_diff_isPreirreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdeals
section
namespace GlobalTheory

theorem iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)

end GlobalTheory
end

