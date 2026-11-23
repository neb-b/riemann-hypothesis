module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqGaussianOfFderivAddEqZero
section
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_eq_gaussian_of_fderiv_add_eq_zero
    (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ))
    (H : ∀ (j : l) (x : EuclideanSpace ℝ l),
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0)
    (x : EuclideanSpace ℝ l) :
    h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  have hE : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2))
        (Real.exp (Real.pi * ‖y‖ ^ 2) • (Real.pi • (2 • innerSL ℝ y))) y := by
    intro y
    exact ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul Real.pi).exp
  have hu : ∀ y : EuclideanSpace ℝ l,
      HasFDerivAt (fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
        (0 : EuclideanSpace ℝ l →L[ℝ] ℂ) y := by
    intro y
    have h1 := (hE y).smul (h.differentiableAt (x := y)).hasFDerivAt
    refine h1.congr_fderiv ?_
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun l ℝ).toBasis.ext
    intro j
    have h2 := H j y
    have h3 : fderiv ℝ (⇑h) y (EuclideanSpace.single j 1) = -(2 * Real.pi * (y j : ℂ) * h y) :=
      eq_neg_of_add_eq_zero_left h2
    simp [h3, EuclideanSpace.inner_single_right]
    ring
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (f := fun y : EuclideanSpace ℝ l => Real.exp (Real.pi * ‖y‖ ^ 2) • h y)
    (fun y => (hu y).differentiableAt) (fun y => (hu y).fderiv) x 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, one_smul] at hc
  rw [← hc, Complex.real_smul, mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
section
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate

noncomputable section

namespace GlobalTheory.WrongSignGauss

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip

@[simp] theorem sesq_apply (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring

def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))

theorem mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by
  rw [mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]
  simp [Complex.real_smul]

theorem lineDerivOp_mulForm (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]

theorem lineDerivOp_comm' (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f

theorem twD_apply (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]

section integrals

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ

theorem integrable_ip (u w : 𝓢(V, ℂ)) : Integrable (fun x => u x * conj (w x)) μ := by
  have h := (pairing sesq u w).integrable (μ := μ)
  simpa [pairing_apply] using h

theorem ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ u (c • w) = conj c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by
  simp only [ip, SchwartzMap.sub_apply, sub_mul]
  exact integral_sub (integrable_ip μ u w) (integrable_ip μ v w)

theorem ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by
  simp only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]
  exact integral_sub (integrable_ip μ w u) (integrable_ip μ w v)

theorem ip_lineDerivOp (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]

theorem ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring

theorem ip_twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring

end integrals

theorem lineDerivOp_twD (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]

theorem twD_comm (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    twD a₁ ℓ₁ (twD a₂ ℓ₂ f) - twD a₂ ℓ₂ (twD a₁ ℓ₁ f) =
      (-(2 * Real.pi * Complex.I) * ((ℓ₂ a₁ - ℓ₁ a₂ : ℝ) : ℂ)) • f := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f),
    lineDerivOp_twD]
  rw [twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]
  push_cast
  ring

section main

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem ip_self (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  first
  | rw [← integral_complex_ofReal]
  | rw [← integral_ofReal (𝕜 := ℂ)]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_twD (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E

end main

theorem vanish : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx

end GlobalTheory.WrongSignGauss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

def Stab {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (N : Submodule ℂ V) : Prop :=
  ∀ g ∈ G, ∀ x ∈ N, g x ∈ N

def SimpleOver {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Prop :=
  ∀ N : Submodule ℂ V, Stab G N → K ≤ N → N = K ∨ N = ⊤

def piOp {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (⨂[ℂ] j, M j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)

def piOps {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) :
    Set (Module.End ℂ (⨂[ℂ] j, M j)) :=
  {f | ∃ i, ∃ g ∈ Op i, f = piOp i g}

def tensOps {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) : Set (Module.End ℂ (V₀ ⊗[ℂ] V₁)) :=
  {f | ∃ g ∈ A, f = TensorProduct.map g LinearMap.id} ∪
    {f | ∃ h ∈ B, f = TensorProduct.map LinearMap.id h}

def piKer {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (K : ∀ i, Submodule ℂ (M i)) : Submodule ℂ (⨂[ℂ] j, M j) :=
  Submodule.span ℂ {t | ∃ y : ∀ i, M i, (∃ i, y i ∈ K i) ∧ t = PiTensorProduct.tprod ℂ y}

def tensKer {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) : Submodule ℂ (V₀ ⊗[ℂ] V₁) :=
  Submodule.span ℂ {t | ∃ (x : V₀) (y : V₁), (x ∈ K₀ ∨ y ∈ K₁) ∧ t = x ⊗ₜ[ℂ] y}

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValues
section
open Submodule

namespace GlobalTheory.SubmodulePowSimple

variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

def equivValues (a : ι → Module.End ℂ P) (m : ℕ) (N : Submodule ℂ (Fin m → P)) :
    Set (Fin m → P) :=
  {v | ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
    (∀ p, S p ∈ N) ∧ ∃ q, v = S q}

def snocZero (m : ℕ) : (Fin m → P) →ₗ[ℂ] (Fin (m+1) → P) where
  toFun z := Fin.snoc (α := fun _ => P) z 0
  map_add' x y := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  map_smul' c x := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma snocZero_diag {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]

lemma single_diag {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mem_span_equivValues (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by
  intro m
  induction m with
  | zero =>
    intro N _ y _
    rw [Subsingleton.elim y 0]; exact zero_mem _
  | succ m ih =>
    intro N hN y hy
    let B : Submodule ℂ P := N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))
    have hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
      simp [B]
    have hBst : ∀ i, ∀ p ∈ B, a i p ∈ B := by
      intro i p hp
      rw [hBmem] at hp ⊢
      rw [single_diag]; exact hN i _ hp
    by_cases hB : B = ⊥
    · let I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P) := LinearMap.funLeft ℂ P Fin.castSucc
      have hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂ := by
        intro x₁ h₁ x₂ h₂ he
        have hd : x₁ - x₂ ∈ N := N.sub_mem h₁ h₂
        have hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m)) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j
          · simp
          · have h := congrFun he j
            change x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h
            rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
            simp [h]
        have hB' : (x₁ - x₂) (Fin.last m) ∈ B := by
          rw [hBmem, ← hs']; exact hd
        rw [hB, Submodule.mem_bot] at hB'
        rw [hB', Pi.single_zero] at hs'
        exact sub_eq_zero.mp hs'
      let N0 := N.map I
      have hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0 := by
        intro i w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨_, hN i x hx, rfl⟩
      have lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) →
          ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p := by
        intro S hS
        let J : N →ₗ[ℂ] (Fin m → P) := I ∘ₗ N.subtype
        have hJ : Function.Injective J := by
          intro u v huv; exact Subtype.ext (hinj u u.2 v v.2 huv)
        have hS' : ∀ p, S p ∈ LinearMap.range J := by
          intro p; obtain ⟨x, hx, hxe⟩ := hS p; exact ⟨⟨x, hx⟩, hxe⟩
        have key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v := fun v => by
          have h := congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)
          rw [LinearEquiv.ofInjective_apply] at h
          exact h
        refine ⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ
          S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩
        exact key ⟨S p, hS' p⟩
      have h1 := ih N0 hN0 (I y) ⟨y, hy, rfl⟩
      obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').mp h1
      have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
          (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
      choose S hSa hSN q hq using hg
      choose S' hS'N hS'I using fun k => lift (S k) (hSN k)
      have hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j) := by
        intro k i p
        apply hinj _ (hS'N k _) _ (hN i _ (hS'N k p))
        rw [hS'I, hSa, ← hS'I k p]; rfl
      have hy_eq : y = ∑ k, f k • S' k (q k) := by
        apply hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hfg, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hS'I, hq]
      rw [hy_eq]
      exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)
    · have hBt := hs B hBst hB
      have hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
        rw [← hBmem, hBt]; exact Submodule.mem_top
      obtain ⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m)) := ⟨_, rfl⟩
      have hy'N : y' ∈ N := hy' ▸ N.sub_mem hy (hmem _)
      have hy'last : y' (Fin.last m) = 0 := by simp [hy']
      let N' := N.comap (snocZero m)
      have hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N' := by
        intro i z hz
        show snocZero m _ ∈ N
        rw [snocZero_diag]; exact hN i _ hz
      let z : Fin m → P := fun j => y' (Fin.castSucc j)
      have hz : snocZero m z = y' := by
        funext j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [snocZero, hy'last]
        · simp [snocZero, z]
      have hzN' : z ∈ N' := show snocZero m z ∈ N from hz ▸ hy'N
      have h1 := ih N' hN' z hzN'
      have h2 : y' ∈ span ℂ (equivValues a (m+1) N) := by
        rw [← hz]
        have h := Submodule.mem_map_of_mem (f := snocZero m) h1
        rw [Submodule.map_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩
        refine ⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩
        intro i p; simp only [LinearMap.comp_apply, hSa, snocZero_diag]
      have h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈
          span ℂ (equivValues a (m+1) N) := by
        refine Submodule.subset_span
          ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩
        · intro i p; simp only [LinearMap.single_apply]; exact single_diag _ _
        · intro p; simpa using hmem p
      have : y = y' + Pi.single (Fin.last m) (y (Fin.last m)) := by simp [hy']
      rw [this]; exact add_mem h2 h3

end GlobalTheory.SubmodulePowSimple

namespace GlobalTheory

theorem submodule_pow_simple_eq_sum_equiv_values :
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧
        y = ∑ l, Sm l (q l) := by
  intro P _ _ ι a hs m N hN y hy
  obtain ⟨n, f, g, hfg⟩ :=
    (Submodule.mem_span_set').mp (SubmodulePowSimple.mem_span_equivValues a hs m N hN y hy)
  have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
      (∀ p, S p ∈ N) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
  choose S hSa hSN q hq using hg
  refine ⟨n, S, fun k => f k • q k, hSa, hSN, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdUpdateRegroup
section
open Finset

namespace GlobalTheory

theorem sum_update_fiber_count {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (G : (∀ i, Fin (m i)) → ℂ) :
    ∑ J : (∀ i, Fin (m i)), ∑ j : Fin (m i₀), G (Function.update J i₀ j) = (m i₀ : ℂ) * ∑ J, G J := by
  let e : (∀ i, Fin (m i)) × Fin (m i₀) ≃ (∀ i, Fin (m i)) × Fin (m i₀) :=
    { toFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Fintype.sum_prod_type' (fun J j => G (Function.update J i₀ j))]
  rw [Fintype.sum_equiv e (fun p => G (Function.update p.1 i₀ p.2)) (fun p => G p.1) (fun p => rfl)]
  rw [Fintype.sum_prod_type' (fun J (_ : Fin (m i₀)) => G J)]
  simp [Finset.mul_sum]

theorem sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  intro ι _ _ X W _ _ m k ℓ i₀ F F' w w' hone v
  have key : ∀ (u : W i₀) (H : (∀ i, X i) → ℂ) (J : ∀ i, Fin (m i)),
      ∑ j, (∏ i, ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)) *
          H (fun i => k i (Function.update J i₀ j i))
        = (∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i)) *
          ∑ j, ℓ i₀ j u * H (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) := by
    intro u H J
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest : ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)
        = ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := by simpa using hi
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hk : (fun i => k i (Function.update J i₀ j i)) = Function.update (fun i => k i (J i)) i₀ (k i₀ j) := by
      funext i
      exact Function.apply_update k J i₀ j i
    rw [hrest, hk, Function.update_self, Function.update_self]
    ring
  by_cases hm : m i₀ = 0
  · haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by
      have h := J i₀
      rw [hm] at h
      exact h.elim0⟩
    simp
  · have hm' : (m i₀ : ℂ) ≠ 0 := by exact_mod_cast hm
    apply mul_left_cancel₀ hm'
    rw [← sum_update_fiber_count, ← sum_update_fiber_count]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [key w' F J, key w F' J, hone J]

end GlobalTheory
end

