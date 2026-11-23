module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryA
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

section Bump

def hsOne (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖(g - 1) i j‖ ^ 2

theorem sum_sq_norm_eq_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = (trace (Aᴴ * A)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem hsOne_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : hsOne (k * g * star k) = hsOne g := by
  have h1' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have e : k * g * star k - 1 = k * (g - 1) * kᴴ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1']
  have e2 : (k * (g - 1) * kᴴ)ᴴ * (k * (g - 1) * kᴴ) = k * ((g - 1)ᴴ * (g - 1)) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, h2, Matrix.one_mul]
  unfold hsOne
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2,
    Matrix.one_mul]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)

theorem contDiff_hsOne : ContDiff ℝ ∞ (hsOne (n := n)) := by
  unfold hsOne
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℂ).comp ((contDiff_entry i j).sub contDiff_const)

def arbB (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (r ^ 2 - hsOne g)

theorem contDiff_arbB (r : ℝ) : ContDiff ℝ ∞ (arbB (n := n) r) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_hsOne)

theorem arbB_nonneg (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ arbB r g :=
  Real.smoothTransition.nonneg _

theorem arbB_one_pos {r : ℝ} (hr : 0 < r) : 0 < arbB r (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h0 : hsOne (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hsOne]
  unfold arbB
  rw [h0, sub_zero]
  exact Real.smoothTransition.pos_of_pos (by positivity)

theorem norm_lt_of_arbB_ne {r : ℝ} (hr : 0 < r) {g : Matrix (Fin n) (Fin n) ℂ} (h : arbB r g ≠ 0) :
    ‖g - 1‖ < r := by
  have hlt : hsOne g < r ^ 2 := by
    by_contra hc
    push Not at hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  rw [Matrix.norm_lt_iff hr]
  intro i j
  have h1 : ‖(g - 1) i j‖ ^ 2 ≤ hsOne g := by
    unfold hsOne
    calc ‖(g - 1) i j‖ ^ 2 ≤ ∑ j', ‖(g - 1) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖(g - 1) i j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖(g - 1) i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(g - 1) i' j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ i)
  have h3 : ‖(g - 1) i j‖ ^ 2 < r ^ 2 := lt_of_le_of_lt h1 hlt
  nlinarith [norm_nonneg ((g - 1) i j)]

theorem hasCompactSupport_arbB {r : ℝ} (hr : 0 < r) : HasCompactSupport (arbB (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) fun g hg => ?_
  by_contra h
  exact hg (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (norm_lt_of_arbB_ne hr h).le)

theorem arbB_conj (r : ℝ) {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (g : Matrix (Fin n) (Fin n) ℂ) : arbB r (k * g * star k) = arbB r g := by
  unfold arbB
  rw [hsOne_conj hk.1]

end Bump

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem arb_umat_cont : Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous

theorem arb_umat_mem (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem arb_orbit_cont (hσ : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (fun y : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat y) w) :=
  (hσ.2.2 w).comp_continuous arb_umat_cont arb_umat_mem

theorem arb_rep_mul (hσ : IsURepOn (UJset ε) σ) (a b : Formalism.REAL.UJ ε) (v : H) :
    σ (Formalism.MainNotions.S.umat (a * b)) v = σ (Formalism.MainNotions.S.umat a) (σ (Formalism.MainNotions.S.umat b) v) := by
  show σ (Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b) v = _
  rw [hσ.1.2 _ (arb_umat_mem a) _ (arb_umat_mem b), ContinuousLinearMap.comp_apply]

theorem arb_exists_umat {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ γ : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat γ = g := by
  have : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => ((y : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).2]; exact hg
  exact this

theorem arb_integrable (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) :
    Integrable (fun y : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) (Formalism.REAL.muG ε) :=
  ((hα.comp arb_umat_cont).smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport
    ((hαc.comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1).smul_right)

theorem opConv_add (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (v w : H) :
    opConv ε σ α (v + w) = opConv ε σ α v + opConv ε σ α w := by
  unfold opConv
  rw [← integral_add (arb_integrable hσ v hα hαc) (arb_integrable hσ w hα hαc)]
  congr 1
  funext y
  rw [map_add (f := _), smul_add]

theorem opConv_smul {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (v : H) :
    opConv ε σ α (c • v) = c • opConv ε σ α v := by
  unfold opConv
  rw [← integral_smul]
  congr 1
  funext y
  rw [map_smul, smul_comm]

theorem opConv_comm_K (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (hαK : IsAdKInv ε α) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (v : H) : σ k (opConv ε σ α v) = opConv ε σ α (σ k v) := by
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  obtain ⟨κ, hκ⟩ := arb_exists_umat hkU
  have hku : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hku' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : Formalism.MainNotions.S.umat κ⁻¹ = kᴴ := by
    have h3 : Formalism.MainNotions.S.umat κ⁻¹ * k = 1 := by
      rw [← hκ]
      show Formalism.MainNotions.S.umat (κ⁻¹ * κ) = 1
      rw [inv_mul_cancel]
      rfl
    calc Formalism.MainNotions.S.umat κ⁻¹ = Formalism.MainNotions.S.umat κ⁻¹ * (k * kᴴ) := by rw [hku', Matrix.mul_one]
      _ = kᴴ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hF : ∀ y : Formalism.REAL.UJ ε,
      σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) =
        (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * (y * κ⁻¹)) := by
    intro y
    have e1 : Formalism.MainNotions.S.umat (κ * (y * κ⁻¹)) = k * Formalism.MainNotions.S.umat y * star k := by
      show Formalism.MainNotions.S.umat κ * (Formalism.MainNotions.S.umat y * Formalism.MainNotions.S.umat κ⁻¹) = _
      rw [hκ, hinv, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have m1 : k * Formalism.MainNotions.S.umat y * star k ∈ UJset ε := e1 ▸ arb_umat_mem (κ * (y * κ⁻¹))
    have h4 : k * Formalism.MainNotions.S.umat y * star k * k = k * Formalism.MainNotions.S.umat y := by
      rw [Matrix.mul_assoc (k * _), Matrix.star_eq_conjTranspose, hku, Matrix.mul_one]
    have e2 : σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v) = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
      calc σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v)
          = ((σ (k * Formalism.MainNotions.S.umat y * star k)).comp (σ k)) v := rfl
        _ = σ (k * Formalism.MainNotions.S.umat y * star k * k) v := by rw [hσ.1.2 _ m1 _ hkU]
        _ = σ (k * Formalism.MainNotions.S.umat y) v := by rw [h4]
        _ = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
            rw [hσ.1.2 _ hkU _ (arb_umat_mem y)]
            rfl
    show _ = α (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) • σ (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) (σ k v)
    rw [e1, hαK k hk, e2, map_smul]
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ v hα hαc)]
  calc ∫ y, σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * (y * κ⁻¹)) ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        exact hF y
    _ = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * y) ∂(Formalism.REAL.muG ε) :=
        integral_mul_right_eq_self
          (fun y => (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * y)) κ⁻¹
    _ = ∫ y, α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) (σ k v) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) κ

theorem opConv_translate (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (γ : Formalism.REAL.UJ ε) :
    σ (Formalism.MainNotions.S.umat γ) (opConv ε σ α w) =
      ∫ y, α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε) := by
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ w hα hαc)]
  calc ∫ y, σ (Formalism.MainNotions.S.umat γ) (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) (γ * y)
          ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        show _ = α (Formalism.MainNotions.S.umat (γ⁻¹ * (γ * y))) • σ (Formalism.MainNotions.S.umat (γ * y)) w
        rw [inv_mul_cancel_left, map_smul, arb_rep_mul hσ]
    _ = _ := integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) γ

end Conv

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem data_equiv_derived (hgap : StdGap ε lam)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (U : closGen E₁ V₁ ≃ₗᵢ[ℂ] closGen E₂ V₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : closGen E₁ V₁,
      (x : H₁) = σ₁ g (y : H₁) → ((U x : closGen E₂ V₂) : H₂) = σ₂ g ((U y : closGen E₂ V₂) : H₂))
    (x : D₁) (hx : x ∈ genSub E₁ V₁) (x' : closGen E₁ V₁) (hx' : (x' : H₁) = x) :
    ∃ y : D₂, y ∈ genSub E₂ V₂ ∧ ((U x' : closGen E₂ V₂) : H₂) = y ∧
      ∀ (a b : Fin n) (x'' : closGen E₁ V₁), (x'' : H₁) = ((E₁ a b x : D₁) : H₁) →
        ((U x'' : closGen E₂ V₂) : H₂) = ((E₂ a b y : D₂) : H₂) := by
  classical
  have hst₁ := closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁
  have hint : ∀ g ∈ UJset ε, ∀ z ∈ closGen E₁ V₁, ICD.ext U (σ₁ g z) = σ₂ g (ICD.ext U z) :=
    fun g hg z hz => ICD.ext_intertw U hU hst₁ hg hz

  have hV12 : ∀ v ∈ V₁, ∃ w ∈ V₂, (w : H₂) = ICD.ext U (v : H₁) := by
    have hK := data_isKTypeOf hgap hσ₁ hD₁ hV₁ hc₁ hVK₁
    have hle : V₁.map D₁.subtype ≤ closGen E₁ V₁ := by
      rintro _ ⟨v, hv, rfl⟩
      exact ICD.mem_closGen (ICD.le_gen E₁ V₁ hv)
    have hT := ICD.ktype_map (σ₂ := σ₂) (closGen E₁ V₁) (ICD.ext U : H₁ →ₗ[ℂ] H₂)
      (fun z hz w hw h => ICD.ext_inj U hz hw h)
      (fun g hg z hz => hint g (smd_inUJ_of_Kset hg) z hz)
      (fun g hg z hz => hst₁ g (smd_inUJ_of_Kset hg) z hz) hle hK
    have hS2 : (V₁.map D₁.subtype).map (ICD.ext U : H₁ →ₗ[ℂ] H₂) ≤ closGen E₂ V₂ := by
      rintro _ ⟨z, -, rfl⟩
      exact ICD.ext_mem U z
    have heq := data_lowK_eq hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ _ hS2 hT
    intro v hv
    have hm : (ICD.ext U : H₁ →ₗ[ℂ] H₂) (D₁.subtype v) ∈
        (V₁.map D₁.subtype).map (ICD.ext U : H₁ →ₗ[ℂ] H₂) :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hv)
    rw [heq] at hm
    obtain ⟨w, hw, e⟩ := hm
    exact ⟨w, hw, e⟩

  let P : Submodule ℂ D₁ :=
    { carrier := {z | z ∈ genSub E₁ V₁ ∧ ∃ y : D₂, y ∈ genSub E₂ V₂ ∧ ICD.ext U (z : H₁) = (y : H₂)}
      add_mem' := by
        rintro a b ⟨ha, ya, hya, ea⟩ ⟨hb, yb, hyb, eb⟩
        exact ⟨add_mem ha hb, ya + yb, add_mem hya hyb, by simp [ea, eb]⟩
      zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ya, hya, ea⟩
        exact ⟨Submodule.smul_mem _ c ha, c • ya, Submodule.smul_mem _ c hya, by simp [ea]⟩ }
  have hle : genSub E₁ V₁ ≤ P := by
    refine ICD.gen_le (fun v hv => ?_) (fun a b z hz => ?_)
    · obtain ⟨w, hw, e⟩ := hV12 v hv
      exact ⟨ICD.le_gen E₁ V₁ hv, w, ICD.le_gen E₂ V₂ hw, e.symm⟩
    · obtain ⟨hz1, y, hy, e⟩ := hz
      exact ⟨ICD.gen_stable hz1 a b, E₂ a b y, ICD.gen_stable hy a b,
        ICD.map_E hD₁ hD₂ (ICD.ext U) (closGen E₁ V₁) hint z (ICD.mem_closGen hz1) y e a b⟩
  obtain ⟨-, y, hy, e⟩ := hle hx
  refine ⟨y, hy, ?_, fun a b x'' hx'' => ?_⟩
  · rw [← ICD.ext_apply', hx', e]
  · rw [← ICD.ext_apply', hx'',
      ICD.map_E hD₁ hD₂ (ICD.ext U) (closGen E₁ V₁) hint x (ICD.mem_closGen hx) y e a b]

end Two

namespace ICD

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, apply_ite (⇑f), map_zero, AlgHom.commutes]

theorem qdet_mem {B : Type*} [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ B) (F : Fin n → Fin n → B)
    (hF : ∀ a b, F a b ∈ S) (u : ℂ) : Formalism.REAL.qdet F u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine S.sum_mem fun τ _ => S.mul_mem ?_ (list_prod_mem fun z hz => ?_)
  · rw [← zsmul_one]
    exact zsmul_mem S.one_mem _
  · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    unfold Formalism.REAL.Tm
    refine S.add_mem ?_ (hF _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def relAlg (R : M₁ → M₂ → Prop) (hadd : ∀ x y x' y', R x y → R x' y' → R (x + x') (y + y'))
    (hsmul : ∀ (c : ℂ) x y, R x y → R (c • x) (c • y)) :
    Subalgebra ℂ (Module.End ℂ M₁ × Module.End ℂ M₂) where
  carrier := {p | ∀ x y, R x y → R (p.1 x) (p.2 y)}
  mul_mem' := fun ha hb x y h => ha _ _ (hb x y h)
  add_mem' := fun ha hb x y h => hadd _ _ _ _ (ha x y h) (hb x y h)
  algebraMap_mem' := fun c x y h => by
    simp only [Prod.algebraMap_apply, Module.algebraMap_end_apply]
    exact hsmul c x y h

end ICD

section One

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem ICD.transfer (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) (hP : IsPsiFor ε lam T Ψ)
    {p₁ : Module.End ℂ D} {p₂ : Module.End ℂ (smD ε (rreg ε))}
    (hp : (p₁, p₂) ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)))
    (c : ℂ) (hc2 : ∀ v₀ : T.V, v₀ ≠ 0 → ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), p₂ y = c • y)
    (x : D) (hx : x ∈ genSub E V) : p₁ x = c • x := by
  classical
  have hv₀ : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨U, hU⟩ := sigLam_equiv_data hgap hP hv₀ hσ hD hV hc hVK hV0
  have hσ₂ := rreg_isURepOn ε
  have hD₂ := isDerivedOn_smE hσ₂
  have hU' : ∀ g ∈ UJset ε, ∀ x y : closGen E V,
      (x : H) = σ g (y : H) → ((U.symm x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g ((U.symm y : Hlam ε Ψ T.w) : L2 ε) := by
    intro g hg x y hxy
    have h1 := hU g hg (U.symm y)
    rw [U.apply_symm_apply] at h1
    have : x = U (sigLam ε Ψ T.w g (U.symm y)) := Subtype.ext (hxy.trans h1.symm)
    rw [this, U.symm_apply_apply, sigLam_coe hgap hP hv₀ hg]
  have hst := closGen_stable hgap hσ hD hV hc hVK
  have hint : ∀ g ∈ UJset ε, ∀ z ∈ closGen E V, ICD.ext U.symm (σ g z) = rreg ε g (ICD.ext U.symm z) :=
    fun g hg z hz => ICD.ext_intertw U.symm hU' hst hg hz
  let R : D → smD ε (rreg ε) → Prop := fun x y =>
    x ∈ genSub E V ∧ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ∧ ICD.ext U.symm (x : H) = (y : L2 ε)
  let S := ICD.relAlg R
    (fun x y x' y' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩ => ⟨add_mem h1 h1', add_mem h2 h2', by simp [h3, h3']⟩)
    (fun c x y ⟨h1, h2, h3⟩ => ⟨Submodule.smul_mem _ c h1, Submodule.smul_mem _ c h2, by simp [h3]⟩)
  have hgen : Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ∀ x y, R x y → R (E a b x) (smE ε (rreg ε) a b y)
    rintro x y ⟨h1, h2, h3⟩
    exact ⟨ICD.gen_stable h1 a b, ICD.gen_stable h2 a b,
      ICD.map_E hD hD₂ (ICD.ext U.symm) (closGen E V) hint x (ICD.mem_closGen h1) y h3 a b⟩
  obtain ⟨y, hy, hxy, -⟩ := data_equiv_derived hgap hσ hD hV hc hVK hσ₂ hD₂ (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP T.w) (datumV_kStable hP T.w) U.symm hU' x hx ⟨x, ICD.mem_closGen hx⟩ rfl
  have hR : R x y := ⟨hx, hy, by rw [ICD.ext_apply U.symm _ (ICD.mem_closGen hx)]; exact hxy⟩
  have hpS : ∀ x y, R x y → R (p₁ x) (p₂ y) := hgen hp
  obtain ⟨h1, -, h3⟩ := hpS x y hR
  refine Subtype.ext (ICD.ext_inj U.symm (ICD.mem_closGen h1)
    (ICD.mem_closGen (Submodule.smul_mem _ c hx)) ?_)
  rw [h3, hc2 T.w hv₀ y hy, Submodule.coe_smul, Submodule.coe_smul, map_smul, hR.2.2]

theorem ICD.pair_mem_adjoin {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (a b : Fin n) :
    (E₁ a b, E₂ a b) ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E₁ ab.1 ab.2, E₂ ab.1 ab.2)) :=
  Algebra.subset_adjoin ⟨(a, b), rfl⟩

theorem capelli_data (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (x : D) (hx : x ∈ genSub E V) :
    Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) x = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x := by
  classical
  have hF : ∀ a b, (E a b, smE ε (rreg ε) a b) ∈
      Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) :=
    ICD.pair_mem_adjoin _ _
  have hm := ICD.qdet_mem _ (fun a b => (E a b, smE ε (rreg ε) a b)) hF (Y + ((n : ℂ) - 1) / 2)
  have h1 := ICD.qdet_map (AlgHom.fst ℂ _ _) (fun a b => (E a b, smE ε (rreg ε) a b)) (Y + ((n : ℂ) - 1) / 2)
  have h2 := ICD.qdet_map (AlgHom.snd ℂ _ _) (fun a b => (E a b, smE ε (rreg ε) a b)) (Y + ((n : ℂ) - 1) / 2)
  simp only [AlgHom.fst_apply, AlgHom.snd_apply] at h1 h2
  have hp : (Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2), Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2)) ∈
      Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) := by
    rw [← h1, ← h2]
    exact hm
  exact ICD.transfer hgap hσ hD hV hc hVK hV0 hP hp _
    (fun v₀ hv₀ y hy => capelli_sigLam hgap hP hv₀ hcap Y y hy) x hx

end One

end ReciprocityTheory.ChartRestriction.DS
end
end

