module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0002

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistenceStatement
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathCoef

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def LeftAt (ε : Fin n → Bool) (X : GMod n) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (i : ι) : Prop :=
  ∃ l : Fin n → Fin n → ι →₀ ℂ, ∀ (a b : Fin n) (u : X.V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
    c i (X.E a b u) g = ∑ p, ∑ q, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) p q *
      (l p q).sum fun i' r => r * c i' u g

theorem sum_mapDomain_mul {ι κ : Type} (f : κ → ι) (l : κ →₀ ℂ) (w : ι → ℂ) :
    ((l.mapDomain f).sum fun i r => r * w i) = l.sum fun q r => r * w (f q) :=
  Finsupp.sum_mapDomain_index (by simp) (by intros; ring)

theorem sum_weighted {ι κ : Type} [Fintype κ] (l : ι →₀ ℂ) (w : κ → ℂ) (f : κ → ι → ℂ) :
    ∑ k, w k * (l.sum fun x r => r * f k x) = l.sum fun x r => r * ∑ k, w k * f k x := by
  simp only [Finsupp.sum, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun k _ => by ring

theorem LeftAt.reindex {ε : Fin n → Bool} {X : GMod n} {ι κ : Type}
    {c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} {c' : κ → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (f : κ → ι) (hf : ∀ q, c (f q) = c' q) {i : ι} {k : κ} (hk : c i = c' k) (h : LeftAt ε X c' k) :
    LeftAt ε X c i := by
  obtain ⟨l, hl⟩ := h
  refine ⟨fun p q => (l p q).mapDomain f, fun a b u g hg => ?_⟩
  rw [hk, hl a b u g hg]
  simp only [sum_mapDomain_mul, hf]

theorem left_tens {ε : Fin n → Bool} (X : GMod n) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (h : ∀ i, LeftAt ε X c i) (q : ι × Fin n) :
    LeftAt ε (tens X) (fun q : ι × Fin n => tensCoef X (c q.1) q.2) q := by
  obtain ⟨p, j⟩ := q
  obtain ⟨l, hl⟩ := h p
  refine ⟨fun s t => (l s t).mapDomain (fun i' => (i', j)) +
    (if s = j then Finsupp.single (p, t) 1 else 0), fun a b (u : Fin n → X.V) g hg => ?_⟩
  have hgi : g⁻¹ * g = 1 := ReciprocityTheory.ChartRestriction.DS.Lap.Base.inv_mul_self_of_mem_indefiniteUnitary (ε := ε) hg
  have hMg : (g * Matrix.single a b (1 : ℂ) * g⁻¹) * g = g * Matrix.single a b (1 : ℂ) := by
    rw [Matrix.mul_assoc _ g⁻¹ g, hgi, Matrix.mul_one]
  generalize hM : (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) = M at hMg
  have hT : ∀ (i : ι) (m : Fin n), tensCoef X (c i) m u g = ∑ k, g m k * c i (u k) g := fun _ _ => rfl
  have e1 : ∀ s t, (((l s t).mapDomain (fun i' => (i', j)) +
      (if s = j then Finsupp.single (p, t) 1 else 0) : (ι × Fin n) →₀ ℂ).sum
        fun i' r => r * tensCoef X (c i'.1) i'.2 u g) =
      ((l s t).sum fun i' r => r * ∑ k, g j k * c i' (u k) g) +
        if s = j then ∑ k, g t k * c p (u k) g else 0 := by
    intro s t
    rw [Finsupp.sum_add_index' (by simp) (by intros; ring), sum_mapDomain_mul]
    simp only [hT]
    congr 1
    split_ifs
    · rw [Finsupp.sum_single_index (by simp), one_mul]
    · simp
  have eL : tensCoef X (c p) j ((tens X).E a b u) g =
      ∑ k, g j k * c p (X.E a b (u k)) g + g j a * c p (u b) g := by
    show ∑ k, g j k * c p (tensE X a b u k) g = _
    simp only [tensE_apply, map_add (f := _), Pi.add_apply, mul_add, sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have eA : ∑ k, g j k * c p (X.E a b (u k)) g =
      ∑ s, ∑ t, M s t * ((l s t).sum fun i' r => r * ∑ k, g j k * c i' (u k) g) := by
    simp only [hl a b _ g hg, hM, ← sum_weighted]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_congr rfl fun k _ => by ring
  have eB : g j a * c p (u b) g = ∑ s, ∑ t, M s t * (if s = j then ∑ k, g t k * c p (u k) g else 0) := by
    rw [Finset.sum_eq_single j (fun s _ hs => by simp [hs]) (by simp)]
    simp only [if_true]
    have : ∑ t, M j t * ∑ k, g t k * c p (u k) g = ∑ k, (M * g) j k * c p (u k) g := by
      simp only [mul_sum, Matrix.mul_apply, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ => by ring
    rw [this, hMg]
    rw [Finset.sum_eq_single b]
    · simp [Matrix.mul_apply, Matrix.single_apply]
    · intro k _ hk
      simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hk]
    · simp
  show tensCoef X (c p) j ((tens X).E a b u) g = ∑ s, ∑ t, M s t *
      (((l s t).mapDomain (fun i' => (i', j)) + (if s = j then Finsupp.single (p, t) 1 else 0) : (ι × Fin n) →₀ ℂ).sum
        fun i' r => r * tensCoef X (c i'.1) i'.2 u g)
  simp only [e1, mul_add, sum_add_distrib]
  rw [eL, eA, eB]

theorem left_step {ε : Fin n → Bool} (X : GMod n) (z : ℂ) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (h : ∀ i, LeftAt ε X c i) (q : ι × Fin n) :
    LeftAt ε (step X z) (fun q : ι × Fin n => stepCoef X z (c q.1) q.2) q := by
  obtain ⟨l, hl⟩ := left_tens X c h q
  exact ⟨l, fun a b u g hg => hl a b u.1 g hg⟩

theorem left_path {ε : Fin n → Bool} (ss : List (Fin n)) : ∀ (X : GMod n) (χ : Fin n → ℂ) {ι : Type}
    (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)), (∀ i, LeftAt ε X c i) →
    ∀ i : ι × List (Fin n), LeftAt ε (path X χ ss) (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ ss p.2) i := by
  induction ss with
  | nil =>
    intro X χ ι c hc i
    exact LeftAt.reindex (X := X) (c := fun p : ι × List (Fin n) => c p.1) (c' := c)
      (fun k => (k, [])) (fun _ => rfl) (k := i.1) rfl (hc i.1)
  | cons s ss ih =>
    intro X χ ι c hc i
    have h2 := ih (step X (χ s)) (χ + Pi.single s 1) (fun q : ι × Fin n => stepCoef X (χ s) (c q.1) q.2)
      (left_step X (χ s) c hc) ((i.1, i.2.headD s), i.2.tail)
    show LeftAt ε (path (step X (χ s)) (χ + Pi.single s 1) ss) (fun p : ι × List (Fin n) =>
      pathCoef (step X (χ s)) (stepCoef X (χ s) (c p.1) (p.2.headD s)) (χ + Pi.single s 1) ss p.2.tail) i
    exact LeftAt.reindex (fun q : (ι × Fin n) × List (Fin n) => (q.1.1, q.1.2 :: q.2)) (fun _ => rfl) rfl h2

section Base

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_deriv_skew (hσ : IsURepOn (UJset ε) σ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) {ξ ξ' u u' : H}
    (hξ : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ) ξ' 0)
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) : ⟪ξ, u'⟫_ℂ = ⟪ξ', u⟫_ℂ := by
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) ξ) hu
  have h2 := HasDerivAt.inner ℂ hξ (hasDerivAt_const (0 : ℝ) u)
  simp only [inner_zero_left, add_zero] at h1
  simp only [inner_zero_right, zero_add] at h2
  have e : (fun t : ℝ => ⟪ξ, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ, u⟫_ℂ := by
    funext t
    have hm := exp_smul_mem_UJset hY t
    have hm' := exp_smul_mem_UJset (SmDerA.inG_neg hY) t
    have hone : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • -Y) = 1 := by
      have hcomm : Commute ((t : ℂ) • Y) ((t : ℂ) • -Y) := by
        rw [smul_neg]; exact (Commute.refl _).neg_right
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, add_neg_cancel, NormedSpace.exp_zero]
    have hw : σ (NormedSpace.exp ((t : ℂ) • Y)) (σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ) = ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hm _ hm', hone, hσ.1.1]
      rfl
    calc ⟪ξ, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ
        = ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) (σ (NormedSpace.exp ((t : ℂ) • -Y)) ξ),
            σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ := by rw [hw]
      _ = _ := isometry_inner_eq (hσ.2.1 _ hm) _ _
  rw [e] at h1
  exact h1.unique h2

theorem deriv_transport (hσ : IsURepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) {u u' : H} (hd : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) u) u' 0) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g u)) (σ g u') 0 := by
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm := exp_smul_mem_UJset (inG_conj_unitary hg hX) t
  have hmX := exp_smul_mem_UJset hX t
  have hc : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) = g * NormedSpace.exp ((t : ℂ) • X) * g⁻¹ := by
    rw [← Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_smul, Matrix.smul_mul]
  show σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g u) = σ g (σ (NormedSpace.exp ((t : ℂ) • X)) u)
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hm g hg, hc, Matrix.mul_assoc _ g⁻¹ g,
    inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one, hσ.1.2 g hg _ hmX]
  rfl

theorem conj_entry {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) (p q : Fin n) :
    (starRingEnd ℂ) (Y p q) = -((if ε p = ε q then 1 else -1) * Y q p) := by
  have h := congrFun (congrFun hY q) p
  have hs : star (Y p q) = (starRingEnd ℂ) (Y p q) := rfl
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, hs] at h
  cases hp : ε p <;> cases hq : ε q <;> simp [hp, hq] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

theorem real_rule (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ u : D)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) :
    ⟪(ξ : H), σ g (∑ a, ∑ b, X a b • ((E a b u : D) : H))⟫_ℂ =
      ∑ p, ∑ q, (g * X * g⁻¹) p q * ((if ε p = ε q then 1 else -1) * ⟪((E q p ξ : D) : H), σ g u⟫_ℂ) := by
  have hY := inG_conj_unitary hg hX
  have h1 := hK.real (-(g * X * g⁻¹)) (SmDerA.inG_neg hY) ξ
  have h2 := deriv_transport hσ hg hX (hK.real X hX u)
  rw [inner_deriv_skew hσ hY h1 h2]
  simp only [sum_inner, inner_smul_left, Matrix.neg_apply, map_neg, conj_entry hY]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  have : (if ε q = ε p then (1 : ℂ) else -1) = if ε p = ε q then 1 else -1 := by simp only [eq_comm]
  rw [this]
  ring

theorem unit_rule (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ u : D)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (a b : Fin n) :
    ⟪(ξ : H), σ g ((E a b u : D) : H)⟫_ℂ =
      ∑ p, ∑ q, (g * Matrix.single a b (1 : ℂ) * g⁻¹) p q *
        ((if ε p = ε q then 1 else -1) * ⟪((E q p ξ : D) : H), σ g u⟫_ℂ) := by
  obtain ⟨X₁, X₂, h₁, h₂, hdec⟩ : ∃ X₁ X₂ : Matrix (Fin n) (Fin n) ℂ, inG ε X₁ ∧ inG ε X₂ ∧
      Matrix.single a b (1 : ℂ) = X₁ + Complex.I • X₂ :=
    ⟨_, _, SmDerA.inG_cpart1 ε _, SmDerA.inG_cpart2 ε _, SmDerA.cpart_decomp ε _⟩
  have hz : ∀ c d, X₁ c d + Complex.I * X₂ c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    rw [hdec]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hv : ((E a b u : D) : H) = (∑ c, ∑ d, X₁ c d • ((E c d u : D) : H)) +
      Complex.I • ∑ c, ∑ d, X₂ c d • ((E c d u : D) : H) := by
    calc ((E a b u : D) : H) = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d u : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]
      _ = ∑ c, ∑ d, (X₁ c d + Complex.I * X₂ c d) • ((E c d u : D) : H) := by simp only [hz]
      _ = _ := by simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
  have hM : g * Matrix.single a b (1 : ℂ) * g⁻¹ = g * X₁ * g⁻¹ + Complex.I • (g * X₂ * g⁻¹) := by
    rw [hdec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hv, map_add (f := _), map_smul, inner_add_right, inner_smul_right, real_rule hσ hK ξ u hg h₁,
    real_rule hσ hK ξ u hg h₂, hM]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring

theorem left_base (hσ : IsURepOn (UJset ε) σ) (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (ξ : D) :
    LeftAt ε ⟨D, E, hK.gl⟩ (fun ξ : D => baseCoef σ D (ξ : H)) ξ := by
  refine ⟨fun p q => Finsupp.single (E q p ξ) (if ε p = ε q then 1 else -1), fun a b u g hg => ?_⟩
  have h := unit_rule hσ hK ξ u hg a b
  simp only [Finsupp.sum_single_index, zero_mul]
  exact h

end Base

theorem leftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i
  exact left_path ss ⟨D, E, hK.gl⟩ χ (fun ξ : D => baseCoef σ D (ξ : H)) (fun ξ => left_base hσ hK ξ) i

end GlobalTheory.CompanionTheory.PathCoef
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeFirst
section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OdeRoots

theorem energy_pointwise (z x y : ℂ) (s e : ℝ) (hz : z.re < s) (he : 0 ≤ e) :
    2 * (inner ℝ x (z * x + y)) * e + ‖x‖ ^ 2 * (e * (-2 * s)) ≤
      -(s - z.re) * (‖x‖ ^ 2 * e) + (1 / (s - z.re)) * (‖y‖ ^ 2 * e) := by
  have ha : 0 < s - z.re := sub_pos.2 hz
  have h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y := by
    rw [inner_add_right]
    congr 1
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [h1]
  set a := s - z.re with hadef
  set p := ‖x‖
  set q := ‖y‖
  have hs : s = a + z.re := by rw [hadef]; ring
  have h3 : 0 ≤ (a * p - q) ^ 2 / a := by positivity
  have h4 : (a * p - q) ^ 2 / a = a * p ^ 2 - 2 * (p * q) + (1 / a) * q ^ 2 := by
    field_simp
    ring
  have h5 : 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) ≤
      -a * p ^ 2 + (1 / a) * q ^ 2 := by
    rw [hs]
    nlinarith
  have := mul_le_mul_of_nonneg_right h5 he
  nlinarith

theorem odeA : CompanionTheory.RgExh.Dec.N.OdeA := by
  intro z s hz f g hf hg hgi
  have ha : 0 < s - z.re := sub_pos.2 hz
  set a := s - z.re with hadef

  let ft : ℝ → ℂ := fun t => f (max t 0)
  have hfon : ContinuousOn f (Ici 0) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hft : Continuous ft :=
    hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))
  have hfe : ∀ t, 0 ≤ t → ft t = f t := fun t ht => by simp [ft, max_eq_left ht]
  let E : ℝ → ℝ := fun t => Real.exp (-2 * s * t)
  have hE : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 ≤ E t := fun t => (Real.exp_pos _).le
  let U : ℝ → ℝ := fun t => ‖ft t‖ ^ 2 * E t
  let V : ℝ → ℝ := fun t => ‖g t‖ ^ 2 * E t
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  have hUn : ∀ t, 0 ≤ U t := fun t => mul_nonneg (by positivity) (hEpos t)
  have hVn : ∀ t, 0 ≤ V t := fun t => mul_nonneg (by positivity) (hEpos t)
  let D : ℝ → ℝ := fun t =>
    2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))
  have hD : Continuous D := by
    have : Continuous fun t => inner ℝ (ft t) (z * ft t + g t) :=
      Continuous.inner hft (by fun_prop)
    fun_prop
  have hDle : ∀ t, D t ≤ -a * U t + (1 / a) * V t := fun t =>
    energy_pointwise z (ft t) (g t) s (E t) hz (hEpos t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t := by
    intro t ht
    have h1 := (hf t ht).norm_sq
    have h2 : HasDerivAt E (E t * (-2 * s)) t := by
      have := ((hasDerivAt_id t).const_mul (-2 * s)).exp
      simpa [E] using this
    have e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s)) := by
      simp only [D, hfe t ht]
    rw [e]
    exact h1.mul h2

  have hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hgi
    refine lintegral_congr fun t => ?_
    simp only [V, E]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hVint : IntegrableOn V (Ioi 0) :=
    ⟨hV.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩
  set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC
  have hVle : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, V t ≤ C := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hVint (ae_of_all _ hVn) (ae_of_all _ Ioc_subset_Ioi_self)
  have hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (U 0 + (1 / a) * C) / a := by
    intro T hT
    have hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_)
        (hD.intervalIntegrable _ _)
      rw [uIcc_of_le hT] at ht
      exact hderiv t ht.1
    have hmono : ∫ t in (0 : ℝ)..T, D t ≤ ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) :=
      intervalIntegral.integral_mono_on hT (hD.intervalIntegrable _ _)
        (((continuous_const.mul hU).add (continuous_const.mul hV)).intervalIntegrable _ _)
        (fun t _ => hDle t)
    have hsplit : ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) =
        -a * (∫ t in (0 : ℝ)..T, U t) + (1 / a) * ∫ t in (0 : ℝ)..T, V t := by
      have c1 : IntervalIntegrable (fun t => -a * U t) volume 0 T :=
        (continuous_const.mul hU).intervalIntegrable _ _
      have c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T :=
        (continuous_const.mul hV).intervalIntegrable _ _
      rw [intervalIntegral.integral_add c1 c2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hT0 : 0 ≤ ‖f T‖ ^ 2 * E T := mul_nonneg (by positivity) (hEpos T)
    have hU0 : U 0 = ‖f 0‖ ^ 2 * E 0 := by simp only [U, hfe 0 le_rfl]
    have hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C :=
      mul_le_mul_of_nonneg_left (hVle T hT) (by positivity)
    rw [le_div_iff₀ ha]
    rw [hI, hsplit] at hmono
    nlinarith
  have hUint : IntegrableOn U (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((U 0 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T)
      (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hUn _)] using hbound T hT
  have hfin := hUint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [U, E, hfe t ht0]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm]

end GlobalTheory.CompanionTheory.OdeRoots
end
end

