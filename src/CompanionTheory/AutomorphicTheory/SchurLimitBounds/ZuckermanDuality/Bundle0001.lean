module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Bundle0001
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial
section
noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate

variable {k r : ℕ}

theorem one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)

theorem letters_pow_succ {d : ℕ} {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) : q ∈ Letters k r ^ (d + 1) := by
  rw [pow_succ]
  simpa using Submodule.mul_mem_mul h one_mem_letters

theorem letters_pow_mono {d e : ℕ} (hde : d ≤ e) {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) :
    q ∈ Letters k r ^ e := by
  induction hde with
  | refl => exact h
  | step _ ih => exact letters_pow_succ ih

theorem prod_mem_pow {ι : Type} (s : Finset ι) (q : ι → B.Mat k r → ℂ) (h : ∀ i ∈ s, q i ∈ Letters k r) :
    ∏ i ∈ s, q i ∈ Letters k r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.mem_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem det_mem_pow {m : ℕ} (Z : B.Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ a b, (fun g => Z g a b) ∈ Letters k r) : (fun g => (Z g).det) ∈ Letters k r ^ m := by
  have e : (fun g => (Z g).det) =
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ i, fun g => Z g (σ i) i := by
    funext g
    simp [Matrix.det_apply', Finset.prod_apply]
  rw [e]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
  simpa using prod_mem_pow Finset.univ (fun i g => Z g (σ i) i) fun i _ => h _ _

theorem hpk_herm : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem herm_letter (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨x, Formalism.QuantumDeterminants.Hpk k r *ᵥ y, Or.inl fun g _ => ?_⟩)
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, hpk_herm, Matrix.dotProduct_mulVec]

theorem herm_conj_letter (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => star (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨y, Formalism.QuantumDeterminants.Hpk k r *ᵥ x, Or.inr fun g hg => ?_⟩)
  have hu := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * g⁻¹ := by
    conv_rhs => rw [← hg']
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]
  simp only [Formalism.QuantumDeterminants.herm]
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.star_mulVec, Matrix.conjTranspose_mul, hpk_herm, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem dmin_mem (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    (fun g : B.Mat k r => ((Complex.normSq (Formalism.QuantumDeterminants.Dmin k r z z' g l) : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
  have hl : (l : ℕ) ≤ r + 1 := Nat.le_of_lt_succ l.isLt
  have h1 : (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) ∈ Letters k r ^ (r + 1) :=
    letters_pow_mono hl (det_mem_pow _ fun a b => herm_letter _ _)
  have h2 : (fun g : B.Mat k r => conj (Formalism.QuantumDeterminants.Dmin k r z z' g l)) ∈ Letters k r ^ (r + 1) := by
    have := det_mem_pow (k := k) (r := r) (fun g => ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix
      (Fin.castLE hl) (Fin.castLE hl))ᴴ) fun a b => herm_conj_letter _ _
    simp only [Matrix.det_conjTranspose] at this
    exact letters_pow_mono hl this
  have := Submodule.mul_mem_mul h1 h2
  rw [← pow_add, show r + 1 + (r + 1) = 2 * r + 2 by ring] at this
  convert this using 1
  funext g
  simp [Complex.mul_conj]

theorem generating_function_polynomial : GfPoly := by
  intro k r z z' p
  have h : (fun g : B.Mat k r => ((Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
    have := Submodule.sub_mem _ (dmin_mem z z' (Fin.last (r + 1)))
      (Submodule.smul_mem _ ((Formalism.QuantumDeterminants.Tz k r z * Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) (dmin_mem z z' ⟨r, by omega⟩))
    convert this using 1
    funext g
    simp [Formalism.QuantumDeterminants.Gf]
  rw [pow_mul]
  convert Submodule.pow_mem_pow _ h p using 1
  funext g
  simp

end CompanionTheory.LimBd.Main
end
end

-- bundled from CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Letter
section
noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}

theorem inv_eq_ct (hP : IsCayleyU k r ε P) : P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hP.2)

theorem inv_unitary (hP : IsCayleyU k r ε P) : P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  rw [inv_eq_ct hP]
  exact Unitary.star_mem hP.2

theorem back_K (hP : IsCayleyU k r ε P) {g : B.Mat k r} (hg : g ∈ Kset ε) :
    P⁻¹ * g * P ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  refine ⟨back_mem hP.1 ?_, Submonoid.mul_mem _ (Submonoid.mul_mem _ (inv_unitary hP) hg.1) hP.2⟩
  show gᴴ * Jm ε * g = Jm ε
  have h1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg.1
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem forth_K (hP : IsCayleyU k r ε P) {x : B.Mat k r}
    (hx : x ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) : P * x * P⁻¹ ∈ Kset ε := by
  have hu : P * x * P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hx.2) (inv_unitary hP)
  refine ⟨hu, ?_⟩
  have h1 : (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε := forth_mem hP.1 hx.1
  have h2 : (P * x * P⁻¹) * (P * x * P⁻¹)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  generalize P * x * P⁻¹ = g at h1 h2
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h1]
    _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
    _ = Jm ε * g := by rw [h2, Matrix.one_mul]

theorem kfin_iff {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (hP : IsCayleyU k r ε P)
    (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by
  constructor
  · rintro ⟨S, hS, hv, hst⟩
    exact ⟨S, hS, hv, fun g hg y hy => hst _ (back_K hP hg) y hy⟩
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun x hx y hy => ?_⟩
    have := hst _ (forth_K hP hx) y hy
    simpa only [back_forth hP.1] using this

theorem kfin_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) :
    IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_of_J (hP : IsCayleyU k r ε P) {μ : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {τ : B.Mat k r → (H →L[ℂ] H)} (hμ : IsHCParam μ) (hτ : IsDS ε μ τ)
    {v w : H} (hv : IsKFin ε τ v) (hw : IsKFin ε τ w) :
    IsCoef k r ε μ fun x => ⟪w, τ (P * x * P⁻¹) v⟫_ℂ := by
  have e : (fun g => (fun x => τ (P * x * P⁻¹)) (P⁻¹ * g * P)) = τ := funext fun g => by
    simp only [forth_back hP.1]
  refine ⟨H, _, _, inferInstance, fun x => τ (P * x * P⁻¹), v, w, hμ, ⟨P, hP, by rw [e]; exact hτ⟩, ?_, ?_,
    fun _ _ => rfl⟩
  · rw [kfin_iff hP, e]; exact hv
  · rw [kfin_iff hP, e]; exact hw

theorem mem_box_self {n : ℕ} (μ : Fin n → ℝ) : μ ∈ Box μ 1 := fun s => by simp

theorem mem_box_add {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) : μ + Pi.single s 1 ∈ Box μ 1 := fun t => by
  by_cases h : t = s
  · subst h; simp
  · simp [h]

theorem mem_box_sub {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) : μ - Pi.single s 1 ∈ Box μ 1 := fun t => by
  by_cases h : t = s
  · subst h; simp
  · simp [h]

theorem mem_spanBox_of_eq {μ : Fin (2 * r + k + 1) → ℝ} {φ ψ ψ' : B.Mat k r → ℂ} (hφ : IsCoef k r ε μ φ)
    (hψ' : ψ' ∈ SpanBox k r ε μ 1) (h : ∀ g ∈ B.GV k r, ψ g = ψ' g) : ψ ∈ SpanBox k r ε μ 1 := by
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, hw, -⟩ := hφ
  have h0 : ψ - ψ' ∈ SpanBox k r ε μ 1 := Submodule.subset_span ⟨μ, mem_box_self μ, H, i1, i2, i3, σ, 0, w, hμ, hσ,
    kfin_zero σ, hw, fun g hg => by simp [h g hg]⟩
  simpa using Submodule.add_mem _ h0 hψ'

theorem dot_transport (hP : IsCayleyU k r ε P) (a : B.Mat k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    star (P *ᵥ y) ⬝ᵥ ((P * a * P⁻¹) *ᵥ (P *ᵥ x)) = star y ⬝ᵥ (a *ᵥ x) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← inv_eq_ct hP]
  congr 2
  calc P⁻¹ * (P * a * P⁻¹ * P) = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = a := by rw [inv_mul_P hP.1, Matrix.one_mul, Matrix.mul_one]

theorem letter_recursion : LetterStep := by
  intro t hZ hZd k r ε μ h q φ hq hφ hg hlt
  rcases hq with rfl | ⟨x, y, hq⟩
  · rw [one_mul]
    exact Submodule.subset_span ⟨μ, mem_box_self μ, hφ⟩
  have hφ' := hφ
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, ⟨P, hP, hτ⟩, hv, hw, hφG⟩ := hφ'
  rw [kfin_iff hP] at hv hw
  rcases hq with hq | hq
  · obtain ⟨X⟩ := hZ _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanBox_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, mem_box_add μ (sI i),
        isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    simp only [back_forth hP.1, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
  · obtain ⟨X⟩ := hZd _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanBox_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, mem_box_sub μ (sI i),
        isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    have hi : (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    simp only [back_forth hP.1, hi, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]

theorem mul_mem_spanBox_of_gap (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) (hZ : ZuckT t) (hZd : ZuckDualT t) (k r : ℕ)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (d : ℕ) (q φ : B.Mat k r → ℂ)
    (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ) (hg : PI.ZuckTensor.GapAtLeast ε lam h)
    (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) : q * φ ∈ SpanBox k r ε lam (d : ℝ) := by
  induction d generalizing q with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨lam, fun s => by simp, hφ⟩)
  | succ d ih =>
    push_cast at hlt ⊢
    have step : Letters k r * SpanBox k r ε lam (d : ℝ) ≤ SpanBox k r ε lam ((d : ℝ) + 1) := by
      unfold Letters
      rw [SpanBox, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨μ, hμ, hb⟩, rfl⟩
      have hgμ : PI.ZuckTensor.GapAtLeast ε μ (h - 2 * d) := by
        intro i j hij
        have h1 := hg i j hij
        have h2 := abs_le.1 (hμ i)
        have h3 := abs_le.1 (hμ j)
        rcases abs_cases (lam i - lam j) with h4 | h4 <;> rcases abs_cases (μ i - μ j) with h5 | h5 <;> linarith
      have := letter_recursion t hZ hZd k r ε μ _ a b ha hb hgμ (by linarith)
      refine Submodule.span_mono ?_ this
      rintro ψ ⟨ν, hν, hψ⟩
      refine ⟨ν, fun s => ?_, hψ⟩
      have h2 := abs_le.1 (hμ s)
      have h3 := abs_le.1 (hν s)
      rw [abs_le]
      constructor <;> linarith
    rw [pow_succ'] at hq
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [mul_assoc]
      exact step (Submodule.mul_mem_mul ha (ih b hb (by linarith)))
    · rw [add_mul]
      exact Submodule.add_mem _ ha hb

theorem capelli_inequivalence : Inequiv := by
  intro hE k r ε ε' μ μ' H H' _ _ _ _ _ _ σ σ' hμ hμ' hσ hσ' hne ⟨U, hU⟩
  have hR := isURepOn_of_ds hσ
  have hσ₀ := hσ
  obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS, hst, -, ⟨v, hvS, hv0, -⟩, -⟩, -⟩ := hσ₀
  have hv : IsKFinHpk (k := k) (r := r) σ v := (kfin_iff hP σ v).2 ⟨S, hS, hvS, hst⟩
  have hv' : IsKFinHpk (k := k) (r := r) σ' (U v) := by
    obtain ⟨S₁, hS₁, hv₁, hst₁⟩ := hv
    refine ⟨S₁.map (U.toLinearEquiv : H →ₗ[ℂ] H'), inferInstance, ⟨v, hv₁, rfl⟩, ?_⟩
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst₁ g hg x hx, hU g hg.1 x⟩
  let φ : B.Mat k r → ℂ := fun g => ⟪v, σ g v⟫_ℂ
  have h1 : IsCoef k r ε μ φ := ⟨H, _, _, inferInstance, σ, v, v, hμ, hσ, hv, hv, fun _ _ => rfl⟩
  have h2 : IsCoef k r ε' μ' φ := ⟨H', _, _, inferInstance, σ', U v, U v, hμ', hσ', hv', hv', fun g hg => by
    rw [← hU g hg, U.inner_map_map]⟩
  have hone : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  have hφ1 : φ 1 • (1 : ℂ →L[ℂ] ℂ) ≠ 0 := by
    refine smul_ne_zero ?_ one_ne_zero
    simp [φ, hR.1.1, hv0]
  have key : ∀ Y : ℂ, ∏ s, (Y + (μ s : ℂ)) = ∏ s, (Y + (μ' s : ℂ)) := fun Y =>
    smul_left_injective ℂ hφ1 ((hE k r ε μ φ ℂ ℂ 1 h1 Y 1 hone).symm.trans (hE k r ε' μ' φ ℂ ℂ 1 h2 Y 1 hone))
  have sub : ∀ {a b : Fin (2 * r + k + 1) → ℝ}, (∀ Y : ℂ, ∏ s, (Y + (a s : ℂ)) = ∏ s, (Y + (b s : ℂ))) →
      Set.range a ⊆ Set.range b := by
    rintro a b hab _ ⟨s, rfl⟩
    have h0 : ∏ t, (-(a s : ℂ) + (b t : ℂ)) = 0 := by
      rw [← hab]
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by ring)
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨t, ?_⟩
    have : (b t : ℂ) = a s := by linear_combination ht
    exact_mod_cast this
  exact hne ((hμ.1.range_inj hμ'.1).1 (Set.Subset.antisymm (sub key) (sub fun Y => (key Y).symm)))

end CompanionTheory.LimBd.Main
end
end

