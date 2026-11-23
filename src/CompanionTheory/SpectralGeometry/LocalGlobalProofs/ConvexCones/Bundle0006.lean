module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevel
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan


open Matrix in
theorem posDef_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ε * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hx
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x) := by
    apply Continuous.dotProduct continuous_id
    exact Continuous.matrix_mulVec continuous_const continuous_id
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere _ _
  have key : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, ε ≤ x ⬝ᵥ (A *ᵥ x) := by
    rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos x0 ?_, fun x hx => hmin hx⟩
      rintro rfl
      simp at hx0
  obtain ⟨ε, hε, hb⟩ := key
  refine ⟨ε, hε, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hb _ hu
  have e : (‖x‖⁻¹ • x) ⬝ᵥ (A *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [sq, mul_assoc]
  rw [e] at h1
  have h2 : 0 < ‖x‖ ^ 2 := by positivity
  calc ε * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x))) * ‖x‖ ^ 2 := by gcongr
    _ = x ⬝ᵥ (A *ᵥ x) := by field_simp


open Matrix in
theorem sublevel_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) →
    ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  intro X _ _ _ β hsym hpos c
  obtain ⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ X) :=
    ⟨_, ⟨Module.finBasis ℤ X⟩⟩
  obtain ⟨b⟩ := b
  let Q : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => ((β (b i) (b j) : ℤ) : ℚ)
  have hQs : Q.IsSymm := by
    ext i j
    simp [Q, hsym (b i) (b j)]
  have hval : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i)
      = ∑ i, ∑ j, β (b i) (b j) * v i * v j := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hne : ∀ v : Fin n → ℤ, v ≠ 0 → (∑ i, v i • b i) ≠ 0 := by
    intro v hv h0
    exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h0))
  have hQpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := by
    intro v hv
    have h := hpos _ (hne v hv)
    rw [hval] at h
    have h' : (0 : ℚ) < ((∑ i, ∑ j, β (b i) (b j) * v i * v j : ℤ) : ℚ) := by exact_mod_cast h
    simpa [Q] using h'
  have hA := GlobalTheory.CompanionTheory.Ar.Fan.posDef_of_int_pos n Q hQs hQpos
  obtain ⟨ε, hε, hco⟩ := posDef_coercive _ hA
  obtain ⟨N, hN⟩ := exists_nat_ge ((c : ℝ) / ε)
  have hbound : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i) ≤ c →
      ∀ i, |v i| ≤ (N + 1 : ℤ) := by
    intro v hv i
    have h1 := hco (fun i => (v i : ℝ))
    have h2 : (fun i => (v i : ℝ)) ⬝ᵥ ((Q.map (Rat.cast : ℚ → ℝ)) *ᵥ (fun i => (v i : ℝ)))
        = ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) := by
      rw [hval]
      simp only [dotProduct, mulVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Q]
      ring
    rw [h2] at h1
    have h3 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) ≤ c := by exact_mod_cast hv
    have h4 : ‖(fun i => (v i : ℝ))‖ ^ 2 ≤ N := by
      refine le_trans ?_ hN
      rw [le_div_iff₀ hε]
      linarith
    have h5 : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖ := by
      simpa using norm_le_pi_norm (fun i => (v i : ℝ)) i
    have h6 : |(v i : ℝ)| ≤ (N : ℝ) + 1 := by
      nlinarith [sq_nonneg (‖(fun i => (v i : ℝ))‖ - 1), norm_nonneg (fun i => (v i : ℝ))]
    exact_mod_cast h6
  have hfin : (Set.Icc (fun _ : Fin n => -(N + 1 : ℤ)) (fun _ => (N + 1 : ℤ))).Finite :=
    Set.finite_Icc _ _
  refine (hfin.image fun v => ∑ i, v i • b i).subset ?_
  intro y hy
  have hy' : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
  refine ⟨fun i => b.repr y i, ?_, hy'.symm⟩
  have hb2 := hbound (fun i => b.repr y i) (by rw [← hy']; exact hy)
  exact ⟨fun i => (abs_le.1 (hb2 i)).1, fun i => (abs_le.1 (hb2 i)).2⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.DomZ

open Matrix

def quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

theorem quadOf_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadOf A x = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [quadOf, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem continuous_quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadOf A) := by
  unfold quadOf
  fun_prop

theorem quadOf_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    quadOf A (t • x) = t ^ 2 * quadOf A x := by
  simp only [quadOf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_nat_quadOf_le {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ) : ∃ C : ℕ, ∀ x, quadOf R x ≤ C * quadOf P x := by
  have hpos : ∀ x, x ≠ 0 → 0 < quadOf P x := fun x hx => by
    rw [quadOf_eq]
    exact hP.dotProduct_mulVec_pos hx
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne : ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1, u ≠ 0 := fun u hu h => by
    simp [h] at hu
  have hc : ContinuousOn (fun u => quadOf R u / quadOf P u) (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (continuous_quadOf R).continuousOn.div (continuous_quadOf P).continuousOn
      fun u hu => (hpos u (hne u hu)).ne'
  obtain ⟨K, hK⟩ := hS.bddAbove_image hc
  refine ⟨⌈K⌉₊, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp [quadOf]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  obtain ⟨u, hu⟩ : ∃ u, u = ‖x‖⁻¹ • x := ⟨_, rfl⟩
  have hum : u ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [hu, norm_smul, hn]
  have h1 : quadOf R u / quadOf P u ≤ K := hK ⟨u, hum, rfl⟩
  have hpu := hpos u (hne u hum)
  have h2 : quadOf R u ≤ ⌈K⌉₊ * quadOf P u := by
    rw [div_le_iff₀ hpu] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hpu.le)
  have hxu : x = ‖x‖ • u := by simp [hu, smul_smul, hn]
  have eR : ∀ A : Matrix (Fin n) (Fin n) ℝ, quadOf A x = ‖x‖ ^ 2 * quadOf A u := fun A => by
    rw [← quadOf_smul, ← hxu]
  rw [eR, eR]
  calc ‖x‖ ^ 2 * quadOf R u ≤ ‖x‖ ^ 2 * (⌈K⌉₊ * quadOf P u) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem sum_mul_nonneg {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * G i j := by
  have h := (hA.hadamard hG).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply] using h

theorem posSemidef_of_int_nonneg {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hs : G.IsHermitian)
    (h : ∀ v : Fin n → ℤ, 0 ≤ quadOf G fun i => (v i : ℝ)) : G.PosSemidef := by
  have hrat : ∀ w : Fin n → ℚ, 0 ≤ quadOf G fun i => (w i : ℝ) := fun w => by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
    choose v hv using hc
    have hc0 : (((c : ℤ) : ℝ)) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.ne_zero c.2
    have hv' : ∀ i, (v i : ℚ) = (c : ℤ) * w i := fun i => by
      simpa [Algebra.smul_def] using hv i
    have e : (fun i => (v i : ℝ)) = ((c : ℤ) : ℝ) • fun i => (w i : ℝ) := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hv' i)
      simpa using this
    have h1 := h v
    rw [e, quadOf_smul] at h1
    have h2 : 0 < (((c : ℤ) : ℝ)) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right h1 h2
  have hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ quadOf G x} := isClosed_le continuous_const (continuous_quadOf G)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs fun x => ?_
  rw [← quadOf_eq]
  exact hdense.induction_on (p := fun x => 0 ≤ quadOf G x) x hcl hrat

section Forms

variable {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X)

def elemForm (i j : Fin n) : LinearMap.BilinForm ℤ X :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)

theorem elemForm_comm (i j : Fin n) : elemForm b i j = elemForm b j i := add_comm _ _

theorem two_smul_eq {β : LinearMap.BilinForm ℤ X} (hβ : ∀ y z, β y z = β z y) :
    (2 : ℤ) • β = ∑ i, ∑ j, β (b i) (b j) • elemForm b i j := by
  refine b.ext fun k => b.ext fun l => ?_
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  simp [elemForm, Finsupp.single_apply, mul_add, Finset.sum_add_distrib]
  rw [hβ (b l) (b k)]
  ring

theorem two_mul_map (L : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    (hβ : ∀ y z, β y z = β z y) : 2 * L β = ∑ i, ∑ j, L (elemForm b i j) * β (b i) (b j) := by
  have h := congrArg L (two_smul_eq b hβ)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end Forms

end GlobalTheory.CompanionTheory.Ar.Fan.DomZ

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix DomZ

theorem dominates_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := by
  intro ℓ m hℓ
  let Q : Matrix (Fin n) (Fin n) ℚ := fun i j => (ℓ (elemForm b i j) : ℚ)
  let P : Matrix (Fin n) (Fin n) ℝ := Q.map (Rat.cast : ℚ → ℝ)
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (m (elemForm b i j) : ℝ)
  have hQs : Q.IsSymm := by
    ext i j
    show (ℓ (elemForm b j i) : ℚ) = (ℓ (elemForm b i j) : ℚ)
    rw [elemForm_comm b j i]
  have hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := fun v hv => by
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ i, l (b i) = v i := fun i => by simp [l, Finsupp.single_apply]
    have hsym : ∀ y z, GlobalTheory.PolFan.sqForm l y z = GlobalTheory.PolFan.sqForm l z y := fun y z => by
      simp [mul_comm]
    have hne : GlobalTheory.PolFan.sqForm l ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
      have h1 := congrArg (fun β : LinearMap.BilinForm ℤ X => β (b k) (b k)) h0
      simp only [GlobalTheory.PolFan.sqForm_apply, hl, LinearMap.zero_apply, mul_self_eq_zero] at h1
      exact hk h1
    have h1 := hℓ (GlobalTheory.PolFan.sqForm l) (mem_balForms_int.2 hsym)
      (fun y => by simpa using mul_self_nonneg (l y)) hne
    have h2 := two_mul_map b ℓ hsym
    simp only [GlobalTheory.PolFan.sqForm_apply, hl] at h2
    have h3 : (0 : ℤ) < ∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) := by
      rw [← h2]
      omega
    have h4 : ((∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) : ℤ) : ℚ) = ∑ i, ∑ j, Q i j * v i * v j := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Q]
      ring
    rw [← h4]
    exact_mod_cast h3
  have hP : P.PosDef := posDef_of_int_pos n Q hQs hQ
  obtain ⟨C, hC⟩ := exists_nat_quadOf_le hP R
  refine ⟨C, fun β hβ hp => ?_⟩
  have hβs := mem_balForms_int.1 hβ
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => (β (b i) (b j) : ℝ)
  have hG : G.PosSemidef := by
    refine posSemidef_of_int_nonneg ?_ fun v => ?_
    · ext i j
      rw [Matrix.conjTranspose_apply, star_trivial]
      show ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
      rw [hβs]
    · have h1 := hp (∑ i, v i • b i)
      have h2 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) = quadOf G fun i => (v i : ℝ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, quadOf, G]
        push_cast
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [← h2]
      exact_mod_cast h1
  have hRs : R.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    show (m (elemForm b j i) : ℝ) = (m (elemForm b i j) : ℝ)
    rw [elemForm_comm b j i]
  have hA : ((C : ℝ) • P - R).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · exact (hP.1.smul (by simp)).sub hRs
    · rw [← quadOf_eq]
      have e : quadOf ((C : ℝ) • P - R) x = C * quadOf P x - quadOf R x := by
        simp only [quadOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      linarith [hC x]
  have h1 := sum_mul_nonneg hA hG
  have hPij : ∀ i j, P i j = (ℓ (elemForm b i j) : ℝ) := fun i j => by
    show (((ℓ (elemForm b i j) : ℤ) : ℚ) : ℝ) = _
    simp
  have e1 : ∑ i, ∑ j, P i j * G i j = ((2 * ℓ β : ℤ) : ℝ) := by
    rw [two_mul_map b ℓ hβs]
    push_cast
    simp only [hPij, G]
  have e2 : ∑ i, ∑ j, R i j * G i j = ((2 * m β : ℤ) : ℝ) := by
    rw [two_mul_map b m hβs]
    push_cast
    simp only [R, G]
  have e3 : ∑ i, ∑ j, ((C : ℝ) • P - R) i j * G i j
      = C * ∑ i, ∑ j, P i j * G i j - ∑ i, ∑ j, R i j * G i j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3, e1, e2] at h1
  have h2 : (2 * m β : ℝ) ≤ C * (2 * ℓ β) := by
    push_cast at h1
    linarith
  have h3 : (m β : ℝ) ≤ C * ℓ β := by linarith
  exact_mod_cast h3

theorem dominates_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X],
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := fun X _ _ _ => dominates_of_basis (Module.finBasis ℤ X)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLift
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_sum_smul {X : Type} [AddCommGroup X] {m : ℕ} (B : Fin m → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c : Fin m → ℝ) (y : X)
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ i, IsMin2 (B i) y) : IsMin2 (∑ i, c i • B i) y := by
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i x) (hc i)

def sumDiag {X ι : Type} [AddCommGroup X] [Fintype ι] (g : ℕ) (p : ι → X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := 2 ^ g * ∑ y, β (p y) (p y)
  map_add' β γ := by
    simp only [LinearMap.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' k β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem isCell_vorFun_of_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ)
    (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) →
    (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ →
    IsCell bar (vorFun O g) γ := by
  intro O _ _ _ _ bar g X _ _ _ _ n r a hr ha m γ hbal hpsd hcon hsub
  have hval := (vorFun_value_le O bar g X n r a hr ha).2
  have hreal : ∀ (β : LinearMap.BilinForm ℤ X) , (∀ y, 0 ≤ β y y) → ∀ y, 0 ≤ toReal β y y := fun β hβ y => by
    simpa [toReal_apply] using hβ y
  have hℓ : ∀ β : LinearMap.BilinForm ℤ X, ((sumDiag g (fun y => r (a y)) β : ℤ) : ℝ) =
      2 ^ g * ∑ y, toReal β (r (a y)) (r (a y)) := fun β => by
    simp [sumDiag, toReal_apply]
  have hgen : ∀ i, (2 : ℝ) ^ n * (vorFun O g).evalZ (γ i) = sumDiag g (fun y => r (a y)) (γ i) := fun i => by
    rw [hℓ, ← evalR_toReal]
    exact (hval _ (hreal _ (hpsd i))).2.2 (hcon i).2
  refine ⟨hbal, hpsd, (linearOn_iff _ γ).2 fun c hc => ?_, 2 ^ n, sumDiag g (fun y => r (a y)), by positivity, ?_, ?_, ?_⟩
  · have hS : ∀ y, 0 ≤ (∑ i, c i • toReal (γ i)) y y := fun y => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hreal _ (hpsd i) y)
    have h1 := (hval _ hS).2.2 fun y => isMin2_sum_smul _ c _ hc fun i => (hcon i).2 y
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine mul_left_cancel₀ hp (h1.trans ?_)
    have h2 : ∀ i, (2 : ℝ) ^ g * ∑ y, toReal (γ i) (r (a y)) (r (a y)) = 2 ^ n * (vorFun O g).evalZ (γ i) := fun i => by
      rw [hgen, hℓ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, h2, mul_left_comm]
  · intro i
    push_cast
    exact (hgen i).symm
  · intro β _ hβ
    have h := (hval _ (hreal β hβ)).1
    rw [evalR_toReal] at h
    rw [hℓ]
    push_cast
    exact h
  · intro β hb hβ he
    have hmin : ∀ y, IsMin2 (toReal β) (r (a y)) := by
      refine (hval _ (hreal β hβ)).2.1 ?_
      rw [evalR_toReal, ← hℓ]
      exact_mod_cast he
    have hpc : toReal β ∈ psdCone (bar := bar) (X := X) := by
      simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hb]) (by simp [hβ]) (by simp)
    exact exists_nat_comb_of_toReal_mem_rcone X m γ β (hsub ⟨hpc, hmin⟩)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rational_cone_of_perturbation : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | exact GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMemStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_add_mem : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | exact GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjectionStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_descends_along_surjection : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), Function.Surjective r → B ∈ psdCone (bar := bar) (X := X) → (∀ y, r y = 0 → B y y = 0) → ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupportStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_exists_maximal_support : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)), K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) → ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal

theorem smoothEnd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ :=
  fun _ _ _ _ _ _ _ _ _ _ hD hPF hSL hM => GlobalTheory.PolFan.SmoothEnd.isPolFan_of_maxMult_le_one hD hPF hSL hM

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal
end

