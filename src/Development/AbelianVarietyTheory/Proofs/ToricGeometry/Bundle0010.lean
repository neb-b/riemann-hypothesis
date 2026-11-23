module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesTangentVectors
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaTangent

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dense_ne_zero [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f)
    (h0 : f ≠ 0) : Dense {x | f x ≠ 0} := by
  intro x
  rw [mem_closure_iff_frequently]
  by_contra h
  rw [Filter.not_frequently] at h
  apply h0
  have h1 : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := h.mono fun y hy => by simpa using hy
  have := GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hf.differentiableOn
    (differentiableOn_const (0 : ℂ)) (Set.mem_univ x) h1
  funext y
  exact this (Set.mem_univ y)

theorem exists_entire_quotient {θ D : E → ℂ} (hU : Dense {x | θ x ≠ 0})
    (h : ∀ a, ∃ φ : E → ℂ, ∀ᶠ x in 𝓝 a, DifferentiableAt ℂ φ x ∧ D x = φ x * θ x) :
    ∃ ψ : E → ℂ, Differentiable ℂ ψ ∧ ∀ x, D x = ψ x * θ x := by
  choose φ hφ using h
  refine ⟨fun a => φ a a, fun a => ?_, fun x => (hφ x).self_of_nhds.2⟩
  have key : (fun x => φ x x) =ᶠ[𝓝 a] φ a := by
    filter_upwards [(hφ a).eventually_nhds] with x hx
    have hfr : ∃ᶠ y in 𝓝 x, y ∈ {x | θ x ≠ 0} := mem_closure_iff_frequently.mp (hU x)
    have hfr2 : ∃ᶠ y in 𝓝 x, φ x y = φ a y := by
      refine (hfr.and_eventually (hx.and (hφ x))).mono ?_
      rintro y ⟨hy, ⟨-, h1⟩, -, h2⟩
      exact mul_right_cancel₀ hy (h2.symm.trans h1)
    exact tendsto_nhds_unique_of_frequently_eq (hφ x).self_of_nhds.1.continuousAt
      hx.self_of_nhds.1.continuousAt hfr2
  exact (hφ a).self_of_nhds.1.congr_of_eventuallyEq key

theorem exists_unit_of_three_term [FiniteDimensional ℂ E] {θ : E → ℂ} (hθ : Differentiable ℂ θ)
    (h0 : θ ≠ 0) (ξ s : E) (γ : ℂ) (m : ℕ)
    (hrel : ∀ a b : E,
      fderiv ℂ θ a ξ * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * (((m : ℂ) + 1) * θ b ^ m * fderiv ℂ θ b ξ) * θ (s - a - ((m : ℂ) + 1) • b)
        + θ a * θ b ^ (m + 1) * fderiv ℂ θ (s - a - ((m : ℂ) + 1) • b) ξ
      = γ * (θ a * θ b ^ (m + 1) * θ (s - a - ((m : ℂ) + 1) • b))) (t : ℂ) :
    ∃ h : E → ℂ, Differentiable ℂ h ∧ (∀ y, h y ≠ 0) ∧ ∀ y, θ (y + t • ξ) = h y * θ y := by
  set k : ℂ := (m : ℂ) + 1 with hk
  have hk0 : k ≠ 0 := Nat.cast_add_one_ne_zero m
  set D : E → ℂ := fun x => fderiv ℂ θ x ξ with hD
  have hDd : Differentiable ℂ D := by
    rw [← differentiableOn_univ]
    exact GlobalTheory.SCV.differentiableOn_fderiv_apply isOpen_univ hθ.differentiableOn ξ
  have hU := dense_ne_zero hθ h0
  have hUo : IsOpen {x | θ x ≠ 0} := isOpen_ne_fun hθ.continuous continuous_const
  obtain ⟨x₀, hx₀⟩ : ∃ x, θ x ≠ 0 := hU.nonempty
  have hU' : ∀ (p : E) (c : ℂ), c ≠ 0 → Dense {x | θ (p - c • x) ≠ 0} := by
    intro p c hc
    refine dense_ne_zero (f := fun x => θ (p - c • x)) (hθ.comp (by fun_prop)) fun h => hx₀ ?_
    have := congrFun h (c⁻¹ • (p - x₀))
    simpa [smul_smul, hc] using this
  obtain ⟨ψ, hψ, hDψ⟩ := exists_entire_quotient (D := D) hU (by
    intro a
    obtain ⟨b, hb1, hb2⟩ := ((hU' (s - a) k hk0).inter_of_isOpen_right hU hUo).nonempty
    simp only [Set.mem_setOf_eq] at hb1 hb2
    refine ⟨fun x => γ - k * D b / θ b - D (s - x - k • b) / θ (s - x - k • b), ?_⟩
    have hc : ContinuousAt (fun x => θ (s - x - k • b)) a :=
      (hθ.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [hc.eventually_ne hb1] with x hx
    refine ⟨?_, ?_⟩
    · have d1 : DifferentiableAt ℂ (fun x => D (s - x - k • b)) x :=
        (hDd.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      have d2 : DifferentiableAt ℂ (fun x => θ (s - x - k • b)) x :=
        (hθ.comp (f := fun x => s - x - k • b) (by fun_prop)) x
      simp only [div_eq_mul_inv]
      exact (differentiableAt_const _).sub (d1.mul (d2.inv hx))
    · have := hrel x b
      have hp : θ b ^ m ≠ 0 := pow_ne_zero _ hb2
      field_simp
      apply mul_left_cancel₀ hp
      simp only [hD]
      linear_combination this)
  have hψc := hψ.continuous
  have hfun : ∀ a b : E, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
    have h1 : ∀ b, θ b ≠ 0 → ∀ a, ψ a + k * ψ b + ψ (s - a - k • b) = γ := by
      intro b hb a
      have hd := (hU' (s - k • b) 1 one_ne_zero).inter_of_isOpen_right hU hUo
      refine congrFun (Continuous.ext_on hd
        (f := fun a => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const ?_) a
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_setOf_eq, one_smul] at hx1 hx2
      rw [sub_right_comm] at hx1
      have := hrel x b
      have e1 := hDψ x
      have e2 := hDψ b
      have e3 := hDψ (s - x - k • b)
      simp only [hD] at e1 e2 e3
      rw [e1, e2, e3] at this
      apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hx2 (pow_ne_zero (m + 1) hb)) hx1)
      linear_combination this
    intro a b
    exact congrFun (Continuous.ext_on hU
        (f := fun b => ψ a + k * ψ b + ψ (s - a - k • b)) (g := fun _ => γ)
        (by fun_prop) continuous_const fun x hx => h1 x hx a) b
  have hdiff : ∀ y w : E, ψ (y + w) = ψ y + (ψ w - ψ 0) := by
    intro y w
    have e1 := hfun (y + w) (k⁻¹ • (s - y - w))
    have e2 := hfun y (k⁻¹ • (s - y - w))
    rw [smul_inv_smul₀ hk0] at e1 e2
    rw [show s - (y + w) - (s - y - w) = 0 by abel] at e1
    rw [show s - y - (s - y - w) = w by abel] at e2
    linear_combination e1 - e2
  have hκ : Differentiable ℂ (fun r : ℂ => ψ (r • ξ) - ψ 0) := by fun_prop
  obtain ⟨K, hK⟩ := hκ.isExactOn_univ
  refine ⟨fun y => Complex.exp (t * ψ y + (K t - K 0)), by fun_prop,
    fun y => Complex.exp_ne_zero _, fun y => ?_⟩
  have hF : ∀ r : ℂ, HasDerivAt
      (fun r : ℂ => θ (y + r • ξ) * Complex.exp (-(r * ψ y + K r))) 0 r := by
    intro r
    have hl : HasDerivAt (fun r : ℂ => y + r • ξ) ξ r := by
      simpa using ((hasDerivAt_id r).smul_const ξ).const_add y
    have h1 : HasDerivAt (fun r : ℂ => θ (y + r • ξ)) (D (y + r • ξ)) r :=
      (hθ (y + r • ξ)).hasFDerivAt.comp_hasDerivAt r hl
    have h2 : HasDerivAt (fun r : ℂ => -(r * ψ y + K r)) (-(1 * ψ y + (ψ (r • ξ) - ψ 0))) r :=
      (((hasDerivAt_id r).mul_const (ψ y)).add (hK r (Set.mem_univ r))).neg
    refine (h1.mul h2.cexp).congr_deriv ?_
    rw [hDψ, hdiff]
    ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) t 0
  simp only [zero_smul, add_zero, zero_mul, zero_add] at hc
  have e : θ (y + t • ξ) = (θ (y + t • ξ) * Complex.exp (-(t * ψ y + K t)))
      * Complex.exp (t * ψ y + K t) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [e, hc, mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

end General

theorem level_three_separates_tangent_vectors :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) := by
  intro H1 H2 H3 g τ hτ N hN z ξ γ hf
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
  obtain ⟨⟨hθ, hlaw⟩, h0⟩ := H1 g τ hτ
  have hper := H2 g τ hτ
  have hdisc := (H3 g τ hτ).1
  set θ : (Fin g → ℂ) → ℂ := fun z => theta 0 0 z τ with hθdef
  have hmem : ∀ t : ℂ, t • ξ ∈ periodLattice τ := by
    intro t
    obtain ⟨h, h1, h2, h3⟩ := exists_unit_of_three_term hθ h0 ξ (((m : ℂ) + 3) • z) γ m (by
      intro a b
      set c := ((m : ℂ) + 3) • z - a - ((m : ℂ) + 1) • b with hc
      have hd : ∀ p : Fin g → ℂ, HasFDerivAt (fun x => θ (x + (p - z))) (fderiv ℂ θ p) z := by
        intro p
        have := (hθ p).hasFDerivAt
        rw [show p = z + (p - z) by abel] at this
        rw [← hasFDerivAt_comp_add_right] at this
        simpa using this
      have hdd : ∀ p : Fin g → ℂ, Differentiable ℂ (fun x => θ (x + (p - z))) := fun p =>
        hθ.comp (by fun_prop)
      have key := hf (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
        ⟨((hdd a).mul ((hdd b).pow _)).mul (hdd c), ?_⟩
      · have hD := (((hd a).mul ((hd b).pow (m + 1))).mul (hd c)).fderiv
        have e : (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
          = ((fun x => θ (x + (a - z))) * (fun x => θ (x + (b - z)) ^ (m + 1)))
            * fun x => θ (x + (c - z)) := rfl
        rw [e, hD] at key
        simp at key
        linear_combination key
      · intro n n' x
        have e : ∀ p : Fin g → ℂ, x + τ *ᵥ ofIntVec n + ofIntVec n' + p
            = x + p + τ *ᵥ ofIntVec n + ofIntVec n' := fun p => by abel
        simp only [e]
        rw [hlaw n n', hlaw n n', hlaw n n', mul_pow]
        have e2 : eC (-((m + 3 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ x))
            = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ (x + (a - z))))
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (b - z)))) ^ (m + 1)
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (c - z)))) := by
          unfold eC
          rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hc]
          congr 1
          simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          push_cast
          ring
        rw [e2]
        ring) t
    exact hper _ h h1 h2 h3
  have hcont : Continuous (fun t : ℂ => (⟨t • ξ, hmem t⟩ : periodLattice τ)) :=
    Continuous.subtype_mk (by fun_prop) _
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hcont (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

end GlobalTheory.ThetaTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem entire_eq_of_mul_eq_mul_right {f₁ f₂ θ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (hθ : Continuous θ) (hθ0 : θ ≠ 0)
    (h : ∀ z, f₁ z * θ z = f₂ z * θ z) : f₁ = f₂ := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, θ z₀ ≠ 0 := by
    by_contra hc
    apply hθ0
    funext z
    by_contra hz
    exact hc ⟨z, hz⟩
  have hW : IsOpen {z | θ z ≠ 0} := isOpen_ne_fun hθ continuous_const
  have hEq : Set.EqOn f₁ f₂ {z | θ z ≠ 0} := fun z hz => mul_right_cancel₀ hz (h z)
  have hall := GlobalTheory.SCV.eqOn_of_eqOn_open isOpen_univ isPreconnected_univ h₁.differentiableOn
    h₂.differentiableOn hW ⟨z₀, hz₀⟩ (Set.subset_univ _) hEq
  funext z
  exact hall (Set.mem_univ z)

theorem entire_eq_exp_linear_of_multiplier [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {h : E → ℂ} (hd : Differentiable ℂ h) (h0 : ∀ z, h z ≠ 0) {S : Set E}
    (hS : Submodule.span ℝ S = ⊤) (hper : ∀ s ∈ S, ∃ c : ℂ, ∀ z, h (z + s) = c * h z) :
    ∃ L : E →L[ℂ] ℂ, ∀ z, h z = h 0 * Complex.exp (L z) := by
  set F : E → E →L[ℂ] ℂ := fun z => (h z)⁻¹ • fderiv ℂ h z with hFdef
  have hfd : Differentiable ℂ (fderiv ℂ h) := by
    intro z
    exact (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hd.differentiableOn).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hF : Differentiable ℂ F := (hd.inv h0).smul hfd
  have hFper : ∀ x, ∀ s ∈ S, F (x + s) = F x := by
    intro x s hs
    obtain ⟨c, hc⟩ := hper s hs
    have hc0 : c ≠ 0 := by
      intro hc0
      apply h0 s
      have := hc 0
      rwa [zero_add, hc0, zero_mul] at this
    have hfun : (fun z => h (z + s)) = fun z => c * h z := funext hc
    have hder : fderiv ℂ h (x + s) = c • fderiv ℂ h x := by
      rw [← fderiv_comp_add_right, hfun, fderiv_const_mul (hd x) c]
    simp only [hFdef]
    rw [hder, hc, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have hconst : ∀ z, F z = F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hF hS hFper z 0
  have hdh : ∀ z, fderiv ℂ h z = h z • F 0 := by
    intro z
    rw [← hconst z, hFdef]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (h0 z), one_smul]
  refine ⟨F 0, fun z => ?_⟩
  have hG : ∀ y, HasFDerivAt (fun z => h z * Complex.exp (-(F 0) z)) (0 : E →L[ℂ] ℂ) y := by
    intro y
    have h1 : HasFDerivAt h (h y • F 0) y := by
      rw [← hdh]
      exact (hd y).hasFDerivAt
    have h2 : HasFDerivAt (fun z => Complex.exp (-(F 0) z)) (Complex.exp (-(F 0) y) • (-(F 0))) y :=
      ((F 0).hasFDerivAt.neg).cexp
    refine (h1.mul h2).congr_fderiv ?_
    simp only [smul_neg, smul_smul, mul_comm (h y), neg_add_cancel]
  have hGc := is_const_of_fderiv_eq_zero (f := fun z => h z * Complex.exp (-(F 0) z))
    (fun y => (hG y).differentiableAt) (fun y => (hG y).fderiv) z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one] at hGc
  rw [← hGc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end General

theorem mem_periodLattice_of_theta_translate_eq_unit_mul :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) := by
  intro H1 H2 g τ hτ w h hd h0 hrel
  obtain ⟨⟨hθd, hqp⟩, hθ0⟩ := H1 g τ hτ
  obtain ⟨-, hspan, -⟩ := H2 g τ hτ
  have hmult : ∀ n n' : Fin g → ℤ, ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z := by
    intro n n'
    set A : (Fin g → ℂ) → ℂ := fun z =>
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) with hA
    have hAne : ∀ z, A z ≠ 0 := fun z => by
      simp only [hA, eC]
      exact Complex.exp_ne_zero _
    have hAw : ∀ z, A (z + w) = A z * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      intro z
      simp only [hA]
      rw [← eC_add, dotProduct_add]
      congr 1
      ring
    have hAc : Continuous A := by
      simp only [hA, eC]
      exact Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul
        (continuous_const.add (continuous_const.dotProduct continuous_id))))
    have hne : (fun z => A z * theta 0 0 z τ) ≠ 0 := by
      intro hz
      apply hθ0
      funext z
      have := congrFun hz z
      simp only [Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left (hAne z)
    have hEq : ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ) =
        eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
      intro z
      have e2 : theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ = A z * theta 0 0 z τ := by
        rw [← add_assoc]
        exact hqp n n' z
      have e3 : theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ =
          A (z + w) * theta 0 0 (z + w) τ := by
        rw [← add_assoc]
        exact hqp n n' (z + w)
      calc h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ)
          = h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) *
              theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [e2]
        _ = theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n') + w) τ := (hrel _).symm
        _ = theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [add_right_comm]
        _ = A (z + w) * theta 0 0 (z + w) τ := e3
        _ = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
          rw [hAw, hrel]
          ring
    intro z
    exact congrFun (entire_eq_of_mul_eq_mul_right
      (f₁ := fun z => h (z + (τ *ᵥ ofIntVec n + ofIntVec n')))
      (f₂ := fun z => eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z)
      (hd.comp (differentiable_id.add_const _)) ((differentiable_const _).mul hd)
      (hAc.mul hθd.continuous) hne hEq) z
  have hS : ∀ s ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ c : ℂ, ∀ z, h (z + s) = c * h z := by
    rintro s ⟨n, n', rfl⟩
    exact ⟨_, hmult n n'⟩
  obtain ⟨L, hL⟩ := entire_eq_exp_linear_of_multiplier hd h0 hspan hS
  have hexp : ∀ n n' : Fin g → ℤ, Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
    intro n n'
    have e := hmult n n' 0
    rw [zero_add] at e
    have e' : h 0 * Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
        h 0 * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      rw [← hL, e, mul_comm]
    exact mul_left_cancel₀ (h0 0) e'
  have hk : ∀ j : Fin g, ∃ m : ℤ, L (Pi.single j 1) = m * (2 * Real.pi * Complex.I) := by
    intro j
    have e := hexp 0 (Pi.single j 1)
    have hv : τ *ᵥ ofIntVec (0 : Fin g → ℤ) + ofIntVec (Pi.single j 1) = Pi.single j 1 := by
      rw [ofIntVec_zero, mulVec_zero, zero_add]
      ext i
      by_cases hij : i = j
      · subst hij
        simp [ofIntVec]
      · simp [ofIntVec, hij]
    rw [hv, ofIntVec_zero, zero_dotProduct, mul_zero, eC_zero] at e
    exact Complex.exp_eq_one_iff.mp e
  choose k hk using hk
  have hLz : ∀ z, L z = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
    intro z
    calc L z = L (∑ i, Pi.single i (z i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, z i * L (Pi.single i 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsi : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ) := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj]
        rw [hsi, map_smul, smul_eq_mul]
      _ = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
        simp only [hk, dotProduct, ofIntVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  have hm : ∀ j : Fin g, ∃ m : ℤ, w j + (τ *ᵥ ofIntVec k) j = m := by
    intro j
    have e := hexp (Pi.single j 1) 0
    rw [ofIntVec_zero, add_zero, hLz] at e
    have hdot1 : ofIntVec (Pi.single j 1) ⬝ᵥ w = w j := by
      simp [ofIntVec, dotProduct, Pi.single_apply]
    have hdot2 : ofIntVec k ⬝ᵥ (τ *ᵥ ofIntVec (Pi.single j 1)) = (τ *ᵥ ofIntVec k) j := by
      rw [dot_mulVec_symm hτ.1]
      simp [ofIntVec, dotProduct, Pi.single_apply]
    rw [hdot1, hdot2] at e
    unfold eC at e
    have e2 : Complex.exp (2 * Real.pi * Complex.I * (w j + (τ *ᵥ ofIntVec k) j)) = 1 := by
      rw [mul_add, Complex.exp_add, e, ← Complex.exp_add,
        show 2 * (Real.pi : ℂ) * Complex.I * w j + 2 * Real.pi * Complex.I * (-(1 : ℂ) * w j) = 0 by
          ring, Complex.exp_zero]
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp e2
    exact ⟨m, mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hm]; ring)⟩
  choose m hm using hm
  show ∃ n n' : Fin g → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'
  refine ⟨-k, m, ?_⟩
  ext j
  have hj := hm j
  rw [ofIntVec_neg, mulVec_neg, Pi.add_apply, Pi.neg_apply]
  simp only [ofIntVec] at hj ⊢
  linear_combination hj

end GlobalTheory
end

