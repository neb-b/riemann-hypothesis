module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFiniteAdele_integral_separated_complete : ∀ (D : D7), (∀ y : AE D, (∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = (N : AE D) * w) → y = 0) ∧ ∀ x : ℕ → AE D, (∀ N, x N ∈ OhE D) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w) → ∃ y ∈ OhE D, ∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = x N + (N : AE D) * w := by
  first | exact @GlobalTheory.IntAdeleComplete.integral_separated_complete | exact GlobalTheory.IntAdeleComplete.integral_separated_complete | (intros; apply GlobalTheory.IntAdeleComplete.integral_separated_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticFormEqAlternatingForm
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.Vacuum.Parity

theorem zmod_two : ∀ a b c f r s p q : ZMod 2, a * a + b * c = a → a * b + b * f = b → c * a + f * c = c →
    c * b + f * f = f → ¬ (r * a + s * c = 0 ∧ r * b + s * f = 0) →
    ¬ (r - (r * a + s * c) = 0 ∧ s - (r * b + s * f) = 0) →
    (((p * b + q * f) * p - (p * a + q * c) * q) + (q * r - p * s) = 0 ↔ p = 0 ∧ q = 0) := by
  decide

theorem int_two (a b c f r s p q n e : ℤ) (he : e * e = 1) (h1 : a * a + b * c = a - 2 * n) (h2 : a * b + b * f = b)
    (h3 : c * a + f * c = c) (h4 : c * b + f * f = f - 2 * n)
    (h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)))
    (h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f)))) :
    Even (e * ((p * b + q * f) * p - (p * a + q * c) * q) + e * (q * r - p * s)) ↔ Even p ∧ Even q := by
  have he' : ¬ Even e := by
    intro h
    have : Even (e * e) := h.mul_right e
    rw [he] at this
    exact Int.not_even_one this
  rw [← mul_add, Int.even_mul, or_iff_right he']
  simp only [← ZMod.intCast_eq_zero_iff_even] at h5 h6 ⊢
  have two : (2 : ZMod 2) = 0 := rfl
  have g1 := congrArg (Int.cast : ℤ → ZMod 2) h1
  have g2 := congrArg (Int.cast : ℤ → ZMod 2) h2
  have g3 := congrArg (Int.cast : ℤ → ZMod 2) h3
  have g4 := congrArg (Int.cast : ℤ → ZMod 2) h4
  push_cast at g1 g2 g3 g4 h5 h6 ⊢
  rw [two, zero_mul, sub_zero] at g1 g4
  exact zmod_two _ _ _ _ _ _ _ _ g1 g2 g3 g4 h5 h6

theorem coord_unique (L : PeriodPair) {p q p' q' : ℤ}
    (h : (p : ℂ) * L.ω₁ + q * L.ω₂ = p' * L.ω₁ + q' * L.ω₂) : p = p' ∧ q = q' := by
  have hi := LinearIndependent.pair_iff.1 L.indep ((p : ℝ) - p') ((q : ℝ) - q') (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination h)
  exact ⟨by exact_mod_cast sub_eq_zero.1 hi.1, by exact_mod_cast sub_eq_zero.1 hi.2⟩

theorem half_mem_iff (L : PeriodPair) (p q : ℤ) :
    ((p : ℂ) * L.ω₁ + q * L.ω₂) / 2 ∈ L.lattice ↔ Even p ∧ Even q := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    have := coord_unique L (p := p) (q := q) (p' := m + m) (q' := n + n) (by
      push_cast
      linear_combination -2 * h)
    exact ⟨⟨m, this.1⟩, ⟨n, this.2⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    exact ⟨m, n, by push_cast; ring⟩

theorem exists_sign (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ p q r s : ℤ,
      gl3FieldFirst Λ ((p : ℂ) * L.ω₁ + q * L.ω₂) ((r : ℂ) * L.ω₁ + s * L.ω₂) = ((e * (q * r - p * s) : ℤ) : ℝ) := by
  have hd := GlobalTheory.PlaneLattice.signedArea_ne_zero L
  have ha := GlobalTheory.PlaneLattice.area_eq L Λ h
  have hpos : 0 < area Λ := ha ▸ abs_pos.2 hd
  obtain ⟨e, he, he2⟩ : ∃ e : ℤ, area Λ = e * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ∧ e * e = 1 := by
    rcases abs_choice ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with h' | h'
    · exact ⟨1, by rw [ha, h']; simp only [Int.cast_one, one_mul], by simp⟩
    · exact ⟨-1, by rw [ha, h']; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul], by simp⟩
  refine ⟨e, he2, fun p q r s => ?_⟩
  have he3 : (e : ℝ) * e = 1 := by exact_mod_cast he2
  rw [gl3FieldFirst, div_eq_iff hpos.ne', he]
  simp
  linear_combination (-((q : ℝ) * r - p * s) * (L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re)) * he3

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  rw [q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
  simp [← Complex.ofReal_pow]
  ring

theorem cm_generator_sq_quadratic_eq (D : D7) : ∃ n : ℤ, w0 D * w0 D = w0 D - 2 * n := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, D.host.d + 1 = 8 * n := ⟨(D.host.d + 1) / 8, by omega⟩
  have hn' : (D.host.d : ℂ) + 1 = 8 * n := by exact_mod_cast hn
  have hs : (Real.sqrt D.host.d : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  refine ⟨n, ?_⟩
  rw [w0]
  push_cast
  linear_combination (Real.sqrt D.host.d : ℂ) ^ 2 / 4 * Complex.I_sq - 1 / 4 * hs - 1 / 4 * hn'

theorem lamOf_stable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) :
    ∀ w ∈ lamOf D cc δ, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, by simp; ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem lamOf_eq_closure (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  refine ⟨L.ω₁, L.ω₂, L.indep, AddSubgroup.ext fun z => ?_⟩
  rw [hL, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp only [zsmul_eq_mul]

theorem even_im_hermitian_sub : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → t0 ∉ (lamOf D cc δ) ∧ ∀ ω ∈ (lamOf D cc δ), ∃ m k : ℤ, q1 D (lamOf D cc δ) ω = m ∧ gl3FieldFirst (lamOf D cc δ) ω (2 * t0) = k ∧ (Even (m + k) ↔ ω / 2 ∈ (lamOf D cc δ)) := by
  intro D _ cc δ hc t0 ht
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  obtain ⟨α, hα⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hst : ∀ w ∈ lamOf D cc δ, w0 D * w ∈ lamOf D cc δ := fun w hw =>
    hα ▸ lamOf_stable D cc δ α w hw
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨fun h0 => ht2 (hst _ h0), fun ω hω => ?_⟩
  obtain ⟨e, he, hE⟩ := exists_sign L _ hL
  obtain ⟨n, hn⟩ := cm_generator_sq_quadratic_eq D
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₁_mem_lattice)))
  obtain ⟨c, f, hcf⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₂_mem_lattice)))
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ht1)
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((hL _).1 hω)
  have h12 := coord_unique L (p := a * a + b * c) (q := a * b + b * f) (p' := a - 2 * n) (q' := b) (by
    push_cast
    linear_combination (a + w0 D - 1) * hab + b * hcf + L.ω₁ * hn)
  have h34 := coord_unique L (p := c * a + f * c) (q := c * b + f * f) (p' := c) (q' := f - 2 * n) (by
    push_cast
    linear_combination c * hab + (f + w0 D - 1) * hcf + L.ω₂ * hn)
  have h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht2
    convert h using 1
    change w0 D * t0 = _
    push_cast
    linear_combination (-1 / 2 * r) * hab - 1 / 2 * s * hcf - 1 / 2 * w0 D * hrs
  have h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f))) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht3
    convert h using 1
    have e1 : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - w0 D := by rw [w0]; ring
    rw [e1]
    push_cast
    linear_combination (1 / 2 * r) * hab + 1 / 2 * s * hcf - 1 / 2 * (1 - w0 D) * hrs
  have hw : w0 D * ((p : ℂ) * L.ω₁ + q * L.ω₂) =
      ((p * a + q * c : ℤ) : ℂ) * L.ω₁ + ((p * b + q * f : ℤ) : ℂ) * L.ω₂ := by
    push_cast
    linear_combination -p * hab - q * hcf
  refine ⟨e * ((p * b + q * f) * p - (p * a + q * c) * q), e * (q * r - p * s), ?_, ?_, ?_⟩
  · rw [cmQuadraticForm_eq_alternatingForm, hw, hE]
  · rw [← hrs, hE]
  · rw [hL, half_mem_iff]
    exact int_two a b c f r s p q n e he h12.1 h12.2 h34.1 h34.2 h5 h6

end GlobalTheory.Vacuum.Parity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.MovedLattice

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h] at h2
  simp at h2

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  unfold Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (halfDifferent_ne_bot D))

def ext (D : D7) (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem ext_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) : ext D cc ≠ 0 := by
  unfold ext
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact h
  · exact FaithfulSMul.algebraMap_injective _ _

theorem coe_alg (D : D7) (c : 𝓞 D.host.K) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) =
      ((c : D.host.K) : D.host.E) := rfl

theorem mem_ext (D : D7) {cc : Ideal (𝓞 D.host.K)} {c : 𝓞 D.host.K} (h : c ∈ cc) :
    ((c : D.host.K) : D.host.E) ∈ ext D cc := by
  rw [← coe_alg]
  exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ h)

theorem inc_mul_mem (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) {j : D.host.E}
    (hj : j ∈ (ext D cc * D.host.AA0)⁻¹) {y : AE D} (hy : y ∈ IhE D cc) : inc D j * y ∈ OhE D := by
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D h) (inverseHalfDifferent_ne_zero D)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    rw [← mul_assoc, ← map_mul]
    refine mul_mem ?_ hs
    have h1 := FractionalIdeal.mul_mem_mul hj (FractionalIdeal.mul_mem_mul (mem_ext D hc) ha)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at h1
    exact (AdLattice.incl_mem_iff (F := ℚ) _).2 h1
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem smul_mem_homL (D : D7) {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L₁) (h' : Moves D g' L₁') (z : Matrix (Fin N') (Fin N) D.host.E) (j : D.host.E)
    (hz : ∀ a b, inc D j * (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D))) a b ∈ OhE D) : j • z ∈ homL D L₁ L₁' := by
  refine Submodule.subset_span fun x hx => ?_
  rw [h] at hx
  rw [h']
  intro i
  have key : ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)).mulVec
      (fun k => inc D ((j • z).mulVec x k)) =
      (inc D j • (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D)))).mulVec
        (((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec (fun k => inc D (x k))) := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul _ (inc D j)]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      RingHom.map_mulVec]
    rfl
  rw [key]
  simp only [Matrix.mulVec, dotProduct] at hx ⊢
  exact sum_mem fun k _ => mul_mem (hz i k) (hx k)

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (y y' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (y + y') = pt D (tor0 D cc δ) δ y + pt D (tor0 D cc δ) δ y' := by
  funext τ a b
  simp [pt, embV, tor0, mul_add]

theorem pt_smul_mem (D : D7) (hD : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    {m : D.host.E} (hm : m ∈ ext D cc) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L₁ L₁') :
    pt D (tor0 D cc δ) δ (m • y) ∈ La D (tor0 D cc δ) L₁ L₁' := by
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
  clear hm
  induction hb using Submodule.span_induction generalizing y with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, y, hy, ?_⟩
    funext τ a b
    rw [coe_alg]
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hD τ, mul_assoc]
  | zero =>
    have : pt D (tor0 D cc δ) δ (algebraMap (𝓞 D.host.E) D.host.E 0 • y) = 0 := by
      funext τ a b
      simp [pt, embV, tor0]
    rw [this]; exact zero_mem _
  | add b b' _ _ hb hb' =>
    rw [map_add (f := _), add_smul, pt_add]
    exact add_mem (hb hy) (hb' hy)
  | smul r b _ hb =>
    have := hb ((YYl D L₁ L₁').smul_mem r hy)
    rwa [← algebraMap_smul D.host.E r y, smul_smul, ← map_mul, mul_comm] at this

end GlobalTheory.NormSum.MovedLattice


open GlobalTheory.NormSum.MovedLattice in
theorem GlobalTheory.NormSum.pt_mem_La_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D hD cc δ hcc N N' g g' L₁ L₁' h h' z hz
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)
  have hY : ∀ n ∈ D.host.AA0 * (ext D cc * D.host.AA0)⁻¹, n • z ∈ YYl D L₁ L₁' := by
    intro n hn
    refine FractionalIdeal.mul_induction_on hn (fun a ha j hj => ?_) (fun x y hx hy => ?_)
    · refine Submodule.subset_span ⟨a, ha, j • z, ?_, mul_smul _ _ _⟩
      exact smul_mem_homL D _ _ h h' z j fun a b => inc_mul_mem D hcc hj (hz a b)
    · rw [add_smul]; exact add_mem hx hy
  have h1 : (1 : D.host.E) ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have h2 : ∀ e ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹),
      pt D (tor0 D cc δ) δ (e • z) ∈ La D (tor0 D cc δ) L₁ L₁' := by
    intro e he
    refine FractionalIdeal.mul_induction_on he (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul]
      exact pt_smul_mem D hD.1 cc δ L₁ L₁' hm (hY n hn)
    · rw [add_smul, pt_add]; exact add_mem hx hy
  simpa using h2 1 h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConj
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj.ProdLin

def CjN (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x y : ℂ) : Prop := x ∈ M ∧ y = cj M ρ x

theorem CjN.add {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x + y) (x' + y') :=
  ⟨add_mem h.1 h'.1, by rw [cj_add ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.mul {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x * y) (x' * y') :=
  ⟨mul_mem h.1 h'.1, by rw [cj_mul ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.rat (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (q : ℚ) : CjN M ρ (q : ℂ) (q : ℂ) := by
  have h : (q : ℂ) ∈ M := SubfieldClass.ratCast_mem M q
  refine ⟨h, ?_⟩
  rw [cj_mem ρ h]
  have : (⟨(q : ℂ), h⟩ : M) = (q : M) := by apply Subtype.ext; simp
  rw [this, map_ratCast]

inductive Rel {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : I → E)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : (E → ℂ) → (E → ℂ) → Prop
  | const (c c' : ℂ) : CjN M ρ c c' → Rel v M ρ (fun _ => c) (fun _ => c')
  | base (g g' : ℂ → ℂ) (L L' : E →L[ℂ] ℂ) : Differentiable ℂ g → Differentiable ℂ g' →
      (∀ n, CjN M ρ (iteratedDeriv n g 0) (iteratedDeriv n g' 0)) →
      (∀ k, CjN M ρ (L (v k)) (L' (v k))) → Rel v M ρ (fun z => g (L z)) (fun z => g' (L' z))
  | add (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z + G z) (fun z => F' z + G' z)
  | mul (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z * G z) (fun z => F' z * G' z)

variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : I → E}
  {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem Rel.contDiff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    ContDiff ℂ ⊤ F ∧ ContDiff ℂ ⊤ F' := by
  induction h with
  | const c c' _ => exact ⟨contDiff_const, contDiff_const⟩
  | base g g' L L' hg hg' _ _ => exact ⟨hg.contDiff.comp L.contDiff, hg'.contDiff.comp L'.contDiff⟩
  | add F F' G G' _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | mul F F' G G' _ _ h1 h2 => exact ⟨h1.1.mul h2.1, h1.2.mul h2.2⟩

theorem Rel.diff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    Differentiable ℂ F ∧ Differentiable ℂ F' :=
  ⟨h.contDiff.1.differentiable (by simp), h.contDiff.2.differentiable (by simp)⟩

theorem Rel.at_zero {F F' : E → ℂ} (h : Rel v M ρ F F') : CjN M ρ (F 0) (F' 0) := by
  induction h with
  | const c c' h => exact h
  | base g g' L L' _ _ h _ => simpa using h 0
  | add F F' G G' _ _ h1 h2 => exact h1.add h2
  | mul F F' G G' _ _ h1 h2 => exact h1.mul h2

theorem fderiv_base {g : ℂ → ℂ} (hg : Differentiable ℂ g) (L : E →L[ℂ] ℂ) (w : E) :
    (fun z => fderiv ℂ (fun z => g (L z)) z w) = fun z => L w * deriv g (L z) := by
  funext z
  have := ((hg (L z)).hasDerivAt.comp_hasFDerivAt z L.hasFDerivAt).fderiv
  change fderiv ℂ (g ∘ L) z w = _
  rw [this]; simp [mul_comm]

theorem fderiv_add' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z + G z) z w) = fun z => fderiv ℂ F z w + fderiv ℂ G z w := by
  funext z
  rw [fderiv_fun_add (hF z) (hG z)]; simp

theorem fderiv_mul' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z * G z) z w) =
      fun z => F z * fderiv ℂ G z w + G z * fderiv ℂ F z w := by
  funext z
  rw [fderiv_fun_mul (hF z) (hG z)]; simp

theorem Rel.fderiv {F F' : E → ℂ} (h : Rel v M ρ F F') (k : I) :
    Rel v M ρ (fun z => fderiv ℂ F z (v k)) (fun z => fderiv ℂ F' z (v k)) := by
  induction h with
  | const c c' h =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 0)
    simpa using this
  | base g g' L L' hg hg' h hL =>
    rw [fderiv_base hg, fderiv_base hg']
    refine Rel.mul _ _ _ _ (Rel.const _ _ (hL k))
      (Rel.base (deriv g) (deriv g') L L' hg.deriv hg'.deriv (fun n => ?_) hL)
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact h (n + 1)
  | add F F' G G' hF hG h1 h2 =>
    rw [fderiv_add' hF.diff.1 hG.diff.1, fderiv_add' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ h1 h2
  | mul F F' G G' hF hG h1 h2 =>
    rw [fderiv_mul' hF.diff.1 hG.diff.1, fderiv_mul' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ (Rel.mul _ _ _ _ hF h2) (Rel.mul _ _ _ _ hG h1)

theorem iteratedFDeriv_step {F : E → ℂ} (hF : ContDiff ℂ ⊤ F) (n : ℕ) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℂ (n + 1) F 0 m =
      iteratedFDeriv ℂ n (fun z => fderiv ℂ F z (m (Fin.last n))) 0 (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_clm_apply_const_apply (n := ⊤) (hF.fderiv_right (m := ⊤) le_top) le_top]

theorem Rel.iterated (n : ℕ) : ∀ {F F' : E → ℂ}, Rel v M ρ F F' → ∀ k : Fin n → I,
    CjN M ρ (iteratedFDeriv ℂ n F 0 fun i => v (k i)) (iteratedFDeriv ℂ n F' 0 fun i => v (k i)) := by
  induction n with
  | zero => intro F F' h k; simpa using h.at_zero
  | succ n ih =>
    intro F F' h k
    rw [iteratedFDeriv_step h.contDiff.1, iteratedFDeriv_step h.contDiff.2]
    exact ih (h.fderiv (k (Fin.last n))) (Fin.init k)

theorem Rel.prod {ι : Type} (s : Finset ι) {F F' : ι → E → ℂ} (h : ∀ i, Rel v M ρ (F i) (F' i)) :
    Rel v M ρ (fun z => ∏ i ∈ s, F i z) (fun z => ∏ i ∈ s, F' i z) := by
  induction s using Finset.induction_on with
  | empty =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 1)
    simpa using this
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact Rel.mul _ _ _ _ (h i) ih

theorem Rel.cjF {D : D7} {N N' : ℕ} {F F' : VC D N N' → ℂ} (h : Rel (coordV D) M ρ F F') :
    CjF D M ρ F F' := by
  refine ⟨h.diff.1, h.diff.2, fun α => ?_⟩
  have h1 := (Rel.iterated _ h (fun i : Fin (Multiset.card α.toMultiset) =>
    α.toMultiset.toList.get ⟨i, by rw [Multiset.length_toList]; exact i.2⟩)).mul
      (CjN.rat M ρ (α.prod fun _ n => (n.factorial : ℚ))⁻¹)
  have h2 : (((α.prod fun _ n => (n.factorial : ℚ))⁻¹ : ℚ) : ℂ) =
      (α.prod fun _ n => (n.factorial : ℂ))⁻¹ := by
    simp [Finsupp.prod]
  rw [h2] at h1
  unfold taylor
  simp only [div_eq_mul_inv]
  exact h1

def linF (D : D7) {N N' : ℕ} (l : VC D N N') : VC D N N' →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }

theorem linF_apply (D : D7) {N N' : ℕ} (l z : VC D N N') :
    linF D l z = ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c := rfl

theorem linF_coordV (D : D7) {N N' : ℕ} (l : VC D N N') (k : D.what₂.Tau × Fin N' × Fin N) :
    linF D l (coordV D k) = l k.1 k.2.1 k.2.2 := by
  rw [linF_apply]
  simp [coordV, ite_and]

theorem cjF_prod : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) →
    (∀ j, Differentiable ℂ (g' j)) →
    (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) →
    (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) →
    CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c))
      (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  intro D N N' r M ρ g g' l l' hg hg' hc hl
  refine Rel.cjF (Rel.prod Finset.univ fun j =>
    Rel.base (g j) (g' j) (linF D (l j)) (linF D (l' j)) (hg j) (hg' j) (fun n => ?_) fun k => ?_)
  · have h1 := CjN.mul (hc j n) (CjN.rat M ρ (n.factorial : ℚ))
    have h0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simpa only [coef1, Rat.cast_natCast, div_mul_cancel₀ _ h0] using h1
  · rw [linF_coordV, linF_coordV]; exact hl j _ _ _

end GlobalTheory.ThetaConj.ProdLin
end
end

