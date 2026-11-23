module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def Am (u : Fin 2 → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin 2) ℂ :=
  Matrix.of fun a i => emb τ.1 (u i) a

noncomputable def Cm (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    Matrix (Fin 2) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

theorem zmat_eq (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ = 1 + X.Am u τ * X.Cm u b τ := by
  ext a j
  simp only [Data.zmat, Data.Am, Data.Cm, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.of_apply, Fin.sum_univ_two]
  ring

theorem Cm_add (u : Fin 2 → Fin r → E) (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.Cm u (b + b') τ = X.Cm u b τ + X.Cm u b' τ := by
  ext i j
  simp only [Data.Cm, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma Cm_mulVec_apply (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  simp only [Matrix.mulVec, dotProduct, Data.Cm, Matrix.of_apply, hermC, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem Cm_mul_Am (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : X.Cm u b τ * X.Am u τ = 0 := by
  ext i i'
  have e : (X.Cm u b τ * X.Am u τ) i i' = (X.Cm u b τ *ᵥ emb τ.1 (u i')) i := rfl
  rw [e, Cm_mulVec_apply X u b τ, Matrix.zero_apply]
  simp only [hermC_emb, hu, map_zero, mul_zero, Finset.sum_const_zero]

theorem zmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  have h := X.Cm_mul_Am u hu b τ
  rw [X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]
  calc (1 + X.Am u τ * X.Cm u b τ) * (1 + X.Am u τ * X.Cm u b' τ)
      = 1 + X.Am u τ * X.Cm u b τ + X.Am u τ * X.Cm u b' τ +
          X.Am u τ * (X.Cm u b τ * X.Am u τ) * X.Cm u b' τ := by
        simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
        abel
    _ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by
        rw [h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]

theorem zmat_det (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : (X.zmat u b τ).det = 1 := by
  rw [X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]

theorem Am_mulVec (u : Fin 2 → Fin r → E) (τ : X.Ψ) (y : Fin 2 → ℂ) :
    X.Am u τ *ᵥ y = ∑ i, y i • emb τ.1 (u i) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Data.Am, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Cm_mulVec (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) (v : Fin r → ℂ) (i : Fin 2) :
    (X.Cm u b τ *ᵥ v) i = -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (emb τ.1 (u k)) := by
  exact Cm_mulVec_apply X u b τ v i

theorem zmat_unitary (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hb' : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w :=
    fun k => hermC_conj τ.1 X.Gm_herm _ _
  rw [X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]
  simp only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee,
    X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]
  ring

theorem mat_Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.Zb u b x) τ = X.zmat u b τ * mat x τ := rfl

theorem Zb_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) :
    X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x := by
  funext τ
  show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ
  rw [X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]

private lemma col_mul_eq_mulVec_col (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = M *ᵥ col N a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.Zb u b x) τ) = gram τ.1 X.Gm (mat x τ) := by
  rw [X.mat_Zb]
  ext a a'
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]
  exact X.zmat_unitary u hu b hb τ _ _

theorem dmin_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (X.Zb u b x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [X.gram_Zb u hu b hb x τ]

theorem Zb_dom (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u b x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [X.mat_Zb, Matrix.det_mul, X.zmat_det u hu, one_mul]
    exact (hx τ).1
  · rw [X.dmin_Zb u hu b hb]
    exact (hx τ).2 i

theorem nfac_Zb (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (X.Zb u b x) = X.nfac la x := by
  simp only [Data.nfac, X.dmin_Zb u hu b hb]

theorem flowV_uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (X.uvec u a) s x = X.Zb u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (X.uvec u a τ) τ (s τ) * mat x τ =
    X.zmat u (fun τ i k => s τ * a τ i * conj (a τ k)) τ * mat x τ
  congr 1
  ext p q
  have hk : ∀ k, ∑ l, τ.1 (X.Gm q l) * (conj (a τ k) * conj (emb τ.1 (u k) l)) =
      conj (a τ k) * ∑ l, τ.1 (X.Gm q l) * conj (emb τ.1 (u k) l) := fun k => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [Data.flowMatV, Data.zmat, Matrix.of_apply, Data.uvec, Fin.sum_univ_two, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, hk]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeSummability
section
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate

lemma summable_exp_abs (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by
  have hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))
  have h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun m => ?_
      simp only [Function.comp, Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
    · refine hgeo.congr fun m => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    convert h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp [Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section line

variable (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
  {n : ℕ} (ω : Fin n → X.Ψ → ℝ)

def Lc (t : Fin n → ℂ) : X.Ψ → ℂ := fun τ => ∑ j, t j * (ω j τ : ℂ)

noncomputable def hline (t : Fin n → ℂ) : ℂ := P (X.flow ξ (Lc X ω t) x)

def Om : Set (Fin n → ℝ) := (Fintype.linearCombination ℝ ω) ⁻¹' admissibleImaginary X ξ x

lemma lincomb_apply (y : Fin n → ℝ) (τ : X.Ψ) :
    Fintype.linearCombination ℝ ω y τ = ∑ j, y j * ω j τ := by
  simp [Fintype.linearCombination_apply, Finset.sum_apply]

lemma Lc_im (t : Fin n → ℂ) :
    (fun τ => (Lc X ω t τ).im) = Fintype.linearCombination ℝ ω (fun j => (t j).im) := by
  funext τ
  rw [lincomb_apply]
  simp [Lc, Complex.im_sum]

variable {X ξ x}

lemma flow_Lc_mem_dom (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) (t : Fin n → ℂ) :
    X.flow ξ (Lc X ω t) x ∈ X.dom ↔ t ∈ tube n (Om X ξ x ω) := by
  rw [flow_mem_dom_iff (X := X) hξ x hx, Lc_im]
  rfl

lemma Om_open_convex (hx : x ∈ X.dom) : IsOpen (Om X ξ x ω) ∧ Convex ℝ (Om X ξ x ω) := by
  have hc : Continuous (Fintype.linearCombination ℝ ω) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ho, hcv⟩ := admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx
  exact ⟨ho.preimage hc, hcv.linear_preimage _⟩

lemma zero_mem_Om (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) : (0 : Fin n → ℝ) ∈ Om X ξ x ω := by
  have h0 := (flow_mem_dom_iff (X := X) hξ x hx 0).1 (by rw [flow_zero]; exact hx)
  show Fintype.linearCombination ℝ ω 0 ∈ admissibleImaginary X ξ x
  rw [map_zero]
  simp only [Pi.zero_apply, Complex.zero_im] at h0
  exact h0

variable (X ξ x)

lemma hline_diff (hP : X.IsSec la P) (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube n (Om X ξ x ω)) := by
  intro t ht
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hLc : Differentiable ℂ (fun t : Fin n → ℂ => Lc X ω t) :=
    differentiable_pi.2 fun τ => Differentiable.fun_sum fun j _ =>
      (differentiable_apply j).mul_const _
  have hd1 : DifferentiableAt ℂ (fun t => X.flow ξ (Lc X ω t) x) t :=
    (flow_differentiable X ξ x).differentiableAt.comp t (hLc t)
  exact (hP.1 _ hmem).comp t hd1.differentiableWithinAt
    (fun t' ht' => (flow_Lc_mem_dom ω hξ hx t').2 ht')

lemma hline_periodic (hP : X.IsSec la P) (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0)
    (hx : x ∈ X.dom) (hωp : ∀ j, ω j ∈ X.periods la) :
    ∀ t ∈ tube n (Om X ξ x ω), ∀ m : Fin n → ℤ,
      hline X P ξ x ω (t + fun j => (m j : ℂ)) = hline X P ξ x ω t := by
  intro t ht m
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hp : (∑ j, (m j : ℝ) • ω j) ∈ X.periods la :=
    sum_mem fun j _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hωp j) _
  have hLc : Lc X ω (t + fun j => (m j : ℂ)) = cR X (∑ j, (m j : ℝ) • ω j) + Lc X ω t := by
    funext τ
    simp [Lc, cR, add_mul, Finset.sum_add_distrib, Finset.sum_apply, add_comm]
  simp only [hline]
  rw [hLc, ← flow_flow X hξ]
  exact sec_periodic X la P hP hξΛ hξ hp _ hmem

end line

end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace UnipotentCoefficientShift

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_conj_lt_one {a : E} (ha : IsIntegral ℤ a) (h : ∀ σ : E →+* ℂ, ‖σ a‖ < 1) :
    a = 0 := by
  classical
  by_contra ha0
  have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hN
    rw [← hn, map_zero]
  have hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, AlgHom.card]
    exact Module.finrank_pos
  have hlt : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ < ∏ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty₀
      (fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr ha0))
      (fun σ _ => h (σ : E →+* ℂ)) hne
  rw [Finset.prod_const_one, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a, ← hn] at hlt
  have h1 : ‖((n : ℚ) : ℂ)‖ < 1 := by simpa using hlt
  have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have h3 : ‖((n : ℚ) : ℂ)‖ = |(n : ℝ)| := by
    rw [Rat.cast_intCast, Complex.norm_intCast]
  linarith

variable {r : ℕ} {X : Data E r}

theorem Hf_add_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u + v) w = X.Hf z τ u w + X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_add, smul_add, hermC_sub_left, hermC_add_left, hermC_smul_left]
  ring

theorem Hf_sub_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u - v) w = X.Hf z τ u w - X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_sub, smul_sub, hermC_sub_left, hermC_smul_left]
  ring

private lemma ppos_smul' (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (k • u) = k • X.ppos z τ u := by
  simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

theorem Hf_smul_left (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ (k • u) w = k * X.Hf z τ u w := by
  simp only [Data.Hf, ppos_smul', smul_comm (2 : ℂ) k, hermC_sub_left, hermC_smul_left]
  ring

theorem Hf_add_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ u (v + w) = X.Hf z τ u v + X.Hf z τ u w := by
  simp only [Data.Hf, hermC_add_right]

theorem Hf_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ u (k • w) = conj k * X.Hf z τ u w := by
  simp only [Data.Hf, hermC_smul_right]

theorem Hf_conj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf z τ u w) = X.Hf z τ w u := by
  have key : hermC τ.1 X.Gm w (X.ppos z τ u) = hermC τ.1 X.Gm (X.ppos z τ w) u := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ u) w, X.hermC_ppos_left hz τ u w,
      hermC_conj τ.1 X.Gm_herm, X.hermC_ppos_left hz τ w u]
  simp only [Data.Hf]
  rw [hermC_conj τ.1 X.Gm_herm, hermC_sub_right, hermC_smul_right, hermC_sub_left, hermC_smul_left,
    key, map_ofNat]

private lemma maj_nonneg_of_mem_dom {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hz τ h).le

theorem norm_hermC_le_maj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v v‖ ≤ X.maj z τ v := by
  have hv : v = X.ppos z τ v + (v - X.ppos z τ v) := by abel
  have hPq : X.ppos z τ (v - X.ppos z τ v) = 0 := by
    rw [Data.ppos_sub, X.ppos_ppos hz, sub_self]
  have hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0 := by
    rw [hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]
  have hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]
  have hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) := by
    rw [Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]
  have hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) =
      -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    rw [Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]
  have hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v := by
    rw [Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]
  have hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) +
      hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    conv_lhs => rw [hv]
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]
    ring
  have eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ) := by
    rw [← hA]; exact X.Hf_self hz τ _
  have eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ) := by
    rw [← X.Hf_self hz τ, hB, neg_neg]
  have eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [← X.Hf_self hz τ, hV, hvv, eA, eB]
    push_cast
    ring
  have eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) := by
    exact_mod_cast eC
  have ha := maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)
  have hb := maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)
  have e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [hvv, eA, eB]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, eC']
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem maj_smul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by
  have hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) =
      ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0,
        hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
          conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    simp only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  simp only [Data.maj, Data.posPart]
  rw [hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem coef_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    X.Hf z τ (u + c • e) e / X.Hf z τ e e = X.Hf z τ u e / X.Hf z τ e e + c := by
  rw [Hf_add_left, Hf_smul_left, add_div, mul_div_assoc, div_self he, mul_one]

theorem ucomp_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    (u + c • e) - (X.Hf z τ (u + c • e) e / X.Hf z τ e e) • e =
      u - (X.Hf z τ u e / X.Hf z τ e e) • e := by
  rw [coef_shift z τ u e c he, add_smul]
  abel

theorem maj_decomp {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (he : X.Hf z τ e e ≠ 0) :
    X.maj z τ v = X.maj z τ (v - (X.Hf z τ v e / X.Hf z τ e e) • e) +
      ‖X.Hf z τ v e / X.Hf z τ e e‖ ^ 2 * X.maj z τ e := by
  set K := X.Hf z τ v e / X.Hf z τ e e with hKdef
  have hK : K * X.Hf z τ e e = X.Hf z τ v e := div_mul_cancel₀ _ he
  have h1 : X.Hf z τ (v - K • e) e = 0 := by
    rw [Hf_sub_left, Hf_smul_left, hK, sub_self]
  have h2 : X.Hf z τ e (v - K • e) = 0 := by
    rw [← Hf_conj hz τ (v - K • e) e, h1, map_zero]
  have hv : v = (v - K • e) + K • e := (sub_add_cancel v (K • e)).symm
  have hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e := by
    conv_lhs => rw [hv]
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right,
      Hf_smul_right, h1, h2]
    ring
  rw [X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hexp
  exact_mod_cast hexp

end UnipotentCoefficientShift

end ReciprocityTheory.ChartRestriction.G.FD
end

