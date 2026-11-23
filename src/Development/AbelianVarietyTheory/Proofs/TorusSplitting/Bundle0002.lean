module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsShortIntegersSpan
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.FD in
theorem exists_short_integers_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
        ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
  intro E _ _ _
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hΛ : ∀ x, x ∈ Λ ↔ IsIntegral ℤ (x 0) := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      have : (a • (fun _ => 1 : Fin 1 → E)) 0 = (a : E) := by
        simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe
    · intro h
      refine ⟨⟨x 0, h⟩, ?_⟩
      funext k
      rw [Subsingleton.elim k 0]
      exact mul_one (x 0)
  have hh : ∀ x y : Fin 1 → E, herm 1 x y = x 0 * cc (y 0) := by
    intro x y
    simp [herm]
  have hc : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (cc x) := fun x hx =>
    hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  obtain ⟨v, hv, -, hsp, hle⟩ := exists_short_vectors Λ (Submodule.fg_span_singleton _)
    (fun x hx y hy => by
      rw [hh]
      exact ((hΛ x).1 hx).mul (hc _ ((hΛ y).1 hy)))
    (fun x hx => by
      have := hx (fun _ => 1) (Submodule.mem_span_singleton_self _)
      rw [hh] at this
      rw [hΛ]
      simpa [cc] using this)
  refine ⟨_, fun j => ⟨v j 0, (hΛ _).1 (hv j)⟩, fun j σ => ?_, fun α => ?_⟩
  · have h := hle j σ
    have he : 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * ((1 : ℕ) : ℝ) ^ 2 * rdE E = omStar (E := E) := by
      simp only [omStar, Nat.cast_one, one_pow, mul_one]
      rfl
    have h0 : 0 ≤ omStar (E := E) := by
      unfold omStar PT.rd
      positivity
    rw [he, Fin.sum_univ_one] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 h
  · have h : (fun _ => (α : E) : Fin 1 → E) ∈ Submodule.span ℚ (Set.range v) :=
      hsp ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℚ) (φ := fun _ : Fin 1 => E) 0) h
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCMulImHermCEqSignMulTrace
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.hermC_emb_eq_map_herm {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) = τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) :=
  (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_herm τ G u v).symm


open NumberField in
theorem _root_.GlobalTheory.re_map_xi_eq_zero {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) : (τ X.ξ0).re = 0 := by
  have h := congrArg τ X.ξ0_im
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith


open NumberField in
theorem _root_.GlobalTheory.c_eq_two_mul_abs_im {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by
  have hre := _root_.GlobalTheory.re_map_xi_eq_zero X τ.1
  have hz : τ.1 X.ξ0 = ((τ.1 X.ξ0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.c
  conv_lhs => rw [hz]
  simp [Complex.norm_real]

end GlobalTheory
end

