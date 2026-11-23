module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminant
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSum
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocalSum

theorem finsum_linear_combination_four {α : Type} {f g h i : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (hh : {x | h x ≠ 0}.Finite) (hi : {x | i x ≠ 0}.Finite)
    (a b c d : ℝ) :
    (∑ᶠ x, (a * f x + (b * g x + (c * h x + d * i x)))) =
      a * (∑ᶠ x, f x) + (b * (∑ᶠ x, g x) + (c * (∑ᶠ x, h x) + d * ∑ᶠ x, i x)) := by
  have sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite →
      (Function.support fun x => c * u x).Finite :=
    fun c u hu => hu.subset fun x hx h => hx (by simp [h])
  have sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite →
      (Function.support fun x => u x + v x).Finite :=
    fun u v hu hv => (hu.union hv).subset (Function.support_add u v)
  rw [finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))),
    finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)),
    finsum_add_distrib (sm c h hh) (sm d i hi)]
  simp only [mul_finsum]

theorem two_log_norm {E A : Type} [Field E] [NormedField A] (j : E →+* A) {r : E} {d : ℕ}
    (hr : r ^ 2 = -(d : E)) : 2 * Real.log ‖j r‖ = Real.log ‖(d : A)‖ := by
  have h1 : (j r) ^ 2 = -(d : A) := by rw [← map_pow, hr]; simp
  have h2 : ‖j r‖ ^ 2 = ‖(d : A)‖ := by rw [← norm_pow, h1, norm_neg]
  rw [← h2, Real.log_pow]
  norm_num

theorem deg_of_local_formulas : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN
  have hm : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef
  set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef

  have hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖
      - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
      + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
    intro ℓ j
    have h1 := hN ℓ j
    have h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := two_log_norm (j.comp τ) hr
    linear_combination h1 + (((p : ℝ) - q) / 2) * h2
  constructor
  · have S1 := GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ
    have S4 := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
    have S3 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
    refine (((S1.union S4).union S3).union hfin).subset ?_
    rintro ℓ ⟨j, hj⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h
    obtain ⟨⟨⟨h1, h4⟩, h3⟩, h2⟩ := h
    apply hj
    have e1 : Real.log ‖j ρ‖ = 0 := h1 j
    have e2 : Real.log ‖j (τ (t ℓ))‖ = 0 := h2 (j.comp τ)
    have e3 := h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))
    have e4 : Real.log ‖j (d : k)‖ = 0 := h4 j
    rw [map_natCast] at e4
    rw [hloc, e1, e2, e3, e4]
    simp
  ·
    have hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m := fun ℓ => by
      rw [hmdef, Embeddings.card]
    have hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m := by rw [hmdef, Embeddings.card]
    have hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
      intro ℓ
      simp only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
    have hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ
        + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (LogNorms.ofElt (d : k)).finSum ℓ)) := by
      intro ℓ
      have f1 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)
      have f2 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq E k ℂ_[ℓ] τ
        (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
      have g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) =
          ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
        Finset.sum_congr rfl fun j _ => htt ℓ j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum] at g1
      have h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖
          - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
          + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
        have c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ =
            ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
        rw [← c1, Finset.mul_sum]
        simp only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f1
      have hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f2
      have hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖ := rfl
      rw [h0, hDd, hT, hD, hae]
      linear_combination (-(m / e) / 2) * g1
    have hA := GlobalTheory.T.product_formula_log_norms k ρ hρ
    have hE := GlobalTheory.T.product_formula_log_norms E a ha
    have hG := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
    have hΔ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.different_sum_eq_neg_finrank_mul_log_rootDiscr E
    have hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ)
        + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ)
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (∑ᶠ ℓ, (LogNorms.ofElt (d : k)).finSum ℓ))) := by
      rw [finsum_congr hsum]
      exact finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _
    have hlogn : ∑ s, Real.log (n s) = -(m * x) := by
      rw [← hx]; field_simp
    have hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖)
        + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2))
        + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2 := by
      simp only [hinf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC, ← Finset.sum_div]
    have hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖ := by
      rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
      exact _root_.GlobalTheory.CompanionTheory.Ar.Fl.finrank_mul_sum_comp_eq E k ℂ τ (fun i => Real.log ‖i a‖)
    have hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d := by
      simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC]
    have h1 := hA.2
    have h2 := hE.2
    have h3 := hG.2
    have h4 := hΔ.2
    rw [hdinf] at h3
    have hme : m / e * e = m := div_mul_cancel₀ _ he
    have key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ =
        m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E)
          - ((p : ℝ) + q) / 2 * Real.log d) := by
      rw [hI, hfs, hlogn, hAτ, h4]
      linear_combination h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3
        + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme
    have hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y := fun Y => by field_simp
    rw [LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]
    ring

end GlobalTheory.CompanionTheory.Ar.Fl.LocalSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx

section Main

variable {E : Type} [Field E] [NumberField E] {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {ρ : 𝓞 E →+* Module.End K W} {ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)}

theorem fst_proj (hact : ∀ a y, (ρH a y).1 = ρ a y.1) (σ : E →+* K) (y : W × Module.Dual K W) :
    (HT.eigProj ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hact]

theorem comp_proj {bar : 𝓞 E ≃+* 𝓞 E} (hinr : ∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) {σ σ' : E →+* K}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual K W}
    (h : ((0 : W), φ) ∈ HT.eigSp ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have h3 : ∀ k z, φ (ρ (RingOfIntegers.basis E k) z) = σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) • φ z := by
    intro k z
    have h1 := HT.LatBasic.mem_eigSp.1 h (bar (RingOfIntegers.basis E k))
    rw [hinr, hb, ← hσ] at h1
    have h2 := congrArg Prod.snd h1
    exact LinearMap.congr_fun h2 z
  have h2 : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one σ', ← HT.LatBasic.sum_dualInt_mul, map_sum]
    simp
  ext z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HT.eigProj, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h3,
    smul_smul]
  rw [← Finset.sum_smul, h2, one_smul]

theorem dual_frame [CharZero K] {q : ℕ} {b : Fin q → W} (hb : LinearIndependent K b) {τ : E →+* K}
    (hspan : Submodule.span K (Set.range b) = HT.eigSp ρ τ) :
    ∃ f : Fin q → Module.Dual K W, (∀ x, HT.eigProj ρ τ x = ∑ j, f j x • b j) ∧
      (∀ j j', f j (b j') = if j = j' then 1 else 0) ∧
      ∀ j (c : 𝓞 E), f j ∘ₗ ρ c = τ (c : E) • f j := by
  classical
  let B := Module.Basis.span hb
  let π : W →ₗ[K] Submodule.span K (Set.range b) := (HT.eigProj ρ τ).codRestrict _ fun x => by
    rw [hspan]
    exact HT.LatBasic.eigProj_mem ρ τ x
  have hπ : ∀ x, ((π x : Submodule.span K (Set.range b)) : W) = HT.eigProj ρ τ x := fun x => rfl
  have hfix : ∀ x ∈ HT.eigSp ρ τ, HT.eigProj ρ τ x = x := fun x hx => HT.LatBasic.eigProj_of_mem hx
  refine ⟨fun j => B.coord j ∘ₗ π, fun x => ?_, fun j j' => ?_, fun j c => ?_⟩
  · have h1 := congrArg Subtype.val (B.sum_repr (π x))
    rw [hπ] at h1
    rw [← h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [B, Module.Basis.span_apply]
  · have h1 : π (b j') = B j' := Subtype.ext (by
      rw [hπ, Module.Basis.span_apply]
      exact hfix _ (hspan ▸ Submodule.subset_span ⟨j', rfl⟩))
    simp [h1, Finsupp.single_apply, eq_comm]
  · ext x
    have h1 : π (ρ c x) = τ (c : E) • π x := Subtype.ext (by
      have h2 : HT.eigProj ρ τ (ρ c x) = ρ c (HT.eigProj ρ τ x) := by
        have hcomm : ∀ k, ρ (RingOfIntegers.basis E k) (ρ c x) = ρ c (ρ (RingOfIntegers.basis E k) x) := fun k => by
          rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
      rw [hπ, h2, HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ τ x) c]
      rfl)
    simp [h1]

end Main

theorem exists_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ _ _ ρ ρH bar σ σ' p q v w hact hinr hσσ' hbar hv hvs hw hws
  classical
  obtain ⟨f, hf1, hf2, hf4⟩ := dual_frame hw hws
  let u : Fin (p + q) → W × Module.Dual K W :=
    Fin.addCases (fun i => HT.eigProj ρH σ (v i, 0)) (fun j => ((0 : W), f j))
  have hul : ∀ i, u (Fin.castAdd q i) = HT.eigProj ρH σ (v i, 0) := fun i => by simp [u]
  have hur : ∀ j, u (Fin.natAdd p j) = ((0 : W), f j) := fun j => by simp [u]
  have hvm : ∀ i, v i ∈ HT.eigSp ρ σ := fun i => hvs ▸ Submodule.subset_span ⟨i, rfl⟩
  have hu1 : ∀ i, (u (Fin.castAdd q i)).1 = v i := fun i => by
    rw [hul, fst_proj hact]
    exact HT.LatBasic.eigProj_of_mem (hvm i)
  have hueig : ∀ i, u i ∈ HT.eigSp ρH σ := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [hul]
      exact HT.LatBasic.eigProj_mem _ _ _
    | right j =>
      rw [hur, HT.LatBasic.mem_eigSp]
      intro a
      have h1 := hf4 j (bar a)
      rw [hσσ', hbar] at h1
      rw [hinr, h1]
      simp
  have had : IsAdapted ρH σ v w u := by
    unfold IsAdapted
    exact ⟨hueig, hu1, fun j => ⟨by rw [hur], fun j' => by rw [hur]; exact hf2 j j'⟩⟩
  refine ⟨u, had, ?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∑ i, g (Fin.castAdd q i) • v i = 0 := by
      have h := congrArg Prod.fst hg
      simpa [Prod.fst_sum, hu1, hur] using h
    have hc := Fintype.linearIndependent_iff.1 hv _ h1
    have h3 : ∑ j, g (Fin.natAdd p j) • f j = 0 := by
      have h := congrArg Prod.snd hg
      simpa [Prod.snd_sum, hur, hc] using h
    have hd : ∀ j', g (Fin.natAdd p j') = 0 := fun j' => by
      have h := LinearMap.congr_fun h3 (w j')
      simpa [LinearMap.sum_apply, hf2] using h
    intro i
    induction i using Fin.addCases with
    | left i => exact hc i
    | right j => exact hd j
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hueig i
  · intro y hye
    have hy1 : y.1 ∈ Submodule.span K (Set.range v) := by
      rw [hvs]
      refine HT.LatBasic.mem_eigSp.2 fun a => ?_
      rw [← hact, HT.LatBasic.mem_eigSp.1 hye a]
      rfl
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy1
    obtain ⟨z, hz⟩ : ∃ z, z = y - ∑ i, c i • u (Fin.castAdd q i) := ⟨_, rfl⟩
    have hze : z ∈ HT.eigSp ρH σ := by
      rw [hz]
      exact Submodule.sub_mem _ hye (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hueig _))
    have hz1 : z.1 = 0 := by
      rw [hz, Prod.fst_sub, Prod.fst_sum, sub_eq_zero, ← hc]
      simp [hu1]
    have hzz : ((0 : W), z.2) = z := Prod.ext hz1.symm rfl
    have hcomp : z.2 ∘ₗ HT.eigProj ρ σ' = z.2 := comp_proj hinr hσσ' hbar (hzz.symm ▸ hze)
    have hd : z.2 = ∑ j, z.2 (w j) • f j := by
      ext x
      have h1 := LinearMap.congr_fun hcomp x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.comp_apply, hf1, map_sum] at h1
      rw [← h1]
      simp [LinearMap.sum_apply, mul_comm]
    have e2 : ∑ j, z.2 (w j) • (((0 : W), f j) : W × Module.Dual K W) = z := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, hz1]
      · rw [Prod.snd_sum]
        simpa using hd.symm
    have e3 : y = ∑ i, (Fin.addCases c (fun j => z.2 (w j)) i : K) • u i := by
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, hur]
      rw [e2, hz]
      abel
    rw [e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem bc_smul {C : Type} [Field C] [Algebra Ω C] {ι : Type} (w : Ω) (v : ι → Ω) :
    bcMap Ω C ι (w • v) = algebraMap Ω C w • bcMap Ω C ι v := by
  funext i
  show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)
  rw [map_mul]

theorem pow_one_smul_mem {E : Type} [AddCommGroup E] [Module Ω E] {R : Subalgebra o Ω} {N : ℕ}
    {L : AddSubgroup E} (hL : LocFree R N L) {p : ℕ} {w : Ω} (hw : ∃ c ∈ R, (p : Ω) = c * w) {v : E}
    (hv : w • v ∈ L) : ∃ m : ℕ, (p : Ω) ^ m • v ∈ L := by
  obtain ⟨c, hc, e⟩ := hw
  refine ⟨1, ?_⟩
  rw [pow_one, e, mul_smul]
  exact hL.1 c hc _ hv

end GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence


open GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence in
theorem GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ
  have hle := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG
  have hbc1 := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange.imH_bc D R p w χ hc hb hG hle
  obtain ⟨hf2, hbc2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main D R p w χ hc hb hG hG2 hle
  have hp0 := hc.1
  have hw := hc.2.2.1
  obtain ⟨flie, -, fom, -⟩ := hb.free τ
  obtain ⟨i1, i2, i3, i4⟩ := hb.incl τ
  refine ⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine _root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_
    · obtain ⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [hbc1 C RC hRC.2.2.2 τ]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).im τ
      exact e.le h
  · refine _root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_
    · exact ⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← hbc1 C RC hRC.2.2.2 τ]
      have e := (hT C RC hRC).im τ
      exact e.ge (mem_span RC ⟨v, hv, rfl⟩)
  · show w • v ∈ D.lie τ
    refine _root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_
    · obtain ⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [((hbc2 C RC hRC.2.2.2).2 τ).1]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).ker τ
      rw [bc_smul]
      exact e.le h
  · have hv' : w • v ∈ D.lie τ := hv
    refine _root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_
    · exact ⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← ((hbc2 C RC hRC.2.2.2).2 τ).1]
      have e := (hT C RC hRC).ker τ
      refine e.ge ?_
      show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ
      rw [← bc_smul]
      exact mem_span RC ⟨_, hv', rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartTestPoint
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem om'_between_of_testPoints : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') :=
  @PositivityTheory.HtPt.Gc.chart_ii

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSq
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem isPrimitiveRoot_map_of_charZero {A C : Type} [CommRing A] [IsDomain A] [Field C] [CharZero C]
    (ψ : A →+* C) (p : ℕ) [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (ψ ζ) p := by
  have hp1 := hp.out
  have h1 : ψ ζ ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ψ ζ ≠ 1 := by
    intro h
    have hs := congrArg ψ (hζ.geom_sum_eq_zero hp1.one_lt)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at hs
    simp only [map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hs
    exact hp1.ne_zero (by exact_mod_cast hs)
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h1 h2)

theorem isHTConst_sub_one_of_primitive {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [hp : Fact p.Prime] {A : Type} [CommRing A] [IsDomain A]
    (φ : A →+* O) {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsHTConst v p (φ (ζ - 1)) ∧ (ζ - 1) ∣ (p : A) ^ 2 := by
  have h1 : IsPrimitiveRoot ((algebraMap O C) (φ ζ)) p :=
    GlobalTheory.CompanionTheory.Ar.HT.isPrimitiveRoot_map_of_charZero ((algebraMap O C).comp φ) p hζ
  have hne : p - 1 ≠ 0 := by
    have := hp.out.two_le
    omega
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_one]
    exact GlobalTheory.CompanionTheory.Ar.HT.PointTest.isHTConst_sub_one h1
  · exact (dvd_pow_self (ζ - 1) hne).trans
      ((GlobalTheory.CompanionTheory.Ar.HT.primRoot_sub_one_pow_associated hp.out hζ).dvd.trans
        (dvd_pow_self _ two_ne_zero))

theorem isHTConst_of_isCp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  intro C _ v O _ _ hv _ p _ A _ _ _ φ κ hvp hκ
  split_ifs at hκ with h2
  · subst h2
    subst hκ
    have hv2 : v (2 : C) < 1 := by exact_mod_cast hvp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [map_ofNat, map_ofNat]
      norm_num
    · rw [map_ofNat, map_ofNat]
      have h4 : (4 : C) = 2 * 2 := by norm_num
      rw [h4, map_mul]
      norm_num
      exact mul_le_of_le_one_left' hv2.le
    · exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_sub_one_of_primitive v hv p φ hζ

end GlobalTheory.CompanionTheory.Ar.HT
end

