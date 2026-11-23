module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurEquivariantIsometryScalar
section
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

noncomputable section
open Complex
open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace Real FourierTransform ContDiff SchwartzMap

namespace GlobalTheory.RealWeil.FourierConjProductVanishing

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem ae_eq_zero_of_fourier_eq_zero {D : V → ℂ} (hD : Integrable D) (hF : ∀ ξ, 𝓕 D ξ = 0) :
    D =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hD.locallyIntegrable fun g hg hgc => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set ψ : 𝓢(V, ℂ) := hg₁.toSchwartzMap hg₂ with hψ
  set φ : 𝓢(V, ℂ) := 𝓕⁻ ψ with hφ
  have h0 : ∀ x, (𝓕 φ) x = (g x : ℂ) := fun x => by
    rw [hφ, FourierTransform.fourier_fourierInv_eq, hψ]
    simp
  have h1 : ∫ x, g x • D x = ∫ x, (𝓕 φ) x * D x := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [h0, Complex.real_smul]
  have h2 : ∫ x, (𝓕 φ) x * D x = ∫ x, φ x * 𝓕 D x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hD
    simpa using! this
  rw [h1, h2]
  simp [hF]

variable {l : Type} [Fintype l]

def pt (p q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) (fun i => q i)

theorem pPart_pt (p q : EuclideanSpace ℝ l) : pPart (pt p q) = p := by
  ext i; simp [pPart, pt]

theorem qPart_pt (p q : EuclideanSpace ℝ l) : qPart (pt p q) = q := by
  ext i; simp [qPart, pt]

theorem fourier_conj_mul_eq_zero (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) (p ξ : EuclideanSpace ℝ l) :
    𝓕 (fun x => conj (f x) * g (x + p)) ξ = 0 := by
  have h1 := h (pt p (-ξ))
  rw [L2.inner_def] at h1
  have h2 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x = 0 := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rho (pt p (-ξ)) g] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h3 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x =
      cexp (((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) * 𝓕 (fun x => conj (f x) * g (x + p)) ξ := by
    rw [Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [rhoFun, phase, pPart_pt, qPart_pt, smul_eq_mul]
    have e : (((2 * π * ⟪-ξ, x⟫ + π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) =
        ((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I + ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * I := by
      rw [inner_neg_left, real_inner_comm]
      push_cast
      ring
    rw [e, Complex.exp_add]
    ring
  rw [h2] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left (Complex.exp_ne_zero _)

theorem integrable_conj_mul_shift (f g : L2 l) (p : EuclideanSpace ℝ l) :
    Integrable (fun x => conj (f x) * g (x + p)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) f (rho (pt p 0) g)).congr ?_
  filter_upwards [coeFn_rho (pt p 0) g] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]
  simp [rhoFun, phase, pPart_pt, qPart_pt]

theorem eq_zero_or_eq_zero_of_inner_rho (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) : f = 0 ∨ g = 0 := by
  have hz : ∀ p : EuclideanSpace ℝ l, ∀ᵐ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 = 0 := by
    intro p
    filter_upwards [ae_eq_zero_of_fourier_eq_zero (integrable_conj_mul_shift f g p)
      (fourier_conj_mul_eq_zero f g h p)] with x hx
    have hx' : conj ((f : _ → ℂ) x) * (g : _ → ℂ) (x + p) = 0 := hx
    rcases mul_eq_zero.1 hx' with h0 | h0
    · rw [map_eq_zero] at h0
      simp [h0]
    · simp [h0]
  have hfm : Measurable fun x => ‖(f : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable f).measurable.enorm.pow_const 2
  have hgm : Measurable fun x => ‖(g : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable g).measurable.enorm.pow_const 2
  have hprod : (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2) = 0 := by
    calc (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2)
        = ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ∫⁻ p, ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          rw [← lintegral_mul_const _ hfm]
          refine lintegral_congr fun x => ?_
          rw [lintegral_add_left_eq_self (fun y => ‖(g : _ → ℂ) y‖ₑ ^ 2) x]
      _ = ∫⁻ x, ∫⁻ p, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_congr fun x => ?_
          exact (lintegral_const_mul _ (hgm.comp (measurable_const_add x))).symm
      _ = ∫⁻ p, ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_lintegral_swap ?_
          exact ((hfm.comp measurable_fst).mul (hgm.comp measurable_add)).aemeasurable
      _ = 0 := by
          rw [← lintegral_zero]
          exact lintegral_congr fun p => lintegral_eq_zero_of_ae_eq_zero (hz p) |>.trans rfl
  have key : ∀ u : L2 l, (∫⁻ x, ‖(u : _ → ℂ) x‖ₑ ^ 2) = 0 → u = 0 := by
    intro u hu
    have hum : Measurable fun x => ‖(u : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable u).measurable.enorm.pow_const 2
    rw [lintegral_eq_zero_iff hum] at hu
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hu] with x hx
    simpa using hx
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact Or.inl (key f h0)
  · exact Or.inr (key g h0)

theorem rho_symm_apply (w : l ⊕ l → ℝ) (v : L2 l) :
    (rho w).symm v = (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rho (-w) v := by
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, rho_rho, add_neg_cancel, rho_zero,
    inv_smul_smul₀ (Complex.exp_ne_zero _)]

def opSet (l : Type) [Fintype l] : Set (L2 l →L[ℂ] L2 l) :=
  Set.range fun cw : ℂ × (l ⊕ l → ℝ) => cw.1 • ((rho cw.2).toContinuousLinearEquiv : L2 l →L[ℂ] L2 l)

theorem star_mem_opSet : ∀ A ∈ opSet l, star A ∈ opSet l := by
  rintro _ ⟨⟨c, w⟩, rfl⟩
  refine ⟨⟨conj c * (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹, -w⟩, ?_⟩
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint]
  ext v
  have e := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) (LinearIsometryEquiv.adjoint_eq_symm (rho w))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e ⊢
  rw [e, rho_symm_apply, smul_smul]
  rfl

theorem irreducible_opSet (S : Submodule ℂ (L2 l)) (hS : IsClosed (S : Set (L2 l)))
    (hst : ∀ A ∈ opSet l, ∀ v ∈ S, A v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro f hf
  have hw : ∀ w, ⟪f, rho w g⟫_ℂ = 0 := by
    intro w
    have hm : rho w g ∈ S := by
      have := hst _ ⟨⟨1, w⟩, rfl⟩ g hg
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal hm hf
  exact (eq_zero_or_eq_zero_of_inner_rho f g hw).resolve_right hg0

end GlobalTheory.RealWeil.FourierConjProductVanishing

namespace GlobalTheory.RealWeil


open GlobalTheory.RealWeil.FourierConjProductVanishing in
theorem schur_rho_l2 : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  intro l _ U hU
  obtain ⟨c, hc⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded (opSet l) star_mem_opSet
    (fun S hS hst => irreducible_opSet S hS hst) (U.toContinuousLinearEquiv : L2 l →L[ℂ] L2 l) (by
      rintro _ ⟨⟨c, w⟩, rfl⟩
      ext v
      simp [hU])
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) hc
  simpa using this

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecomposition
section
open scoped nonZeroDivisors
open GlobalTheory.EtC

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

theorem artinian_quot {I : Ideal B} (hI : I ≠ ⊥) : IsArtinianRing (B ⧸ I) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
    intro h
    apply hI
    rw [eq_bot_iff, ← h]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem exists_split (f b : B) (hb : b ≠ 0) :
    ∃ (N : ℕ) (Q : Ideal B), Ideal.span {b} = (Ideal.span {b} ⊔ Ideal.span {f ^ N}) * Q ∧
      Q ⊔ Ideal.span {f} = ⊤ := by
  haveI := artinian_quot (I := Ideal.span {b}) (by simpa using hb)
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (Ideal.Quotient.mk (Ideal.span {b}) f) (1 : B ⧸ Ideal.span {b})
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : f ^ N - f ^ (N + 1) * y' ∈ Ideal.span {b} := by
    rw [← Ideal.Quotient.eq]
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    rw [map_mul, map_pow, map_pow, hy]
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hbP : Ideal.span {b} ≤ P := le_sup_left
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hbP
  refine ⟨N, Q, hQ, ?_⟩
  have hP0 : P ≠ 0 := by
    intro h
    apply hb
    have : b ∈ P := hbP (Ideal.mem_span_singleton_self b)
    rw [h] at this
    simpa using this
  have key : P * (Q ⊔ Ideal.span {f}) = P * ⊤ := by
    rw [Ideal.mul_top, Ideal.mul_sup, ← hQ]
    apply le_antisymm
    · exact sup_le hbP Ideal.mul_le_left
    · apply sup_le le_sup_left
      rw [Ideal.span_singleton_le_iff_mem]
      have e : f ^ N = (f ^ N - f ^ (N + 1) * y') + f ^ N * y' * f := by ring
      rw [e]
      refine add_mem (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right ?_)
      exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _))) (Ideal.mem_span_singleton_self f)
  exact mul_left_cancel₀ hP0 key

theorem exists_mem_coprime {I : Ideal B} (hI : I ≠ ⊥) (f : B) (h : I ⊔ Ideal.span {f} = ⊤) :
    ∃ g ∈ I, g ≠ 0 ∧ IsCoprime f g := by
  have h1 : (1 : B) ∈ I ⊔ Ideal.span {f} := h ▸ Submodule.mem_top
  obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx, hx0, ⟨c, 0, by simpa using hay⟩⟩
  · exact ⟨a, ha, ha0, ⟨c, 1, by linear_combination hay⟩⟩

theorem isCoprime_ideal_of_le {I J J' : Ideal B} (h : IsCoprime I J) (hle : J ≤ J') :
    IsCoprime I J' := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.2 (h ▸ sup_le_sup_left hle I)

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

theorem core (q : ℕ) (hq : q ≠ 0) (hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c)
    (f b : B) (hf : f ≠ 0) (hb : b ≠ 0) :
    ∃ (g n t w : B) (N : ℕ), g ≠ 0 ∧ IsCoprime f g ∧ IsCoprime f n ∧ IsCoprime g w ∧
      b ∣ f ^ N * g ∧ n ∣ g ^ q ∧ b * t ^ q = n * w := by
  obtain ⟨N, Q, hQ, hQf⟩ := exists_split f b hb
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hb
    simpa using hQ
  have hf0 : Ideal.span {f} ≠ ⊥ := by simpa using hf
  let Q' : (Ideal B)⁰ := ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ0⟩
  obtain ⟨c, hc⟩ := hdiv (ClassGroup.mk0 Q')⁻¹
  obtain ⟨J, hJf, hJc⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hf0 c
  have hmemQJ : Q * (J : Ideal B) ^ q ∈ (Ideal B)⁰ := (Q' * J ^ q).2
  have h1 : ClassGroup.mk0 ⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ = 1 := by
    have : (⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ : (Ideal B)⁰) = Q' * J ^ q := Subtype.ext (by simp [Q'])
    rw [this, map_mul, map_pow, hJc, hc, mul_inv_cancel]
  obtain ⟨n, hn⟩ := ((ClassGroup.mk0_eq_one_iff hmemQJ).1 h1).principal
  have hn' : Q * (J : Ideal B) ^ q = Ideal.span {n} := hn
  have hJ0 : (J : Ideal B) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Q * (J : Ideal B) ^ q = ⊥ := by rw [hn']; simp
    rcases Ideal.mul_eq_bot.1 this with h | h
    · exact hQ0 h
    · exact hJ0 (pow_eq_zero_iff hq |>.1 h)

  have cQ : IsCoprime (Ideal.span {f}) Q := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hQf
  have cJ : IsCoprime (Ideal.span {f}) (J : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJf
  have hfn : IsCoprime f n := by
    rw [← Ideal.isCoprime_span_singleton_iff, ← hn']
    exact cQ.mul_right (cJ.pow_right)

  have hQJ0 : Q * (J : Ideal B) ≠ ⊥ := mul_ne_zero hQ0 hJ0
  have hQJf : Q * (J : Ideal B) ⊔ Ideal.span {f} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq]; exact (cQ.mul_right cJ).symm
  obtain ⟨g, hgQJ, hg0, hfg⟩ := exists_mem_coprime hQJ0 f hQJf

  have hg0' : Ideal.span {g} ≠ ⊥ := by simpa using hg0
  obtain ⟨J₂, hJ₂g, hJ₂c⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hg0' (ClassGroup.mk0 J)⁻¹
  have hmemJJ : (J : Ideal B) * (J₂ : Ideal B) ∈ (Ideal B)⁰ := (J * J₂).2
  have h2 : ClassGroup.mk0 ⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ = 1 := by
    have : (⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ : (Ideal B)⁰) = J * J₂ := rfl
    rw [this, map_mul, hJ₂c, mul_inv_cancel]
  obtain ⟨t, ht⟩ := ((ClassGroup.mk0_eq_one_iff hmemJJ).1 h2).principal
  have ht' : (J : Ideal B) * (J₂ : Ideal B) = Ideal.span {t} := ht

  have hspan : Ideal.span {b * t ^ q} = Ideal.span {n} * (P * (J₂ : Ideal B) ^ q) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ← ht', hQ, ← hn',
      mul_pow]
    ring
  have hdvd : n ∣ b * t ^ q := by
    rw [← Ideal.mem_span_singleton]
    have hle : Ideal.span {b * t ^ q} ≤ Ideal.span {n} := hspan ▸ Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self _)
  obtain ⟨w, hw⟩ := hdvd
  have hn0' : Ideal.span {n} ≠ 0 := by simpa using hn0
  have hwspan : Ideal.span {w} = P * (J₂ : Ideal B) ^ q := by
    apply mul_left_cancel₀ hn0'
    rw [Ideal.span_singleton_mul_span_singleton, ← hw, hspan]
  have cgP : IsCoprime (Ideal.span {g}) P := by
    apply isCoprime_ideal_of_le _ (le_sup_right : Ideal.span {f ^ N} ≤ P)
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hfg.symm.pow_right
  have cgJ₂ : IsCoprime (Ideal.span {g}) (J₂ : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJ₂g
  have hgw : IsCoprime g w := by
    rw [← Ideal.isCoprime_span_singleton_iff, hwspan]
    exact cgP.mul_right cgJ₂.pow_right
  refine ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, ?_, ?_, hw⟩
  · rw [← Ideal.mem_span_singleton, hQ]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      ((Ideal.mul_le_left : Q * (J : Ideal B) ≤ Q) hgQJ)
  · rw [← Ideal.mem_span_singleton, ← hn']
    have : g ^ q ∈ (Q * (J : Ideal B)) ^ q := Ideal.pow_mem_pow hgQJ q
    rw [mul_pow] at this
    exact Ideal.mul_mono_left (Ideal.pow_le_self hq) this

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

theorem divisor_step : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 →
    ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ,
      ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧
      algebraMap B (Localization.Away (f * g)) (b * d) =
        (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧
      (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') =
        algebraMap B (Localization.Away (f * g)) n' := by
  intro k B _ _ _ _ _ _ q hq f hf b hb m
  have hqk : (q : k) ≠ 0 := hq.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  have hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := GlobalTheory.T.classGroup_dedekind_algClosed_divisible k B q hqk
  obtain ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, hbd, hnd, hw⟩ := core q hq0 hdiv f b hf hb
  refine ⟨g, hg0, hfg, ?_⟩
  set L := Localization.Away (f * g)
  have hfgU : IsUnit (algebraMap B L (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgU
  have hfU : IsUnit (algebraMap B L f) := isUnit_of_mul_isUnit_left hfgU
  have hgU : IsUnit (algebraMap B L g) := isUnit_of_mul_isUnit_right hfgU
  have hbU : IsUnit (algebraMap B L b) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hbd) ?_
    rw [map_mul, map_pow]
    exact (hfU.pow N).mul hgU
  have hnU : IsUnit (algebraMap B L n) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hnd) ?_
    rw [map_pow]
    exact hgU.pow q
  set un := (hnU.mul (hfU.pow m)).unit with hun
  have hv : (algebraMap B L n * algebraMap B L f ^ m) * ((un⁻¹ : Lˣ) : L) = 1 := by
    have : (un : L) = algebraMap B L n * algebraMap B L f ^ m := rfl
    rw [← this]; exact Units.mul_inv un
  refine ⟨hbU.unit * un⁻¹, n, 1, t, w, f ^ m, hfn, isCoprime_one_right, hgw, hfg.symm.pow_right, ?_, ?_⟩
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    rw [Units.val_mul, hb', map_mul, map_mul, map_one, map_pow]
    linear_combination (-(algebraMap B L b)) * hv
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    have hw' := congrArg (algebraMap B L) hw
    simp only [map_mul, map_pow] at hw'
    rw [Units.val_mul, hb', map_mul, map_pow, map_pow]
    linear_combination (((un⁻¹ : Lˣ) : L) * algebraMap B L f ^ m) * hw' + algebraMap B L w * hv

end GlobalTheory.KummerDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEqStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_henselisation_prime_eq : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_torsor) | (exact GlobalTheory.KeyOriginCut.exists_stage_torsor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_torsor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (exact GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv) | (intros; apply GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickSetDensityLeInvFourLwStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickSet_density_le_inv_four_Lw : ∀ (D : D7) (L : SizeData₂ D), 8 * D.host.Lw < D.R.n → L.de2 ≤ 1 / (4 * (D.host.Lw : ℝ)) := by
  first | exact @GlobalTheory.thick_density_le | exact GlobalTheory.thick_density_le | (intros; apply GlobalTheory.thick_density_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltValuation

theorem tilt_isDomain_valuationRing : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ _ : IsDomain (PreTilt O p), ValuationRing (PreTilt O p) := by
  intro p _ C _ _ _ v O _ _ _ _ hv
  haveI hdom : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2 ⟨fun a b => by
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  exact ⟨hdom, ValuationRing.iff_dvd_total.2 ⟨fun a b => GlobalTheory.FrobInt.dvd_total_tilt a b⟩⟩

end GlobalTheory.TiltValuation
end

