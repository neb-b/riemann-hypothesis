module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quadConj_eq_complexConj (x : E) :
    conj (maximalRealSubfield E) E x = IsCMField.complexConj E x := by
  set K := maximalRealSubfield E
  set t := IsCMField.complexConj E
  set y := conj K E x with hy
  have hyy : conj K E y = x := conj_conj x
  have fix : ∀ a : E, conj K E a = a → t a = a := by
    intro a ha
    obtain ⟨b, rfl⟩ := conj_eq_self_iff.1 ha
    exact (IsCMField.complexConj_eq_self_iff E _).2 b.2
  have ha : t (x + y) = x + y := fix _ (by rw [map_add (f := _), hyy, ← hy, add_comm])
  have hb : t (x * y) = x * y := fix _ (by rw [map_mul, hyy, ← hy, mul_comm])
  have hz : (t x - x) * (t x - y) = 0 := by
    have h0 : x * x - (x + y) * x + x * y = 0 := by ring
    have h1 := congrArg t h0
    rw [map_add (f := _), map_sub, map_mul, map_mul, ha, hb, map_zero] at h1
    linear_combination h1
  rcases mul_eq_zero.1 hz with h | h
  · have hx : t x = x := sub_eq_zero.1 h
    have : x ∈ K := (IsCMField.complexConj_eq_self_iff E x).1 hx
    have h2 : y = x := conj_eq_self_iff.2 ⟨⟨x, this⟩, rfl⟩
    rw [h2, hx]
  · exact (sub_eq_zero.1 h).symm

theorem complexConj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (IsCMField.complexConj E (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj E φ, h]
    obtain ⟨s, hs⟩ := Complex.conj_eq_iff_real.1 hc
    have h3 := congrArg φ hsq
    rw [map_pow, map_neg, map_natCast, hs] at h3
    have h4 : (s ^ 2 : ℝ) = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg s]
  · exact h

theorem sesq_skew {V : Type} [AddCommGroup V] [Module E V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V)
    (hadj : ∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y))
    (hskew : ∀ u v, B u v = - B v u) (h₁ : V → V → E)
    (htr : ∀ x y (a : E), Algebra.trace ℚ E (a * h₁ x y) = B (a • x) y) (u v : V) :
    h₁ v u = - IsCMField.complexConj E (h₁ u v) := by
  have nd := traceForm_nondegenerate ℚ E
  have htc : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have : h₁ v u - (- IsCMField.complexConj E (h₁ u v)) = 0 := by
    apply nd.1
    intro a
    have e1 : Algebra.trace ℚ E (a * IsCMField.complexConj E (h₁ u v)) =
        Algebra.trace ℚ E (IsCMField.complexConj E a * h₁ u v) := by
      rw [← htc, map_mul, IsCMField.complexConj_apply_apply]
    have e2 : B u (a • v) = B (IsCMField.complexConj E a • u) v := by
      rw [hadj, IsCMField.complexConj_apply_apply]
    rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, mul_neg, map_neg, e1, htr, htr,
      hskew (a • v) u, e2]
    ring
  linear_combination this


omit [IsCMField E] in
theorem exists_nat_integral {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (F : Λ → Λ → E)
    (h1 : ∀ x x' y, F (x + x') y = F x y + F x' y) (h2 : ∀ x y y', F x (y + y') = F x y + F x y') :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : Fin n × Fin n => F (s p.1) (s p.2))
  have step : ∀ g : Λ →+ E, (∀ i, g (s i) ∈ integralClosure ℤ E) →
      ∀ x, g x ∈ integralClosure ℤ E := by
    intro g hg x
    have hx : x ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i, rfl⟩ := h
      exact hg i
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_zsmul]
      exact zsmul_mem hx a
  have core : ∀ m : ℕ, (∀ i k, (m : E) * F (s i) (s k) ∈ integralClosure ℤ E) →
      ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
    intro m hm x y
    let gy : Λ → Λ →+ E := fun x => AddMonoidHom.mk' (fun y => (m : E) * F x y)
      (fun a b => by rw [h2, mul_add])
    let gx : Λ → Λ →+ E := fun y => AddMonoidHom.mk' (fun x => (m : E) * F x y)
      (fun a b => by rw [h1, mul_add])
    exact step (gy x) (fun k => step (gx (s k)) (fun i => hm i k) x) y
  have hint : ∀ i k, IsIntegral ℤ (y • F (s i) (s k)) := fun i k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := hint i k
    rwa [zsmul_eq_mul, Int.cast_natCast] at this
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := (hint i k).neg
    rwa [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this

end Field

theorem exists_hermitian_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  intro E _ _ _ H Λ _ _ N e B hadj hskew hnd
  obtain ⟨h₁, ⟨htr, hadd1, hadd2, hsm1, hsm2⟩, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_sesq_of_trace E (Fin N → E) B hadj
  have hsk := sesq_skew B hadj hskew h₁ htr
  obtain ⟨m, hm0, hint⟩ := exists_nat_integral (fun x y : Λ => h₁ (e y) (e x))
    (fun x x' y => by rw [map_add (f := _), hadd2]) (fun x y y' => by rw [map_add (f := _), hadd1])
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [h0] at hsq
    have hd : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
    apply hd
    linear_combination hsq
  set c : E := (m : E) * (H.rt : E) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hm0) hrt0
  have htc : IsCMField.complexConj E c = -c := by
    rw [hc, map_mul, map_natCast, complexConj_rt]
    ring
  let S : (Fin N → E) →ₛₗ[conjHom (maximalRealSubfield E) E] (Fin N → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (conjHom (maximalRealSubfield E) E) (RingHom.id E) (fun v u => c * h₁ u v)
      (fun v v' u => by rw [hadd2, mul_add])
      (fun a v u => by
        rw [hsm2, smul_eq_mul]
        have : conjHom (maximalRealSubfield E) E a = IsCMField.complexConj E a :=
          quadConj_eq_complexConj a
        rw [this]
        ring)
      (fun v u u' => by rw [hadd1, mul_add])
      (fun a v u => by
        rw [hsm1, RingHom.id_apply, smul_eq_mul]
        ring)
  have Sapp : ∀ v u, S v u = c * h₁ u v := fun _ _ => rfl
  have hinj : Function.Injective S := by
    intro v v' hvv
    have hz : ∀ w, h₁ w (v - v') = 0 := by
      intro w
      have h3 : c * h₁ w v = c * h₁ w v' := by
        rw [← Sapp, ← Sapp, hvv]
      have h4 := mul_left_cancel₀ hc0 h3
      have h5 := hadd2 w (v - v') v'
      rw [sub_add_cancel, h4] at h5
      linear_combination -h5
    have : v - v' = 0 := hnd _ fun w => by
      have h6 := htr w (v - v') 1
      rw [one_smul, hz, mul_zero, map_zero] at h6
      exact h6.symm
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective S := by
    let g0 : (Fin N → E) →+ (Fin N → E) := AddMonoidHom.mk' (fun u i => S u (Pi.single i 1))
      (fun a b => by
        funext i
        show S (a + b) (Pi.single i 1) = S a (Pi.single i 1) + S b (Pi.single i 1)
        rw [Sapp, Sapp, Sapp, hadd2, mul_add])
    let g : (Fin N → E) →ₗ[ℚ] (Fin N → E) := g0.toRatLinearMap
    have gapp : ∀ u i, g u i = S u (Pi.single i 1) := fun _ _ => rfl
    have ginj : Function.Injective g := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro u hu
      have : S u = S 0 := by
        apply (Pi.basisFun E (Fin N)).ext
        intro i
        rw [Pi.basisFun_apply, map_zero, ← gapp, hu]
        rfl
      exact hinj (this.trans (by rw [map_zero]) |>.trans (map_zero S).symm)
    have gsurj : Function.Surjective g := LinearMap.injective_iff_surjective.1 ginj
    intro f
    obtain ⟨u, hu⟩ := gsurj fun i => f (Pi.single i 1)
    refine ⟨u, (Pi.basisFun E (Fin N)).ext fun i => ?_⟩
    rw [Pi.basisFun_apply, ← gapp, hu]
  refine ⟨⟨S, ⟨fun x y => ?_⟩, hinj, hsurj⟩, m, hm0, ?_, ?_⟩
  · have h7 : conjHom (maximalRealSubfield E) E (S x y) = IsCMField.complexConj E (S x y) :=
      quadConj_eq_complexConj _
    rw [h7, Sapp, Sapp, map_mul, htc, hsk y x]
    ring
  · intro a u v
    have h8 : ((m : E) * (H.rt : E))⁻¹ * S v u = h₁ u v := by
      rw [Sapp, ← hc, inv_mul_cancel_left₀ hc0]
    show Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * S v u)) = _
    rw [h8, htr]
  · intro x y
    show S (e x) (e y) ∈ integralClosure ℤ E
    rw [Sapp, hc]
    have h9 : (H.rt : E) ∈ integralClosure ℤ E := (H.rt).isIntegral_coe
    have h10 := mul_mem h9 (hint x y)
    convert h10 using 1
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

open Complex Matrix

namespace GlobalTheory.CompanionTheory.Metric

theorem mean_sq_fixes_norm_const :
    ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (Λ : Submodule ℤ (Fin g → ℂ))
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ) (b : ℝ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, c i = 0 ∨ c i = 1 / 2) →
    (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ, h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z)) →
    (∀ l ∈ Λ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z, θ (z + l) = ε *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * θ z) →
    0 < b →
    (∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
      b ^ 2 = (∫ w in Fd, (‖θ w‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm w w).re)) ^ 2) / (volume Fd).toReal) →
    b ^ 2 = ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h Hm a c Λ θ κ b hs hp hh ha hc hΛ hH hθ hper hb hmean
  have h₁ : ∀ i, (fun i => (a i : ℂ)) i = 0 ∨ (fun i => (a i : ℂ)) i = 1 / 2 := fun i => by
    rcases ha i with e | e <;> simp [e]
  have h₂ : ∀ i, (fun i => (c i : ℂ)) i = 0 ∨ (fun i => (c i : ℂ)) i = 1 / 2 := fun i => by
    rcases hc i with e | e <;> simp [e]
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨Fd, hFd, -⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) Λ.toAddSubgroup hs hp hh h₁ h₂ hΛ
  have hFdΛ : IsAddFundamentalDomain Λ Fd volume := hFd
  have hb2 := hmean Fd hFdΛ
  have hsq := GlobalTheory.Dict.VacNorm.norm_sq_of_mean (τ := τ) (h := h) (A := Λ.toAddSubgroup)
    (H := hermForm Hm) (θ := fun z => θ z / b) (a := κ / b) ⟨hs, hp⟩ hh h₁ h₂ hΛ
    (fun z w => by
      rw [hH]
      rfl)
    (fun z => by
      simp only [hθ, GlobalTheory.CanTh.canTh, GlobalTheory.CanTh.imInv]
      ring)
    (fun p hp' => by
      obtain ⟨ε, hε, hz⟩ := hper p hp'
      have hε0 : ε ≠ 0 := by
        intro e
        simp [e] at hε
      refine ⟨ε⁻¹, by simp [hε], fun z => ?_⟩
      have e2 : hermForm Hm (z + (1 / 2 : ℂ) • p) p = hermForm Hm z p + 1 / 2 * hermForm Hm p p := by
        simp only [hermForm, add_dotProduct, smul_dotProduct, smul_eq_mul]
      simp only [hz, e2]
      have e3 : Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
          Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p) = 1 := by
        rw [← Complex.exp_add]
        simp only [Nat.cast_one]
        ring_nf
        simp
      have e1 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
      linear_combination (θ z / b * Complex.exp (-(((1 : ℕ) : ℂ) * Real.pi * (hermForm Hm z p + 1 / 2 * hermForm Hm p p))) *
        Complex.exp (Real.pi * hermForm Hm z p + Real.pi / 2 * hermForm Hm p p)) * e1 + (θ z / b) * e3)
    hFd
    (by
      have hint : ∀ z, ‖θ z / (b : ℂ)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = (b ^ 2)⁻¹ *
          (‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re)) ^ 2 := by
        intro z
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, mul_pow, div_pow,
          ← Real.exp_nat_mul]
        have : ((2 : ℕ) : ℝ) * (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) =
            -Real.pi * (hermForm Hm z z).re := by
          push_cast
          ring
        rw [this]
        ring
      simp only [hint]
      rw [MeasureTheory.integral_const_mul, mul_div_assoc, ← hb2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hb.ne'))
  have hD : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hp.det_pos)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, div_pow,
    div_eq_iff (pow_ne_zero _ hb.ne')] at hsq
  rw [hsq]
  field_simp

end GlobalTheory.CompanionTheory.Metric
end

