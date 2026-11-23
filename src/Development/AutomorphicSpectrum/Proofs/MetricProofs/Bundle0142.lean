module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphisms
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

section Ext

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem exists_basis (e : Λ →+ V) (hspan : Submodule.span E (e.range : Set V) = ⊤) :
    ∃ (I : Type) (b : Module.Basis I E V) (xs : I → Λ), ∀ i, b i = e (xs i) := by
  obtain ⟨B, hB, hsp, hli⟩ := exists_linearIndependent E (e.range : Set V)
  have hx : ∀ i : B, ∃ x, e x = i.1 := fun i => AddMonoidHom.mem_range.1 (hB i.2)
  choose xs hxs using hx
  refine ⟨B, Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hspan]), xs, fun i => ?_⟩
  rw [Module.Basis.mk_apply, hxs]

theorem exists_clear {I : Type} (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (b : Module.Basis I E V) (xs : I → Λ)
    (hb : ∀ i, b i = e (xs i)) (x : Λ) :
    ∃ (d : 𝓞 E) (s : Finset I) (a : I → 𝓞 E), d ≠ 0 ∧ d • x = ∑ i ∈ s, a i • xs i := by
  classical
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (b.repr (e x)).support (fun i => b.repr (e x) i)
  have h2 : ∀ i ∈ (b.repr (e x)).support, ∃ a : 𝓞 E, (a : E) = (d : E) * b.repr (e x) i := by
    intro i hi
    obtain ⟨a, ha⟩ := hint i hi
    refine ⟨a, ?_⟩
    rw [show (a : E) = algebraMap (𝓞 E) E a from rfl, ha, Algebra.smul_def]
  choose! a ha using h2
  refine ⟨d, (b.repr (e x)).support, a, nonZeroDivisors.ne_zero hd, he ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  conv_lhs => rw [← b.linearCombination_repr (e x), Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hs, ← hb, ha i hi, smul_smul]

theorem exists_ext (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (f : Λ →ₗ[𝓞 E] Λ) :
    ∃ Φ : V →ₗ[E] V, ∀ x, Φ (e x) = e (f x) := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis e hspan
  refine ⟨b.constr E fun i => e (f (xs i)), fun x => ?_⟩
  obtain ⟨d, s, a, hd, hx⟩ := exists_clear e he hs b xs hb x
  have hdE : (d : E) ≠ 0 := by simpa using hd
  have h1 : (d : E) • (b.constr E fun i => e (f (xs i))) (e x) = (d : E) • e (f x) := by
    rw [← map_smul, ← hs, ← hs, ← map_smul, hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hs, map_smul, ← hb, Module.Basis.constr_basis]
  exact smul_right_injective _ hdE h1

theorem exists_extEquiv (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (φ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ Φ : V ≃ₗ[E] V, ∀ x, Φ (e x) = e (φ x) := by
  obtain ⟨Φ₁, h₁⟩ := exists_ext e he hs hspan (φ : Λ →ₗ[𝓞 E] Λ)
  obtain ⟨Φ₂, h₂⟩ := exists_ext e he hs hspan (φ.symm : Λ →ₗ[𝓞 E] Λ)
  refine ⟨LinearEquiv.ofLinear Φ₁ Φ₂ ?_ ?_, fun x => h₁ x⟩
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]

theorem exists_lat (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (γ : V ≃ₗ[E] V)
    (h₁ : ∀ x, ∃ y, e y = γ (e x)) (h₂ : ∀ x, ∃ y, e y = γ.symm (e x)) :
    ∃ φ : Λ ≃ₗ[𝓞 E] Λ, ∀ x, e (φ x) = γ (e x) := by
  choose f hf using h₁
  choose k hk using h₂
  refine ⟨{ toFun := f, invFun := k, map_add' := fun x y => he ?_, map_smul' := fun a x => he ?_,
            left_inv := fun x => he ?_, right_inv := fun x => he ?_ }, hf⟩
  · simp [hf]
  · simp [hf, hs]
  · simp [hf, hk]
  · simp [hf, hk]

theorem eq_zero_of_trace {xi u : E} (hxi : xi ≠ 0)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (xi * ((a : E) * u)) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨z, hz⟩ := Algebra.trace_surjective ℚ E 1
  have halg : IsAlgebraic ℤ (z / (xi * u)) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 := h (IsIntegralClosure.mk' (𝓞 E) _ hint)
  rw [show ((IsIntegralClosure.mk' (𝓞 E) _ hint : 𝓞 E) : E) = _ from
    IsIntegralClosure.algebraMap_mk' (𝓞 E) _ hint] at h1
  have h2 : xi * (m • (z / (xi * u)) * u) = (m : ℚ) • z := by
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp only [eq_intCast, map_intCast]
    field_simp
  rw [h2, map_smul, hz] at h1
  simp at h1
  exact hm h1

end Ext

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
  {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

theorem xi_ne_zero (C : LatEmb F) : C.xi ≠ 0 := by
  have hΨ : ∃ τ : Ψ, True := by
    by_contra hn
    have hn' : ∀ τ : Ψ, False := fun τ => hn ⟨τ, trivial⟩
    let s : 𝓞 E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding.comp (algebraMap (𝓞 E) E)
    have h := (F.cm.2 s).2 (fun ⟨τ, _⟩ => hn' τ)
    exact hn' h.choose
  obtain ⟨τ, -⟩ := hΨ
  intro h0
  have h1 := C.xi_eq τ
  rw [h0, map_zero] at h1
  have he : C.eps τ ≠ 0 := by
    intro h
    have := C.eps_sq τ
    rw [h] at this
    norm_num at this
  have hc : C.c * C.eps τ ≠ 0 := mul_ne_zero C.c_pos.ne' he
  have : ((C.c * C.eps τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  exact (mul_ne_zero Complex.I_ne_zero this) h1.symm

theorem sesq_eq (C : LatEmb F) (φ : autGrp (E := E) F.form) (x y : Λ) :
    C.h.toSesq (C.e (φ.1 y)) (C.e (φ.1 x)) = C.h.toSesq (C.e y) (C.e x) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_trace (xi_ne_zero C) fun a => ?_
  have h1 := C.form_eq (a • φ.1 x) (φ.1 y)
  have h2 := C.form_eq (a • x) y
  have h3 : F.form (a • φ.1 x) (φ.1 y) = F.form (a • x) y := by
    rw [← map_smul]
    exact φ.2 _ _
  rw [h3, h2, C.e_smul, C.e_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  rw [mul_sub, mul_sub, map_sub, sub_eq_zero]
  exact h1.symm

theorem ext_unitary (C : LatEmb F) (φ : autGrp (E := E) F.form)
    (Φ : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (hΦ : ∀ x, Φ (C.e x) = C.e (φ.1 x)) :
    Φ ∈ C.h.unitaryGroup := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis C.e C.integral.isLattice.span_eq_top
  intro v w
  have key : (C.h.toSesq.comp (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E))).compl₂
      (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) = C.h.toSesq := by
    refine LinearMap.ext_basis b b fun p q => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hb, hΦ]
    exact sesq_eq C φ _ _
  exact LinearMap.congr_fun₂ key v w

open scoped Pointwise in
theorem stab_apply_mem (C : LatEmb F) (γ : latticeStab C.h C.e.range) (x : Λ) :
    ∃ y, C.e y = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  have hs : (γ : C.h.unitaryGroup) • C.e.range = C.e.range := MulAction.mem_stabilizer_iff.1 γ.2
  have h1 : (γ : C.h.unitaryGroup) • C.e x ∈ (γ : C.h.unitaryGroup) • C.e.range :=
    AddSubgroup.smul_mem_pointwise_smul _ _ _ ⟨x, rfl⟩
  rw [hs] at h1
  exact h1

theorem exists_of_stab (C : LatEmb F) (γ : latticeStab C.h C.e.range) :
    ∃ φ : autGrp (E := E) F.form, ∀ x, C.e (φ.1 x) =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  obtain ⟨φ, hφ⟩ := exists_lat C.e C.e_inj C.e_smul
    ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E))
    (stab_apply_mem C γ) (stab_apply_mem C γ⁻¹)
  refine ⟨⟨φ, fun x y => ?_⟩, hφ⟩
  have hu := (γ : C.h.unitaryGroup).2 (C.e y) (C.e x)
  apply Int.cast_injective (α := ℚ)
  rw [C.form_eq, C.form_eq, hφ, hφ]
  exact congrArg (fun t => Algebra.trace ℚ E (C.xi * t)) hu


open scoped Pointwise in
theorem exists_of_aut (C : LatEmb F) (φ : autGrp (E := E) F.form) :
    ∃ γ : latticeStab C.h C.e.range, ∀ x,
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) = C.e (φ.1 x) := by
  obtain ⟨Φ, hΦ⟩ := exists_extEquiv C.e C.e_inj C.e_smul C.integral.isLattice.span_eq_top φ.1
  have hU := ext_unitary C φ Φ hΦ
  refine ⟨⟨⟨Φ, hU⟩, ?_⟩, hΦ⟩
  refine MulAction.mem_stabilizer_iff.2 ?_
  ext v
  change v ∈ Φ • C.e.range ↔ _
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨φ.1 x, (hΦ x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨C.e (φ.1.symm y), ⟨_, rfl⟩, ?_⟩
    change Φ (C.e (φ.1.symm y)) = _
    rw [hΦ, LinearEquiv.apply_symm_apply]

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  choose A hA using exists_of_stab C
  choose B hB using exists_of_aut C
  have hspan := C.integral.isLattice.span_eq_top
  refine ⟨{ toFun := A, invFun := B, left_inv := fun γ => ?_, right_inv := fun φ => ?_,
            map_mul' := fun a b => ?_ }, hA⟩
  · refine Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
      (LinearMap.ext_on hspan ?_)))
    rintro _ ⟨x, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [hB, hA]
  · exact Subtype.ext (LinearEquiv.ext fun x => C.e_inj (by rw [hA, hB]))
  · refine Subtype.ext (LinearEquiv.ext fun x => C.e_inj ?_)
    change C.e ((A (a * b)).1 x) = C.e ((A a).1 ((A b).1 x))
    rw [hA, hA, hA]
    rfl

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ)

open Classical in
theorem pPart_add (y y' : Fin (j + j') → ℂ) : C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add (f := _), smul_sub]
  abel

open Classical in
theorem pPart_real_smul (r : ℝ) (y : Fin (j + j') → ℂ) : C.pPart R τ (r • y) = (r : ℂ) • C.pPart R τ y := by
  have h1 : ∀ y : Fin (j + j') → ℂ, C.perExt R (Pi.single τ (r • y)) = (r : ℂ) • C.perExt R (Pi.single τ y) := by
    intro y
    rw [Pi.single_smul, map_smul]
    ext i; simp
  have h2 : Complex.I • r • y = r • Complex.I • y := smul_comm _ _ _
  simp only [LatEmb.pPart, h2, h1, smul_sub]
  simp only [smul_smul]
  congr 2 <;> ring_nf

open Classical in
theorem pPart_I_smul (y : Fin (j + j') → ℂ) : C.pPart R τ (Complex.I • y) = Complex.I • C.pPart R τ y := by
  have h : Complex.I • Complex.I • y = -y := by simp [smul_smul]
  have h2 : C.perExt R (Pi.single τ (-y)) = - C.perExt R (Pi.single τ y) := by
    rw [Pi.single_neg, map_neg]
  simp only [LatEmb.pPart, h, h2]
  ext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (1 / 2 * (C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

def pPartL : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := C.pPart R τ
  map_add' := pPart_add C R τ
  map_smul' a y := by
    have ha : a • y = a.re • y + a.im • Complex.I • y := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      conv_lhs => rw [← Complex.re_add_im a]
      ring
    rw [ha, pPart_add, pPart_real_smul, pPart_real_smul, pPart_I_smul]
    simp only [RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im a]
    rw [add_smul, mul_smul]

theorem pPart_elim (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (v : Fin j → ℂ) (x : Fin j' → ℂ) :
    C.pPart R τ (A *ᵥ Sum.elim v x) =
      ∑ i, v i • C.pPart R τ (A *ᵥ Sum.elim (Pi.single i 1) 0) +
      ∑ b, x b • C.pPart R τ (A *ᵥ Sum.elim 0 (Pi.single b 1)) := by
  have hs : Sum.elim v x = ∑ i, v i • (Sum.elim (Pi.single i 1) 0 : Sg j j' → ℂ) +
      ∑ b, x b • (Sum.elim 0 (Pi.single b 1) : Sg j j' → ℂ) := by
    ext (i | b)
    · simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, Pi.single_apply]
  change pPartL C R τ _ = ∑ i, v i • pPartL C R τ _ + ∑ b, x b • pPartL C R τ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, Matrix.mulVec_add, map_add (f := _), Matrix.mulVec_sum, Matrix.mulVec_sum, map_sum, map_sum]
  simp [Matrix.mulVec_smul]

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealBasisFromLatticeBasis
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

theorem apply_eq_re (l : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    l z = (((l 1 : ℂ) - Complex.I * (l Complex.I : ℂ)) * z).re := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add (f := _), map_smul, map_smul]
  simp
  ring

theorem coeff_eq_zero {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (c : Ψ → ℂ) (h : ∀ x, ∑ τ, (c τ * s τ x).re = 0) (τ : Ψ) : c τ = 0 := by
  classical
  let m : Ψ ⊕ Ψ → (E →* ℂ) := Sum.elim (fun τ => (s τ : E →* ℂ))
    (fun τ => (((starRingEnd ℂ).comp (s τ) : E →+* ℂ) : E →* ℂ))
  have hm : Function.Injective m := by
    rintro (a | a) (b | b) hab
    · have : s a = s b := RingHom.ext fun x => DFunLike.congr_fun hab x
      rw [hs this]
    · exact absurd (RingHom.ext fun x => DFunLike.congr_fun hab x) (hc a b)
    · exact absurd (RingHom.ext fun x => (DFunLike.congr_fun hab x).symm) (hc b a)
    · have h1 : (starRingEnd ℂ).comp (s a) = (starRingEnd ℂ).comp (s b) :=
        RingHom.ext fun x => DFunLike.congr_fun hab x
      have : s a = s b := by
        ext x
        exact RingHom.injective (starRingEnd ℂ) (DFunLike.congr_fun h1 x)
      rw [hs this]
  have hli := (linearIndependent_monoidHom E ℂ).comp m hm
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (Sum.elim c (fun τ => (starRingEnd ℂ) (c τ))) (by
    funext x
    rw [Fintype.sum_sum_type]
    have h2 : ∑ τ, ((c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x)) = 0 := by
      have : ∀ τ, (c τ * s τ x) + (starRingEnd ℂ) (c τ * s τ x) = 2 * (((c τ * s τ x).re : ℝ) : ℂ) := by
        intro τ
        rw [Complex.add_conj]
        push_cast
        ring
      simp_rw [this]
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, h x]
      simp
    rw [Finset.sum_add_distrib] at h2
    simpa [m, Finset.sum_apply, map_mul] using h2)
  simpa using key (Sum.inl τ)

theorem span_eq_top {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] (N : ℕ) (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ')) :
    Submodule.span ℝ (Set.range fun (v : Fin N → E) => (fun τ i => s τ (v i) : Ψ → Fin N → ℂ)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨L, hL0, hL⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hL0
  let l : Fin N → Ψ → (ℂ →ₗ[ℝ] ℝ) := fun i τ =>
    L ∘ₗ LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ ∘ₗ LinearMap.single ℝ (fun _ : Fin N => ℂ) i
  have hl : ∀ i τ, l i τ = 0 := by
    intro i τ
    have hc0 := coeff_eq_zero s hs hc (fun τ => ((l i τ 1 : ℝ) : ℂ) - Complex.I * ((l i τ Complex.I : ℝ) : ℂ)) (by
      intro x
      simp_rw [← apply_eq_re]
      have hmem : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) ∈ LinearMap.ker L :=
        hL (Submodule.subset_span ⟨_, rfl⟩)
      have hsum : (fun τ j => s τ ((Pi.single i x : Fin N → E) j) : Ψ → Fin N → ℂ) =
          ∑ τ, LinearMap.single ℝ (fun _ : Ψ => Fin N → ℂ) τ
            (LinearMap.single ℝ (fun _ : Fin N => ℂ) i (s τ x)) := by
        funext τ' j
        rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single τ'
          (fun b _ hb => by simp [Pi.single_apply, hb.symm]) (by simp)]
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Pi.single_apply, hj]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, hsum, map_sum] at hmem
      exact hmem) τ
    have h1 : l i τ 1 = 0 := by
      have := congrArg Complex.re hc0
      simpa using this
    have h2 : l i τ Complex.I = 0 := by
      have := congrArg Complex.im hc0
      simpa using this
    apply LinearMap.ext
    intro z
    rw [apply_eq_re, h1, h2]
    simp
  refine LinearMap.pi_ext' fun τ => LinearMap.pi_ext' fun i => ?_
  exact hl i τ

def vecOf {E : Type} [Field E] {Ψ : Type} (N : ℕ) (s : Ψ → (E →+* ℂ)) :
    (Fin N → E) →+ (Ψ → Fin N → ℂ) where
  toFun v τ i := s τ (v i)
  map_zero' := by funext τ i; simp
  map_add' a b := by funext τ i; simp

theorem exists_basis {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] {g N : ℕ} (s : Ψ → (E →+* ℂ))
    (hs : Function.Injective s) (hc : ∀ τ τ', s τ ≠ (starRingEnd ℂ).comp (s τ'))
    (hg : g = Fintype.card Ψ * N) {Λ : Type} [AddCommGroup Λ] (e : Λ →+ (Fin N → E))
    (hspan : ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v)
    (lam : Module.Basis (Fin (2 * g)) ℤ Λ) :
    ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = s τ (e (lam k) i) := by
  classical
  have hlat : ∀ x : Λ, vecOf N s (e x) ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lam.sum_repr x, map_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hall : ∀ v, vecOf N s v ∈
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    intro v
    obtain ⟨k, x, hk, hx⟩ := hspan v
    have h2 := hlat x
    rw [hx, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hk)).1 h2
  have htop : (⊤ : Submodule ℝ (Ψ → Fin N → ℂ)) ≤
      Submodule.span ℝ (Set.range fun k => vecOf N s (e (lam k))) := by
    rw [← span_eq_top N s hs hc]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hall v
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Ψ → Fin N → ℂ) := by
    rw [Fintype.card_fin, Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, hg]
    ring
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ htop hcard, fun k τ i => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBas

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem exists_realBasis_of_latBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g N : ℕ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → g = Fintype.card Ψ * N → ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin N → E)), (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ lam : Module.Basis (Fin (2 * g)) ℤ Λ, ∃ bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin N → ℂ), ∀ k τ i, bas k τ i = embOf (σ τ) (e (lam k) i) := by
  intro E _ _ _ Ψ _ g N σ hσ hg Λ _ e hspan lam
  have hres : ∀ τ a, embOf (σ τ) (algebraMap (𝓞 E) E a) = σ τ a := fun τ a =>
    IsFractionRing.lift_algebraMap (intEmb_injective (σ τ)) a
  have hs : Function.Injective fun τ => embOf (σ τ) := by
    intro a b hab
    apply hσ.1
    ext x
    rw [← hres a x, ← hres b x]
    exact DFunLike.congr_fun hab _
  have hc : ∀ τ τ', embOf (σ τ) ≠ (starRingEnd ℂ).comp (embOf (σ τ')) := by
    intro τ τ' h
    have h1 : σ τ = (starRingEnd ℂ).comp (σ τ') := by
      ext x
      rw [RingHom.comp_apply, ← hres τ x, ← hres τ' x]
      exact DFunLike.congr_fun h _
    exact ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h1⟩
  exact LatBas.exists_basis (fun τ => embOf (σ τ)) hs hc hg e hspan lam

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

