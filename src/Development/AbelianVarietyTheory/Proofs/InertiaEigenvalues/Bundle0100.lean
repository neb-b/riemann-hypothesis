module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianPairNormProperties
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.norm_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) := by
  intro F E _ _ _ _ _ A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [Et.NL]
    rw [Algebra.norm_algebraMap_of_basis b]
    simp
  · intro y y'
    simp only [Et.NL]
    exact map_mul (Algebra.norm A.K) y y'
  · intro t
    apply hinj
    rw [hN, map_one]
    exact t.prop.2
  · intro y hy
    have h := hy.map (algebraMap A.K A.L)
    rw [hN] at h
    exact isUnit_of_mul_isUnit_left h
  · intro y hy
    exact hy.map (Algebra.norm A.K)

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
section
set_option linter.style.haveILetI false

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise

namespace GlobalTheory.InertiaLift

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G F Ω} (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr ((apply_mem_iff_of_mem_Dec hσ s).mpr
      (mem_of_isIntegral_int A hs))) ?_
    rw [← not_lt, valuation_apply_lt_one_iff hσ, hs1]
    exact lt_irrefl 1
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : σ s * (σ x - x) = (σ t - t) + x * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (σ s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_add_lt _ (h t ht) ?_
    rw [Valuation.map_mul, Valuation.map_sub_swap]
    calc A.valuation x * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
          mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact h s hs
  rwa [Valuation.map_mul, hσs, one_mul] at hv

theorem exists_smul_eq {A A' : ValuationSubring Ω}
    (h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, ∀ y, A'.valuation (g y) < 1 ↔ A.valuation y < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow,
        mem_primeBelow]
      exact h x)
  have e : g • A = A' := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
    rw [primeBelow_smul, hg]
  refine ⟨g, fun y => ?_⟩
  rw [← e, smul_valuation_lt_one_iff]
  have : (g⁻¹ : Ω ≃ₐ[F] Ω) (g y) = y := g.symm_apply_apply y
  rw [this]

noncomputable def intEquiv (s : Ω ≃+* Ω) : IntCl F Ω ≃+* IntCl F Ω where
  toFun b := ⟨s b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.toRingHom.toIntAlgHom)⟩
  invFun b := ⟨s.symm b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.symm.toRingHom.toIntAlgHom)⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b)
  right_inv b := Subtype.ext (s.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul s (a : Ω) b)
  map_add' a b := Subtype.ext (map_add s (a : Ω) b)

theorem exists_congr {A : ValuationSubring Ω} (s : Ω ≃+* Ω)
    (hs : ∀ y, A.valuation (s y) < 1 ↔ A.valuation y < 1)
    (h : ∀ x : 𝓞 F, A.valuation (s (algebraMap F Ω x) - algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, g ∈ Dec (F := F) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (g b - s b) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  have hmap : Q = Q.map (intEquiv (F := F) s : IntCl F Ω →+* IntCl F Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow, ← hs ((intEquiv (F := F) s).symm b)]
    have : s (((intEquiv (F := F) s).symm b : IntCl F Ω) : Ω) = b := s.apply_symm_apply b
    rw [this]
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (IntCl F Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intEquiv (F := F) s) hmap) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk Q (intEquiv (F := F) s (algebraMap _ _ x)) =
        Ideal.Quotient.mk Q (algebraMap _ _ x)
      rw [Ideal.Quotient.eq]
      exact h x)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) (Q.under (𝓞 F)) Q φ
  have hσQ' : σ • Q = Q := hσQ
  refine ⟨σ, ?_, fun b hb => ?_⟩
  · refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  · let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    have h1 : Ideal.Quotient.mk Q (σ • b') = Ideal.Quotient.mk Q (intEquiv (F := F) s b') :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b')
    rw [Ideal.Quotient.eq] at h1
    exact h1

omit [IsAlgClosure F Ω] in
theorem mem_Dec_of_lt {A : ValuationSubring Ω} {σ : G F Ω}
    (h : ∀ y, A.valuation (σ y) < 1 ↔ A.valuation y < 1) : σ ∈ Dec (F := F) A := by
  have key : ∀ y, y ∈ A ↔ (y = 0 ∨ ¬ A.valuation y⁻¹ < 1) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
      rw [← A.valuation_le_one_iff, map_inv₀, inv_lt_one₀ h0, not_lt]
      simp [hy]
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, key, key y,
    ← h, map_inv₀ σ, mul_inv_apply, map_eq_zero_iff _ (σ⁻¹ : G F Ω).injective]

theorem exists_mem_Ine_lift (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω]
    [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 → A.valuation ((algebraMap M Ω (τ x)) - (algebraMap M Ω x)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  have hint : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (x : M)) ≤ 1 := fun x =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom))
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x (hint x)
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - (algebraMap M Ω (x : M))) < 1
    rw [h₂]
    exact h x (hint x))
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, mem_Ine_of_integral (mem_Dec_of_lt fun y => ?_)
    fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  intro Ω _ _ _ _ _ A _ M _ _ τ h _
  have hst : @IsScalarTower ℚ M Ω (DivisionRing.toRatAlgebra (R := M)).toSMul
      (inferInstance : Algebra M Ω).toSMul (‹Algebra ℚ Ω›).toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℚ M Ω _ _ _ DivisionRing.toRatAlgebra _ _
      (Subsingleton.elim _ _)
  have e : (DivisionRing.toRatAlgebra : Algebra ℚ M) = M.algebra' := Subsingleton.elim _ _
  have hfd : @FiniteDimensional ℚ M _ _ (DivisionRing.toRatAlgebra (R := M)).toModule := by
    rw [e]; assumption
  exact @exists_mem_Ine_lift ℚ Ω _ _ _ _ _ A M _ DivisionRing.toRatAlgebra _ hst hfd _ τ h

end GlobalTheory.InertiaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.InertiaAlmostAll

theorem val_le_one_of_isIntegral {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {w : Ω}
    (hw : IsIntegral ℤ w) : B.valuation w ≤ 1 := by
  have h : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [B.valuation_le_one_iff, ← hy]
  exact y.2

theorem exists_int_mul (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple
  exact ⟨c, hc, by simpa [zsmul_eq_mul] using h⟩

theorem finite_mem (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(c : 𝓞 F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv

theorem finite_moves (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (x : Ω) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ τ ∈ Ine (F := F) B, τ x ≠ x}.Finite := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨c₀, hc₀, hx⟩ := exists_int_mul F x
  set a : Ω := (c₀ : Ω) * x with ha
  choose c hc hci using fun β : Ω => exists_int_mul F (β - a)⁻¹
  have hfin : ((minpoly F a).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  refine (hfin.biUnion (t := fun β => {v : HeightOneSpectrum (𝓞 F) | (c β : 𝓞 F) ∈ v.asIdeal})
    fun β _ => finite_mem F (hc β)).subset ?_
  rintro v ⟨B, hB, τ, hτ, hne⟩
  have hne' : τ a - a ≠ 0 := by
    rw [ha, map_mul, map_intCast, ← mul_sub]
    exact mul_ne_zero (by exact_mod_cast hc₀) (sub_ne_zero.mpr hne)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨τ a, ?_, ?_⟩
  · rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [← hB]
    have h1 := hτ.2 a (val_le_one_of_isIntegral B hx)
    have h2 := val_le_one_of_isIntegral B (hci (τ a))
    have e : algebraMap F Ω (((c (τ a) : ℤ) : 𝓞 F) : F)
        = ((c (τ a) : Ω) * (τ a - a)⁻¹) * (τ a - a) := by
      rw [inv_mul_cancel_right₀ hne']
      simp
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h2 zero_le h1

theorem finite_ramified (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  let b := Module.finBasis F L
  refine (Set.finite_iUnion fun i => finite_moves F Ω (b i : Ω)).subset ?_
  rintro v ⟨B, hB, hn⟩
  by_contra hv
  apply hn
  intro τ hτ
  have hb : ∀ i, τ (b i : Ω) = b i := by
    intro i
    by_contra h
    exact hv (Set.mem_iUnion.mpr ⟨i, B, hB, τ, hτ, h⟩)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have : τ.toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun this ⟨y, hy⟩

end GlobalTheory.InertiaAlmostAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsQuotSqFiniteEtaleHermitianPair
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem finite_units_quot_sq_normed (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (R : Type) [NormedCommRing R] [Nontrivial R] [NormedAlgebra F R]
    [Module.Finite F R] (hR : ∀ x : R, x ≠ 0 → IsUnit x) :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  obtain ⟨-, hsq⟩ := isOpenUnits_and_eventually_sq_normed F R
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsq
  obtain ⟨b, hb0, hb1⟩ := NormedField.exists_norm_lt_one F
  have hρ2 : 0 < ‖b‖ ^ 2 := by positivity
  have : ProperSpace R := FiniteDimensional.proper F R
  let C : Set R := {x | ‖b‖ ^ 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
  have hCc : IsCompact C := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : R)) (r := 1)).subset
        (fun x hx => by simpa using hx.2)
  have hCu : ∀ c ∈ C, IsUnit c := fun c hc => hR c (by
    intro h
    have h1 := hc.1
    rw [h, norm_zero] at h1
    linarith)
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover
    (fun c => {x : R | dist (x * Ring.inverse c) 1 < ε}) (by
      intro c hc
      apply IsOpen.mem_nhds
      · exact isOpen_lt (by fun_prop) continuous_const
      · simp [Ring.mul_inverse_cancel _ (hCu c hc), hε])
  let f : R → Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range := fun x =>
    if h : IsUnit x then QuotientGroup.mk h.unit else 1
  have hsurj : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)) ⊆ f '' (t : Set R) := by
    rintro q -
    induction q using QuotientGroup.induction_on with | H u => ?_
    have hu0 : 0 < ‖(u : R)‖ := norm_pos_iff.mpr u.ne_zero
    have hy : 1 < (‖b‖ ^ 2)⁻¹ := (one_lt_inv₀ hρ2).mpr (by nlinarith [norm_nonneg b])
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu0 hy
    have hb0' : b ≠ 0 := norm_pos_iff.mp hb0
    have hβ0 : b ^ (n + 1) ≠ 0 := zpow_ne_zero _ hb0'
    have hnv : ‖(b ^ (n + 1)) ^ 2 • (u : R)‖ = ‖(u : R)‖ / ((‖b‖ ^ 2)⁻¹) ^ (n + 1) := by
      rw [norm_smul, norm_pow, norm_zpow, _root_.inv_zpow, div_inv_eq_mul, mul_comm, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul]
      rw [mul_comm (n + 1)]
    have hv : (b ^ (n + 1)) ^ 2 • (u : R) ∈ C := by
      have hpos : 0 < ((‖b‖ ^ 2)⁻¹) ^ n := zpow_pos (by positivity) n
      refine ⟨?_, ?_⟩
      · rw [hnv, zpow_add₀ (by positivity), zpow_one, le_div_iff₀ (by positivity)]
        calc ‖b‖ ^ 2 * (((‖b‖ ^ 2)⁻¹) ^ n * (‖b‖ ^ 2)⁻¹) = ((‖b‖ ^ 2)⁻¹) ^ n := by field_simp
          _ ≤ ‖(u : R)‖ := hn1.le
      · rw [hnv, div_le_one (by positivity)]
        exact hn2
    obtain ⟨c, hct, hcv⟩ := Set.mem_iUnion₂.mp (hcov hv)
    have hcu := hCu c (htC c hct)
    obtain ⟨s, hs⟩ := hball hcv
    have hsU : IsUnit s := by
      have : IsUnit (s ^ 2) := by
        have hic : Ring.inverse c = ↑(hcu.unit⁻¹) := by rw [← Ring.inverse_unit, IsUnit.unit_spec]
        rw [hs, Algebra.smul_def, hic]
        exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hβ0)).map (algebraMap F R) |>.mul u.isUnit).mul
          (hcu.unit⁻¹).isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    refine ⟨c, hct, ?_⟩
    simp only [f, dif_pos hcu]
    rw [QuotientGroup.eq, MonoidHom.mem_range]
    let bu : Rˣ := Units.map (algebraMap F R).toMonoidHom (Units.mk0 _ hβ0)
    have hs' : hsU.unit ^ 2 = bu ^ 2 * u * hcu.unit⁻¹ := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, bu, Units.coe_map,
        Units.val_mk0]
      rw [hs, ← Ring.inverse_unit, IsUnit.unit_spec, Algebra.smul_def, map_pow]
      rfl
    refine ⟨hsU.unit * bu⁻¹, ?_⟩
    rw [powMonoidHom_apply, mul_pow, inv_pow, hs']
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  have hfin : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)).Finite :=
    (t.finite_toSet.image f).subset hsurj
  exact Set.finite_univ_iff.mp hfin

end GlobalTheory

namespace GlobalTheory

theorem finite_units_quot_sq_field (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (L : Type) [Field L] [Algebra F L] [Module.Finite F L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  classical
  let b := Module.finBasis F L
  let : NormedRing (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing L := NormedCommRing.induced L _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F L _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F L _ (Algebra.leftMulMatrix b)
  exact @finite_units_quot_sq_normed F _ _ _ _ L N inferInstance A ‹_› (fun x hx => hx.isUnit)

theorem finite_units_quot_sq_reduced (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (K : Type) [CommRing K] [Algebra F K] [Module.Finite F K]
    [IsReduced K] : Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  letI (I : MaximalSpectrum K) : Field (K ⧸ I.asIdeal) :=
    @Ideal.Quotient.field _ _ I.asIdeal I.isMaximal
  have hfin (I : MaximalSpectrum K) :
      Finite ((K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) :=
    finite_units_quot_sq_field F (K ⧸ I.asIdeal)
  let φ : Kˣ →* ∀ I : MaximalSpectrum K,
      (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hker : φ.ker = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hu
      have hI (I : MaximalSpectrum K) : ∃ s : (K ⧸ I.asIdeal)ˣ,
          s ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u := by
        have := congrFun hu I
        change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u : (K ⧸ I.asIdeal)ˣ) :
          (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1 at this
        rw [QuotientGroup.eq_one_iff] at this
        obtain ⟨s, hs⟩ := this
        exact ⟨s, hs⟩
      choose s hs using hI
      let e := IsArtinianRing.equivPi K
      let x : K := e.symm fun I => (s I : K ⧸ I.asIdeal)
      let y : K := e.symm fun I => ((s I)⁻¹ : (K ⧸ I.asIdeal)ˣ)
      have hxy : x * y = 1 := e.injective (by
        rw [map_mul, map_one]
        funext I
        simp [x, y])
      refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
      ext
      apply e.injective
      funext I
      have := congrArg Units.val (hs I)
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
      simp [x, this] <;> rfl
    · rintro ⟨w, rfl⟩
      funext I
      change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom (w ^ 2) : (K ⧸ I.asIdeal)ˣ) :
        (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1
      rw [QuotientGroup.eq_one_iff, map_pow]
      exact ⟨_, rfl⟩
  have := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  rw [hker] at this
  exact this

theorem Et.finite_units_quot_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E),
    Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  have : LocallyCompactSpace F := hU.lcF
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  exact finite_units_quot_sq_reduced F A.K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  first | exact @GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | exact GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | (intros; apply GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv <;> assumption)
end

