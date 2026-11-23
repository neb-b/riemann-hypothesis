module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import ReciprocityTheory.SemistableReduction.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.IntCoresA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop

theorem sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [EuclideanSpace.norm_eq] at hu
    · exact h
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast Module.finrank_pos.ne'
  have htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsProbabilityMeasure (sphereProb n) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop
  set μ := sphereProb n with hμ
  set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n))
      continuous_const).measurableSet
  obtain ⟨hint, -⟩ := hSJ n a g u hg hu hgu
  have key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤
      (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) -
        Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by
    intro c hc
    have hgc : (MvPolynomial.C c * g).IsHomogeneous a := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg
    obtain ⟨-, hle⟩ := hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle
    have hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ =
        Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖ := by
      intro z
      by_cases hz : MvPolynomial.eval (spherePoint z) g = 0
      · have hzZ : z ∈ Z := hz
        simp [Set.indicator_apply, hzZ, hz]
      · have hzZ : z ∈ Zᶜ := hz
        rw [Set.indicator_of_mem hzZ, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
    have hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ =
        (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ := by
      simp_rw [hpt]
      rw [integral_add ((integrable_const _).indicator hZ.compl) hint,
        integral_indicator_const _ hZ.compl, smul_eq_mul]
      try rfl
    have hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal := by
      rw [prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ =
        Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]
    rw [hI, hcomp, hL] at hle
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K := ⟨_, key⟩
  by_contra hne
  have hp : 0 < (μ Z).toReal := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have h1 := hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp] at h1
  have h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1 := by
    field_simp
  linarith [le_abs_self K]

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
section
namespace ReciprocityTheory.MultiplicativeHeights

theorem integralClosureRank (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]

open MvPolynomial

theorem algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by
  classical
  letI := residueAlgebra V (algebraMap F₁ F₂)
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  by_contra hne
  have hS : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m₀, hm₀, hmax⟩ := p.support.exists_max_image
    (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS
  have hc : p.coeff m₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc

  have hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂) := by
    intro m
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hm : m ∈ p.support
    · calc ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)
          ≤ ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) := by
            gcongr
            exact hmax m hm
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  have hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈
      Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    exact ⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩
  obtain ⟨qV, hqV⟩ := hpp
  have hcoeff : qV.coeff m₀ = 1 := by
    have e := congrArg (AddMonoidAlgebra.coeff · m₀) hqV
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at e
    exact Subtype.ext e
  have h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0 := by
    apply Subtype.ext
    have e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂))
        (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0 := by
      rw [map_mul, hp, mul_zero]
    rw [MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map] at e1
    have e2 := MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV
    have e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) =
        (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype := RingHom.ext fun _ => rfl
    rw [e3] at e2
    exact e2.trans e1

  have h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i))
      (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e4 := MvPolynomial.eval₂_comp_left (IsLocalRing.residue V)
      (comapInclusion V (algebraMap F₁ F₂)) y qV
    rw [h0, map_zero] at e4
    have e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) =
        (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r
    rw [e5]
    exact e4.symm
  have e6 := congrArg (AddMonoidAlgebra.coeff · m₀) (hx _ h1)
  rw [MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero] at e6
  exact one_ne_zero e6

theorem residueTrdegLe : TRStatement := by
  intro F₁ F₂ _ _ _ V
  letI := residueAlgebra V (algebraMap F₁ F₂)
  unfold Algebra.trdeg
  refine ciSup_le' fun s => ?_
  have hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a :=
    fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)
  choose y hy using hy
  have hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
      (fun a => IsLocalRing.residue V (y a)) := by
    have : (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V) :=
      funext hy
    rw [this]
    exact s.2
  exact (algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg

theorem integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.LatSemiSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def UnipotentStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (γ : Matrix (Fin r) (Fin r) K)
    (Q : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) →
    (Real.exp (1 / 3) + 1) * r < g → (∀ σ, (Q σ).det ≠ 0) →
    (∀ σ (u : Fin r → ℂ), normSq ((Q σ * γ.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * normSq u) →
    (γ - 1) ^ r = 0 ∧ ∀ σ, ∑ a, ∑ b, ‖(Q σ * (γ.map σ - 1) * (Q σ)⁻¹) a b‖ ^ 2 < 1

def hq {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) : ℝ := (star u ⬝ᵥ (H *ᵥ u)).re

structure Majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) where

  H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ σ, (H σ).PosDef
  major : ∀ σ, H σ * (S.G.map σ)⁻¹ * H σ = S.G.map σ
  conj_compat : ∀ σ, H ((starRingEnd ℂ).comp σ) = (H σ).map (starRingEnd ℂ)

def gramC {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (b j))

def IsKBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) : Prop :=
  (∀ i, b i ∈ B) ∧ LinearIndependent K b ∧ ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)

def latDeg {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℝ :=
  Real.log ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re

def IsSemistableZero {K : Type} [Field K] [NumberField K] {r : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  (∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn L b → latDeg H L b = 0) ∧
  ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L →
    ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg H B b ≤ 0

def gramX {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (c j))

def quotGramC {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin m) (Fin m) ℂ :=
  gramC H σ c - gramX H σ c b * (gramC H σ b)⁻¹ * gramX H σ b c

def satSub {K : Type} [Field K] [NumberField K] {r k : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin r → K) :=
  L ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def quotDeg {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : ℝ :=
  Real.log ((satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re

def DegAddStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k m : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K),
    (∀ σ, (H σ).PosDef) → L.FG → (∀ i, b i ∈ L) → (∀ j, c j ∈ L) →
    LinearIndependent K (Fin.append b c) →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))) →
    latDeg H L (Fin.append b c) = latDeg H (satSub L b) b + quotDeg H L b c

def SemiPointStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L

def SemistableStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L ∧
      ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
        (∀ σ (u : Fin r → ℂ), u ≠ 0 → hq (M.H σ) (N.map σ *ᵥ u) < hq (M.H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.LemmaH
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix InnerProductSpace

theorem exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by
  classical
  let std := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  have hstd : std.toBasis.toMatrix f = x := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, f, std]
  have hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j := by
    intro j
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [colNormSq, f]
  refine ⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩
  · simpa [OrthonormalBasis.coe_toBasis] using OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e
  · exact gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f
  · rw [Module.Basis.toMatrix_mul_toMatrix, hstd]
  · intro j
    rw [← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    have h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖ := by
      calc ‖inner ℂ (e j) (f j)‖ ≤ ‖e j‖ * ‖f j‖ := norm_inner_le_norm _ _
        _ = ‖f j‖ := by rw [e.orthonormal.1 j, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]

theorem lemmaH_holds : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hC0 : 0 ≤ C := by
    have h1 := hC (fun s => 1) (fun s => one_mem _)
    exact (norm_nonneg _).trans h1
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)

end ReciprocityTheory.MultiplicativeHeights
end

