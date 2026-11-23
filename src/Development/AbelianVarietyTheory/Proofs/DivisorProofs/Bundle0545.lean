module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import GroundTheory.AutomorphicForms.StableConjCyclic
public import GroundTheory.Brauer.Degree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
section
namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem isUnit_of_isUnit_mulLeft {k A : Type} [Field k] [Ring A] [Algebra k A] (x : A)
    (h : IsUnit (LinearMap.mulLeft k x)) : IsUnit x := by
  set u := h.unit with hu
  set y : A := ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1 with hy
  have hxy : x * y = 1 := by
    change LinearMap.mulLeft k x (((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1) = 1
    rw [← Module.End.mul_apply]
    have : LinearMap.mulLeft k x = (u : Module.End k A) := rfl
    rw [this, Units.mul_inv, Module.End.one_apply]
  have hly : LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) := by
    have e : (u : Module.End k A) * LinearMap.mulLeft k y = 1 := by
      change LinearMap.mulLeft k x * LinearMap.mulLeft k y = 1
      ext z
      simp [← mul_assoc, hxy]
    calc LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) *
          ((u : Module.End k A) * LinearMap.mulLeft k y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, mul_one]
  have hyx : y * x = 1 := by
    have := congrArg (fun f : Module.End k A => f 1) (Units.inv_mul u)
    simp only [← hly] at this
    change y * (x * 1) = 1 at this
    rwa [mul_one] at this
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

theorem baseChange_mulLeft {k A K : Type} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (a : A) : (LinearMap.mulLeft k a).baseChange K = LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] a) := by
  ext x
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem exists_isUnit_mem_of_span_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Field K] [Algebra k K] (V : Submodule k A) (u : K ⊗[k] A)
    (hu : u ∈ Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A))) (hunit : IsUnit u) :
    ∃ x ∈ V, IsUnit x := by
  classical
  set r := finrank k V
  let b : Basis (Fin r) k V := Module.finBasis k V
  set m := finrank k A
  let bA : Basis (Fin m) k A := Module.finBasis k A
  let M : Fin r → Matrix (Fin m) (Fin m) k := fun i => LinearMap.toMatrix bA bA (LinearMap.mulLeft k (b i : A))
  set D : MvPolynomial (Fin r) k := (∑ i, (MvPolynomial.X i : MvPolynomial (Fin r) k) •
      (M i).map (MvPolynomial.C : k →+* MvPolynomial (Fin r) k)).det with hD
  have key : ∀ {T : Type} [CommRing T] (ψ : MvPolynomial (Fin r) k →+* T),
      ψ D = (∑ i, ψ (MvPolynomial.X i) • (M i).map (ψ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin r) k))).det := by
    intro T _ ψ
    rw [hD, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext p q
    simp [Matrix.sum_apply]

  have hlin : ∀ t : Fin r → k, ∑ i, t i • M i =
      LinearMap.toMatrix bA bA (LinearMap.mulLeft k (∑ i, t i • (b i : A))) := by
    intro t
    have : LinearMap.mulLeft k (∑ i, t i • (b i : A)) = ∑ i, t i • LinearMap.mulLeft k (b i : A) := by
      ext z; simp [Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp [M, map_smul]

  have hD0 : D ≠ 0 := by
    have hspan : Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A)) ≤
        Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      have hrep := b.sum_repr ⟨a, ha⟩
      have : (1 : K) ⊗ₜ[k] a = ∑ i, (algebraMap k K (b.repr ⟨a, ha⟩ i)) • ((1 : K) ⊗ₜ[k] (b i : A)) := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : V) : A) from rfl, ← hrep]
        simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
          algebraMap_smul]
      show (1 : K) ⊗ₜ[k] a ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A))
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hspan hu)
    intro h0
    have h1 := key (MvPolynomial.eval₂Hom (algebraMap k K) s)
    rw [h0, map_zero] at h1
    have hmat : ∑ i, (MvPolynomial.eval₂Hom (algebraMap k K) s) (MvPolynomial.X i) •
        (M i).map ((MvPolynomial.eval₂Hom (algebraMap k K) s).comp MvPolynomial.C) =
        LinearMap.toMatrix (Algebra.TensorProduct.basis K bA) (Algebra.TensorProduct.basis K bA)
          (LinearMap.mulLeft K u) := by
      rw [← hs]
      have : LinearMap.mulLeft K (∑ i, s i • (1 : K) ⊗ₜ[k] (b i : A)) =
          ∑ i, s i • LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] (b i : A)) := by
        ext z; simp [Finset.sum_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← baseChange_mulLeft, LinearMap.toMatrix_baseChange]
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_comp_C]
    rw [hmat, LinearMap.det_toMatrix] at h1
    have hu' : IsUnit (LinearMap.mulLeft K u) := by
      obtain ⟨w, rfl⟩ := hunit
      refine ⟨⟨LinearMap.mulLeft K (w : K ⊗[k] A), LinearMap.mulLeft K ((w⁻¹ : (K ⊗[k] A)ˣ) : K ⊗[k] A),
        ?_, ?_⟩, rfl⟩ <;> ext z <;> simp [← mul_assoc]
    have := (LinearMap.isUnit_iff_isUnit_det _).1 hu'
    rw [← h1] at this
    exact not_isUnit_zero this

  obtain ⟨t, ht⟩ : ∃ t : Fin r → k, MvPolynomial.eval t D ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hD0 (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  refine ⟨∑ i, t i • (b i : A), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2, ?_⟩
  apply isUnit_of_isUnit_mulLeft (k := k)
  rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix bA, ← hlin, isUnit_iff_ne_zero]
  rw [key] at ht
  convert ht using 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_X]
  congr 1
  ext p q
  simp

end GlobalTheory.LKInv

namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem exists_unit_conj_of_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Field K] [Algebra k K] (x₀ x : A) (w : (K ⊗[k] A)ˣ)
    (hw : (w : K ⊗[k] A) * ((1 : K) ⊗ₜ[k] x₀) = ((1 : K) ⊗ₜ[k] x) * w) :
    ∃ g : Aˣ, (g : A) * x₀ = x * g := by
  let a : A →ₗ[k] A := LinearMap.mulRight k x₀ - LinearMap.mulLeft k x
  let a' : K ⊗[k] A →ₗ[K] K ⊗[k] A :=
    LinearMap.mulRight K ((1 : K) ⊗ₜ[k] x₀) - LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] x)
  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange k K A (K ⊗[k] A) Unit
    (TensorProduct.mk k K A 1) (TensorProduct.isBaseChange k A K) (fun _ => a) (fun _ => a')
    (fun _ v => by simp [a, a', Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).2
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  have hwmem : (w : K ⊗[k] A) ∈ LinearMap.ker a' := by
    rw [LinearMap.mem_ker]
    simp [a', hw]
  rw [hbc] at hwmem
  obtain ⟨y, hyV, hyu⟩ := exists_isUnit_mem_of_span_baseChange (K := K) (LinearMap.ker a)
    (w : K ⊗[k] A) hwmem w.isUnit
  refine ⟨hyu.unit, ?_⟩
  rw [LinearMap.mem_ker] at hyV
  simpa [a, sub_eq_zero] using hyV

theorem charpoly_eq_map_minpoly {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    {n : ℕ} (e : AlgebraicClosure F ⊗[F] B ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F))
    (y : B) (hsep : (minpoly F y).Separable) (hdeg : (minpoly F y).natDegree = n) :
    (e ((1 : AlgebraicClosure F) ⊗ₜ[F] y)).charpoly = (minpoly F y).map (algebraMap F (AlgebraicClosure F)) := by
  set K := AlgebraicClosure F
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have hmap0 : (minpoly F y).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero hyi)
  have hzdeg : (minpoly K z).natDegree = n := by
    refine le_antisymm ?_ (hdeg ▸ hge)
    calc (minpoly K z).natDegree ≤ ((minpoly F y).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap0
      _ = n := by rw [natDegree_map, hdeg]
  have hzeq : minpoly K z = (minpoly F y).map (algebraMap F K) := by
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
      (by rw [natDegree_map, hdeg, hzdeg])
    rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]
  set N := e z with hN
  have hmN : minpoly K N = minpoly K z := minpoly.algEquiv_eq e z
  have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
  rw [hmN] at hd
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hd
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hzdeg])
  rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul, hzeq]

theorem exists_unit_conj_of_minpoly_eq (F B : Type) [Field F] [Infinite F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ)
    (hn : Module.finrank F B = n ^ 2) (x₀ x : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (hmin : minpoly F x = minpoly F x₀) :
    ∃ g : Bˣ, (g : B) * x₀ = x * g := by
  classical
  obtain ⟨m, hm0, hmB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hmn : m = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hmB.symm.trans hn)
  subst hmn
  set K := AlgebraicClosure F
  set N₀ := e ((1 : K) ⊗ₜ[F] x₀) with hN₀
  set N := e ((1 : K) ⊗ₜ[F] x) with hN
  have hc₀ := charpoly_eq_map_minpoly e x₀ hsep hdeg
  have hc := charpoly_eq_map_minpoly e x (hmin ▸ hsep) (hmin ▸ hdeg)
  rw [hmin] at hc
  have hsepK : (Matrix.toLin' N₀).charpoly.Separable := by
    rw [Matrix.charpoly_toLin', hc₀]; exact hsep.map
  obtain ⟨e', he'⟩ := GroundTheory.Automorphic.exists_conj_of_charpoly_eq hsepK
    (f' := Matrix.toLin' N) (by rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', hc₀, hc])
  set P := LinearMap.toMatrix' (e' : (Fin m → K) →ₗ[K] (Fin m → K)) with hP
  set Q := LinearMap.toMatrix' (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hPN : P * N₀ = N * P := by
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ Matrix.toLin' N₀ =
        Matrix.toLin' N ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) :=
      LinearMap.ext fun v => he' v
    have h2 := congrArg LinearMap.toMatrix' this
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at h2

  set w : (K ⊗[F] B)ˣ := ⟨e.symm P, e.symm Q, by rw [← map_mul, hPQ, map_one],
    by rw [← map_mul, hQP, map_one]⟩ with hw
  refine exists_unit_conj_of_baseChange x₀ x w ?_
  apply e.injective
  rw [map_mul, map_mul]
  simp only [hw, Units.val_mk, AlgEquiv.apply_symm_apply]
  rw [← hN₀, ← hN, hPN]

end GlobalTheory.LKInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTorsionFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionFamily

section General

variable {S : Scheme.{0}}

noncomputable def torsionLift (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    T ⟶ torsion G n :=
  pullback.lift f (toUnit T) (by rw [GlobalTheory.GrpTangent.comp_mulN, hf, Hom.one_def])

theorem torsionLift_ι (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    torsionLift G f n hf ≫ torsion.ι G n = f :=
  pullback.lift_fst _ _ _

theorem torsion_ι_pow (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GlobalTheory.GrpTangent.comp_mulN, Hom.one_def]
  exact pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))

end General

end GlobalTheory.TorsionFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedFieldOfInertiaProperty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaGood

theorem not_dvd_discr_of_inertia_fix (E N : Type) [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra E N] [IsGalois ℚ N] (q : ℕ) (hq : q.Prime)
    (h : ∀ Q : Ideal (𝓞 N), Q.IsMaximal → (q : 𝓞 N) ∈ Q → ∀ τ : N ≃ₐ[ℚ] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) →
      ∀ y : E, τ (algebraMap E N y) = algebraMap E N y) : ¬ (q : ℤ) ∣ discr E := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hqz).2 fun P hP hqP => ?_
  have hqP' : (q : 𝓞 E) ∈ P := by simpa using hqP
  have hne : P ≠ ⊥ := fun h0 => by
    rw [h0, Ideal.mem_bot] at hqP'
    exact hq.ne_zero (Nat.cast_eq_zero.1 hqP')
  have hPm : P.IsMaximal := hP.isMaximal hne
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P
  have hqQ : (q : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q P _).1 hqP'
    rwa [map_natCast] at this
  have h1 := (GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix ℚ E N Q).2 (h Q hQ hqQ)
  rw [← Ideal.over_def Q P] at h1
  have hu : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 ℚ)) :=
    (not_dvd_discr_iff_forall_mem ℚ (𝓞 ℚ) hqz).1 (by
      rw [Rat.numberField_discr]; exact hqz.not_dvd_one) _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast]; exact hqP)
  have h2 : P.ramificationIdx ℤ = (P.under (𝓞 ℚ)).ramificationIdx ℤ * P.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower (P.under (𝓞 ℚ)) P
  rw [h1, Ideal.ramificationIdx_eq_one (P.under (𝓞 ℚ)) ℤ, Nat.mul_one] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2

theorem exists_unramified_field_good : ∀ (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] (q : ℕ), q.Prime → ∀ Good : (ℂ ≃+* ℂ) → Prop, (∀ τ τ', Good τ → Good τ' → Good (τ.trans τ')) → (∀ (τ : ℂ ≃+* ℂ) (𝔮 : Ideal (𝓞 N)), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → Good τ) → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F', τ x = x) → Good τ := by
  intro N _ _ q hq Good hmul hin
  have : Countable N := (Module.finBasis ℚ N).equivFun.injective.countable
  let T : Set (N ≃ₐ[ℚ] N) :=
    {σ | ∃ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal ∧ (q : 𝓞 N) ∈ 𝔮 ∧ σ ∈ 𝔮.inertia (N ≃ₐ[ℚ] N)}
  let S : (N ≃ₐ[ℚ] N) → Prop := fun σ => ∀ τ : ℂ ≃+* ℂ, (∀ x : N, τ (x : ℂ) = (σ x : ℂ)) → Good τ
  have hT : ∀ σ ∈ T, S σ := by
    rintro σ ⟨𝔮, h1, h2, h3⟩ τ hτ
    exact hin τ 𝔮 h1 h2 fun x => ⟨σ • x, (hτ x).symm, AddSubgroup.mem_inertia.1 h3 x⟩
  have h1 : (1 : N ≃ₐ[ℚ] N) ∈ T := by
    have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
    have : (Ideal.span {(q : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) (Ideal.span {(q : ℤ)})
    refine ⟨Q, hQ, ?_, one_mem _⟩
    have := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)}) _).1 (Ideal.mem_span_singleton_self _)
    rwa [map_natCast] at this
  have hSmul : ∀ σ σ', S σ → S σ' → S (σ * σ') := by
    intro σ σ' hσ hσ' τ hτ
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N (algebraMap N ℂ)
      ((algebraMap N ℂ).comp (σ' : N →+* N))
    have hτ'' : ∀ x : N, τ' (x : ℂ) = (σ' x : ℂ) := hτ'
    have g2 : Good (τ'.symm.trans τ) := hσ _ fun x => by
      have e : τ'.symm (x : ℂ) = (σ'.symm x : ℂ) := by
        rw [RingEquiv.symm_apply_eq, hτ'', AlgEquiv.apply_symm_apply]
      rw [RingEquiv.trans_apply, e, hτ, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    have e : τ'.trans (τ'.symm.trans τ) = τ := RingEquiv.ext fun z => by simp
    exact e ▸ hmul _ _ (hσ' τ' hτ'') g2
  have hIS : ∀ σ ∈ Subgroup.closure T, S σ := fun σ hσ =>
    Subgroup.closure_induction'' (p := fun σ _ => S σ) hT
      (fun x ⟨𝔮, a, b, c⟩ => hT _ ⟨𝔮, a, b, inv_mem c⟩) (hT _ h1) (fun x y _ _ => hSmul x y) hσ
  let F₀ := IntermediateField.fixedField (Subgroup.closure T)
  have : NumberField (IntermediateField.lift F₀) :=
    have : FiniteDimensional ℚ (IntermediateField.lift F₀) :=
      (IntermediateField.liftAlgEquiv F₀).toLinearEquiv.finiteDimensional
    ⟨⟩
  refine ⟨IntermediateField.lift F₀, this, ?_, fun τ hτ => ?_⟩
  · rw [← discr_eq_discr_of_algEquiv F₀ (IntermediateField.liftAlgEquiv F₀)]
    exact not_dvd_discr_of_inertia_fix F₀ N q hq fun Q a b σ c y =>
      (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ
        (Subgroup.subset_closure ⟨Q, a, b, AddSubgroup.mem_inertia.2 c⟩)
  · let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) fun x => by simp
    have hr : ∀ x : N, τ (x : ℂ) = (τa.restrictNormal N x : ℂ) := fun x =>
      (AlgEquiv.restrictNormal_commutes τa N x).symm
    refine hIS (τa.restrictNormal N) ?_ τ hr
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.closure T),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact Subtype.ext ((hr x).symm.trans (hτ _ ((IntermediateField.mem_lift x).2 hx)))

end GlobalTheory.InertiaGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareEquivOfBaseChangeField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exteriorSquare_equiv_of_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  intro K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex
  classical
  obtain ⟨eL, heL⟩ := hex

  have hinj : Function.Injective (TensorProduct.mk K L N 1) := by
    have h1 : Function.Injective ((Algebra.linearMap K L).rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
    intro x y hxy
    apply (TensorProduct.lid K N).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy

  have hc : ∀ a, c a a = 0 := by
    intro a
    apply hinj
    apply e₂.injective
    have h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
    simp only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]
  let f : M [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun w => c (w 0) (w 1)
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ w i r x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all [hc] }
  let φ := exteriorPower.alternatingMapLinearEquiv f
  have hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1) := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w
  let b := Module.Basis.ofVectorSpace K M
  letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower 2
  let b' := (Algebra.TensorProduct.basis L b).map e₁
  have hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i) := fun i => by
    simp [b', Algebra.TensorProduct.basis_apply]
  let B' := b'.exteriorPower 2
  have key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s) := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, hφ, hcomp, ← heL]
    congr 2
    funext i
    fin_cases i <;> simp [hb']
  let V' := B'.map (eL.trans e₂.symm)
  have hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s) := fun s => by
    simp only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := by
    have h := V'.linearIndependent
    rwa [show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV'] at h
  have h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := h1.restrict_scalars' K
  have h3 : LinearIndependent K (φ ∘ B) := LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2
  let W := Submodule.span K (Set.range (φ ∘ B))
  have hs : Function.Surjective (W.subtype.lTensor L) := by
    have hr : LinearMap.range (W.subtype.baseChange L) = ⊤ := by
      rw [eq_top_iff, ← V'.span_eq, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rw [hV']
      exact ⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hr x
    exact ⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have hW : Function.Surjective W.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs
  have hspan : ⊤ ≤ W := fun x _ => by
    obtain ⟨y, rfl⟩ := hW x
    exact y.2
  let V := Module.Basis.mk h3 hspan
  refine ⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩
  have hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ :=
    B.ext fun s => by simp [V, Module.Basis.mk_apply]
  rw [← LinearEquiv.coe_coe, hEq, hφ]
  rfl

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem _root_.GlobalTheory.FockAlg.fock_lie_and_commute : ∀ (p q r s : ℕ),
    (∀ Y Z, _root_.Formalism.BasicNotions.TH.omAct p q r s (Y * Z - Z * Y) =
      _root_.Formalism.BasicNotions.TH.omAct p q r s Y * _root_.Formalism.BasicNotions.TH.omAct p q r s Z - _root_.Formalism.BasicNotions.TH.omAct p q r s Z * _root_.Formalism.BasicNotions.TH.omAct p q r s Y) ∧
    _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct1 p q r s) ∧ _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct2 p q r s) ∧
    ∀ Y Z, _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y * _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z = _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z * _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y :=
  fun p q r s => ⟨_root_.GlobalTheory.FockLie.omAct_lie p q r s,
    _root_.GlobalTheory.FockPair.pair_lie_commute p q r s⟩

end GlobalTheory.FockAlg
end

