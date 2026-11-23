module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
section
open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  first | (exact @GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (exact GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (intros; apply GlobalTheory.EtC.chains_cech_conerve_quasiIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisibleStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_dedekind_algClosed_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 → ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.classGroup_divisible) | (exact GlobalTheory.PicDiv.classGroup_divisible) | (intros; apply GlobalTheory.PicDiv.classGroup_divisible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassMeanLogNormDiscChowlaSelberg
section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors

namespace GlobalTheory.ClassMeanDisc

theorem classMean_log_norm_disc : ∀ (D : Formalism.BasicNotions.D7) {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → discr K = -(D.host.d : ℤ) → 4 < D.host.d → ∀ (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair), (∀ c, ClassGroup.mk K (rep c) = c) → (∀ c, IsLatOf φK (rep c : FractionalIdeal (𝓞 K)⁰ K) (L c)) → (∑ c, Real.log (nrm (rep c : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (L c)‖)) / (classNumber K : ℝ) = 12 * Real.log (2 * Real.pi) - 6 * Real.log D.host.d + 6 * Real.eulerMascheroniConstant - 6 * Formalism.BasicNotions.dlogL D 1 := by
  intro D K _ _ φK h2 hD hd rep L hrep hL
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd3 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hχ : IsKroneckerChar (Formalism.BasicNotions.chiK D) := isKroneckerChar_quadraticChar hd3
  have key := chowla_selberg_discriminant h2 hD hd hχ φK hrep hL
  have hre := congrArg Complex.re key
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  unfold Formalism.BasicNotions.dlogL nrm latDisc
  rw [hre]
  simp [Complex.mul_re]

end GlobalTheory.ClassMeanDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassZeroOfGeometricPoints
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_zero_of_geometric_points : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ) (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  first | (exact @GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (exact GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (intros; apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIff
section
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.ComplStd

theorem mem_omA_iff {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}
    (hx : ∀ i, x i ≠ 0) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (f : F) :
    f ∈ omA k x I ↔ (∏ j, x i / x j) * f ∈ rA k x I := by
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule]
  refine ⟨fun h => h i hi, fun h i' _ => ?_⟩
  have hg : x i' / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, i', rfl⟩
  have e : (∏ j, x i' / x j) = (x i' / x i) ^ (d + 1) * ∏ j, x i / x j := by
    rw [show (x i' / x i) ^ (d + 1) = ∏ _j : Fin (d + 1), x i' / x i by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (div_mul_div_cancel₀ (hx i)).symm
  rw [e, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hg _) h

theorem trace_algebraMap_mul {F K : Type} [Field F] [Field K] [Algebra F K] (c : F) (w : K) :
    Algebra.trace F K (algebraMap F K c * w) = c * Algebra.trace F K w := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem single (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (τ : DR k K →ₗ[K] K) (hτ : IsTop k K x τ) (i : Fin (d + 1)) (z : K) :
    (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔ ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
  haveI := hc.fin
  have hx := hc.pd.ne
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd i
  set u : Fin d → F := fun j => x (i.succAbove j) / x i with hu_def
  have hu : AlgebraicIndependent k u := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : MvPolynomial.aeval u = (rA k x {i}).val.comp e.toAlgHom :=
      MvPolynomial.algHom_ext fun j => by simp [he, u]
    rw [this]
    exact Subtype.val_injective.comp e.injective
  have hA : rA k x {i} = Algebra.adjoin k (Set.range u) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro y ⟨i', hi', j, rfl⟩
      rw [Finset.mem_singleton] at hi'
      subst hi'
      by_cases hj : j = i'
      · subst hj; rw [div_self (hx _)]; exact one_mem _
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact Algebra.subset_adjoin ⟨j', rfl⟩
    · apply Algebra.adjoin_le
      rintro y ⟨j, rfl⟩
      exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, _, rfl⟩
  haveI : IsFractionRing (rA k x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {i} (Finset.singleton_nonempty _)).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_sign_iMulti_D_chart_change k F K d x hc i
  set P : F := ∏ j, x i / x j with hP
  set C : F := ∏ j, x j / x i with hC
  have hPC : algebraMap F K P * algebraMap F K C = 1 := by
    rw [← map_mul, hP, hC, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_one fun j _ => by rw [div_mul_div_cancel₀ (hx j), div_self (hx i)], map_one]
  have hPne : algebraMap F K P ≠ 0 := left_ne_zero_of_mul_eq_one hPC
  let τ' : DR k K →ₗ[K] K := (((ε : ℤ) : K) * algebraMap F K P) • τ
  have hτ' : τ' (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 := by
    simp only [u]
    rw [hε]
    rw [LinearMap.smul_apply, Units.smul_def, map_zsmul, map_smul, hτ.1]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    have hε2 : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (algebraMap F K P * algebraMap F K C) * hε2 + hPC
  have key := GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover k F K d u hu (rA k x {i}) hA (rB k K x {i}) rfl (hc.smooth i) τ' hτ'
    (algebraMap F K P * z)
  have lhs : (∀ b ∈ rB k K x {i}, Algebra.trace F K (z * b) ∈ omA k x {i}) ↔
      ∀ b : rB k K x {i}, Algebra.trace F K (algebraMap F K P * z * b) ∈ rA k x {i} := by
    simp only [Subtype.forall, mem_omA_iff hx (Finset.mem_singleton_self i), mul_assoc, trace_algebraMap_mul]
    exact Iff.rfl
  have rhs : (∃ y ∈ omB k K (rB k K x {i}) d, τ' y = algebraMap F K P * z) ↔
      ∃ y ∈ omB k K (rB k K x {i}) d, τ y = z := by
    have h1 : ∀ y, τ' y = algebraMap F K P * z ↔ ((ε : ℤ) : K) * τ y = z := by
      intro y
      simp only [τ', LinearMap.smul_apply, smul_eq_mul]
      rw [show ((ε : ℤ) : K) * algebraMap F K P * τ y = algebraMap F K P * (((ε : ℤ) : K) * τ y) by ring,
        mul_right_inj' hPne]
    simp only [h1]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp
    · constructor
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simpa using h⟩
      · rintro ⟨y, hy, h⟩; exact ⟨-y, neg_mem hy, by rw [map_neg]; simp [h]⟩
  exact lhs.trans (key.trans rhs)

theorem unif (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (hc : IsFinCover k K x)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (z : K)
    (h : ∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) :
    ∃ N : ℕ, ∀ b ∈ rB k K x {i},
      Algebra.trace F K (z * algebraMap F K (∏ j ∈ I, x j / x i) ^ N * b) ∈ omA k x {i} := by
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  set P : F := ∏ j, x i / x j with hP
  have hs1 : s ∈ rA k x {i} :=
    Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self _, j, rfl⟩
  have hle : rB k K x {i} ≤ rB k K x I :=
    (GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc {i} i (Finset.mem_singleton_self _)).1 I (Finset.singleton_subset_iff.2 hi)
  haveI : Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    (GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc {i} (Finset.singleton_nonempty _)).1
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := rA k x {i}) (M := integralClosure (rA k x {i}) K)
  have hg : ∀ g : integralClosure (rA k x {i}) K, ∃ N : ℕ,
      P * Algebra.trace F K (z * g) * s ^ N ∈ rA k x {i} := by
    intro g
    have hgI : (g : K) ∈ rB k K x I := hle g.2
    exact (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi _).1 ((mem_omA_iff hx hi _).1 (h _ hgI))
  choose Nf hNf using hg
  refine ⟨∑ g ∈ S, Nf g, fun b hb => ?_⟩
  rw [mem_omA_iff hx (Finset.mem_singleton_self i)]
  have hb' : (⟨b, hb⟩ : integralClosure (rA k x {i}) K) ∈ Submodule.span (rA k x {i}) (S : Set _) := by
    rw [hS]; trivial
  have key : ∀ w : integralClosure (rA k x {i}) K, w ∈ Submodule.span (rA k x {i}) (S : Set _) →
      P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * w) ∈ rA k x {i} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg)
      have e : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * g) =
          s ^ m * (P * Algebra.trace F K (z * g) * s ^ Nf g) := by
        rw [hm, mul_comm z, ← map_pow, mul_assoc, trace_algebraMap_mul]; ring
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs1 _) (hNf g)
    | zero => simp
    | add a c _ _ ha hc =>
      have e : ((a + c : integralClosure (rA k x {i}) K) : K) = a + c := rfl
      rw [e, mul_add, map_add (f := _), mul_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      set_option synthInstance.maxHeartbeats 200000 in
      have e : ((r • a : integralClosure (rA k x {i}) K) : K) = algebraMap F K (r : F) * a := by
        rw [SetLike.val_smul, Algebra.smul_def]; rfl
      have e2 : P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a)) =
          (r : F) * (P * Algebra.trace F K (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a)) := by
        rw [show z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * (algebraMap F K (r : F) * a) =
          algebraMap F K (r : F) * (z * algebraMap F K s ^ (∑ g ∈ S, Nf g) * a) by ring, trace_algebraMap_mul]
        ring
      rw [e, e2]
      exact Subalgebra.mul_mem _ r.2 ha
  exact key _ hb'

theorem complementary_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI z
  obtain ⟨i, hi⟩ := hI
  have hx := hc.pd.ne
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsne : algebraMap F K s ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx j) (hx i))
  constructor
  · intro h
    obtain ⟨N, hN⟩ := unif k F K d x hc I i hi z h
    obtain ⟨y', hy', hτy'⟩ := (single k F K d x hc τ hτ i _).1 hN
    refine ⟨(algebraMap F K s ^ N)⁻¹ • y', (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d _).2 ⟨N, ?_⟩, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hsne), one_smul]; exact hy'
    · rw [map_smul, hτy', smul_eq_mul]; field_simp; exact mul_comm _ _
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hc I i hi d y).1 hy
    have h1 := (single k F K d x hc τ hτ i _).2 ⟨_, hN, rfl⟩
    intro b hb
    obtain ⟨M, hM⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart k F K d x hc I i hi).2 b).1 hb
    have h2 := (mem_omA_iff hx (Finset.mem_singleton_self i) _).1 (h1 _ hM)
    rw [mem_omA_iff hx hi, GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hc.pd I i hi]
    refine ⟨N + M, ?_⟩
    convert h2 using 1
    rw [map_smul, smul_eq_mul, show algebraMap F K s ^ N * τ y * (b * algebraMap F K s ^ M) =
      algebraMap F K (s ^ (N + M)) * (τ y * b) by rw [map_pow, pow_add]; ring, trace_algebraMap_mul]
    ring

end GlobalTheory.ComplStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianPosSemidefOfLeviFormNonnegStatement
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg : ∀ (n : ℕ) (φ : V n → ℝ) (z : V n), ContDiffAt ℝ 2 φ z → (∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  first | exact @GlobalTheory.cHess_posSemidef_of_levi_nonneg | exact GlobalTheory.cHess_posSemidef_of_levi_nonneg | (intros; apply GlobalTheory.cHess_posSemidef_of_levi_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
section
open Finset

namespace GlobalTheory.DSParam

open Finset in
private theorem diagonal_exp_single_two_pi_eq_one {n : ℕ} (a : Fin n) :
    (Matrix.diagonal fun b ↦
      Complex.exp (↑((Pi.single a (2 * Real.pi) : Fin n → ℝ) b) * Complex.I)) = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp [Complex.exp_two_pi_mul_I]
  · simp [Pi.single_apply, h]

open Finset in
private theorem exists_int_eq_weight_of_isWtOn {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ K)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : _root_.Formalism.MainNotions.S.IsWtOn K σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  unfold _root_.Formalism.MainNotions.S.IsWtOn at hv
  have h1 := hv 0 (by simpa using hK)
  have h2 := hv (Pi.single a (2 * Real.pi)) (by rw [diagonal_exp_single_two_pi_eq_one]; exact hK)
  rw [diagonal_exp_single_two_pi_eq_one] at h2
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Matrix.diagonal_one, mul_zero, Finset.sum_const_zero, one_smul] at h1
  rw [h1] at h2
  have hsum : (∑ b, μ b * (Pi.single a (2 * Real.pi) : Fin n → ℝ) b) = μ a * (2 * Real.pi) := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum] at h2
  have he : Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hv0
    have : (Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((μ a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast this

open Finset in
private theorem one_mem_Kset_divisor {n : ℕ} (ε : Fin n → Bool) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.Formalism.REAL.Kset ε := by
  unfold _root_.Formalism.REAL.Kset
  exact ⟨one_mem _, by simp⟩

open Finset in
private theorem card_same_diff_sign_lt_gt_add_one_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b | a < b ∧ ε b = ε a} + #{b | b < a ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a}
      + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ b, ((if a < b ∧ ε b = ε a then 1 else 0) + (if b < a ∧ ε b = ε a then 1 else 0) +
      (if a < b ∧ ε b ≠ ε a then 1 else 0) + (if b < a ∧ ε b ≠ ε a then 1 else 0) : ℕ)
      = if b = a then 0 else 1 := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : b ≠ a := ne_of_gt h
      have h2 : ¬ b < a := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
    · subst h; simp
    · have h1 : b ≠ a := ne_of_lt h
      have h2 : ¬ a < b := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  have := a.isLt
  omega

open Finset in
private theorem exists_int_rhoC_sub_rhoN_sub_half {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, _root_.Formalism.REAL.rhoC ε a - _root_.Formalism.REAL.rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have h := card_same_diff_sign_lt_gt_add_one_eq ε a
  unfold _root_.Formalism.REAL.rhoC _root_.Formalism.REAL.rhoN
  refine ⟨-((#{b | b < a ∧ ε b = ε a} : ℕ) + (#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℤ), ?_⟩
  have hr : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + #{b | b < a ∧ ε b = ε a}
      + #{b | a < b ∧ ε b ≠ ε a} + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
    exact_mod_cast h
  push_cast
  linear_combination hr / 2


open Finset in
theorem _root_.GlobalTheory.DSParam.isHCParam_of_isDS : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    StrictAnti lam → _root_.Formalism.MainNotions.S.IsDS ε lam σ → _root_.Formalism.QuantumDeterminants.IsHCParam lam := by
  intro n H _ _ ε lam σ hlam hds
  unfold _root_.Formalism.MainNotions.S.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  unfold _root_.Formalism.MainNotions.S.IsKTypeOf at hS
  obtain ⟨-, -, -, ⟨v, -, hv0, hv⟩, -⟩ := hS
  unfold _root_.Formalism.QuantumDeterminants.IsHCParam
  refine ⟨hlam, fun a => ?_⟩
  obtain ⟨k, hk⟩ := exists_int_eq_weight_of_isWtOn (one_mem_Kset_divisor ε) hv0 hv a
  obtain ⟨m, hm⟩ := exists_int_rhoC_sub_rhoN_sub_half ε a
  refine ⟨k + m, ?_⟩
  have hl : _root_.Formalism.QuantumDeterminants.lowK ε lam a = lam a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  push_cast
  linarith

end GlobalTheory.DSParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∀ (U U' : Scheme.{0}) (s : U ⟶ S) (f : U' ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj U') F → Function.Bijective (fun φ : LocallyConstant U R => φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  first | exact @GlobalTheory.EtC.eqv_of_gen_lc | exact GlobalTheory.EtC.eqv_of_gen_lc | (intros; apply GlobalTheory.EtC.eqv_of_gen_lc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBaseChangeCechAugmenta
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bc_cechAug_eqv : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W),
    Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  intro R _ F S W V r f hE hS U
  obtain ⟨e₁, e₂, he⟩ := bc_cechAug_iso S W V r f U
  have hE' : Etale (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hS' : Surjective (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hA : Eqv R (cechAug (pullback.snd f (pullback.fst r U.hom))) F :=
    smooth_surjective_cech_descent_cohomology R (pullback.snd f (pullback.fst r U.hom)) F
  obtain ⟨hiso, hcomp, -, -⟩ := eqv_basic R F
  have h1 : Eqv R e₁.hom F := hiso _ _ _ inferInstance
  have h2 : Eqv R e₂.hom F := hiso _ _ _ inferInstance
  have h3 : Eqv R (e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U) F := by
    rw [he]; exact (hcomp _ _ _ _ _).1 hA h2
  exact (hcomp _ _ _ _ _).2.1 h1 h3

end GlobalTheory.EtC
end

