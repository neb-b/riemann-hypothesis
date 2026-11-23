module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZero
section
open IsLocalRing

namespace GlobalTheory

theorem adic_coeffs_tendsto_zero :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ M _ _ r s hs X z hz
  classical
  set m := maximalIdeal R

  have coef : ∀ (x : M) (k : ℕ), x ∈ (m ^ k • ⊤ : Submodule R M) →
      ∃ a : Fin r → R, x = ∑ j, a j • s j ∧ ∀ j, a j ∈ m ^ k := by
    intro x k hx
    rw [← hs, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, hsum⟩ := hx
    refine ⟨a, ?_, ha⟩
    rw [← hsum, Finsupp.sum_fintype]
    intro j; simp
  haveI : Module.Finite R M := ⟨by rw [← hs]; exact Submodule.fg_span (Set.finite_range s)⟩
  have krull : (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have anti : ∀ {a b : ℕ}, a ≤ b → (m ^ b • ⊤ : Submodule R M) ≤ m ^ a • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have choiceχ : ∀ χ, ∃ a : Fin r → R, z χ = ∑ j, a j • s j ∧
      ∀ n, (¬ ∀ j, a j ∈ m ^ n) → z χ ∉ (m ^ n • ⊤ : Submodule R M) := by
    intro χ
    by_cases h : ∃ n, z χ ∉ (m ^ n • ⊤ : Submodule R M)
    · set N := Nat.find h with hN
      have hN0 : N ≠ 0 := by
        intro h0
        have := Nat.find_spec h
        rw [← hN, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
        exact this Submodule.mem_top
      have hmem : z χ ∈ (m ^ (N - 1) • ⊤ : Submodule R M) := by
        by_contra hc
        have := Nat.find_min' h hc
        omega
      obtain ⟨a, ha, hm⟩ := coef _ _ hmem
      refine ⟨a, ha, fun n hn hzn => hn fun j => ?_⟩
      have hlt : n < N := by
        by_contra hle
        push_neg at hle
        exact (Nat.find_spec h) (anti hle hzn)
      exact Ideal.pow_le_pow_right (by omega) (hm j)
    · push_neg at h
      have hz0 : z χ = 0 := by
        have : z χ ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr h
        rw [krull] at this
        exact (Submodule.mem_bot R).mp this
      refine ⟨0, by simp [hz0], fun n hn _ => hn fun j => ?_⟩
      simp
  choose c hc hbad using choiceχ
  refine ⟨c, hc, fun n => (hz n).subset ?_⟩
  intro χ hχ
  exact hbad χ n hχ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootMapComplexLinearIndependent
section
open Filter Topology

namespace GlobalTheory

open Polynomial

theorem adjoinRoot_map_complex_linearIndependent :
    ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic →
      ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))),
        (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧
        (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧
        ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e →
          LinearIndependent ℂ (fun j => τ (e j)) := by
  intro D P hP
  set f : MvPolynomial (Fin D) ℚ →+* MvPolynomial (Fin D) ℂ := MvPolynomial.map (algebraMap ℚ ℂ)
  set Q := P.map f
  have hQ : Q.Monic := hP.map f
  have h0 : P.eval₂ ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) = 0 := by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root]
  let τ := AdjoinRoot.lift ((AdjoinRoot.of Q).comp f) (AdjoinRoot.root Q) h0
  have hof : ∀ r, τ (AdjoinRoot.of P r) = AdjoinRoot.of Q (f r) := fun r => by
    simp [τ, AdjoinRoot.lift_of]
  have hroot : τ (AdjoinRoot.root P) = AdjoinRoot.root Q := AdjoinRoot.lift_root _
  have hsmul : ∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u := by
    intro q u
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin D) ℚ),
      AdjoinRoot.algebraMap_eq, hof, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin D) ℂ),
      AdjoinRoot.algebraMap_eq]
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨τ, fun i => by rw [hof]; simp [f], hsmul, ?_⟩
  intro J e he
  let τL : AdjoinRoot P →ₗ[ℚ] AdjoinRoot Q :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := fun q u => by
        rw [hsmul]
        exact algebraMap_smul ℂ q (τ u) }
  let bA := (MvPolynomial.basisMonomials (Fin D) ℚ).smulTower (AdjoinRoot.powerBasis' hP).basis
  let bB := (MvPolynomial.basisMonomials (Fin D) ℂ).smulTower (AdjoinRoot.powerBasis' hQ).basis
  have hdim : (AdjoinRoot.powerBasis' hP).dim = (AdjoinRoot.powerBasis' hQ).dim := by
    simp [AdjoinRoot.powerBasis', Q, hP.natDegree_map]
  let σ := Equiv.prodCongr (Equiv.refl (Fin D →₀ ℕ)) (finCongr hdim)
  let E := (Algebra.TensorProduct.basis ℂ bA).equiv bB σ
  have hbas : ∀ k, τ (bA k) = bB (σ k) := by
    rintro ⟨a, i⟩
    simp only [bA, bB, σ, Module.Basis.smulTower_apply, MvPolynomial.coe_basisMonomials,
      PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen, Equiv.prodCongr_apply, Equiv.coe_refl,
      Prod.map, id, finCongr_apply, Fin.val_cast]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, hroot, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.algebraMap_eq, hof]
    simp [f, MvPolynomial.map_monomial]
  have hkey : ∀ v, E (1 ⊗ₜ[ℚ] v) = τ v := by
    intro v
    have := bA.ext (f₁ := (E.toLinearMap.restrictScalars ℚ).comp (TensorProduct.mk ℚ ℂ _ 1))
      (f₂ := τL) (fun k => by
        simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
        rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply]
        exact (hbas k).symm)
    exact congrArg (fun g => g v) this
  have hli : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) :=
    Module.Flat.linearIndependent_one_tmul he
  have := hli.map' E.toLinearMap E.ker
  have h2 : (fun j => τ (e j)) = E.toLinearMap ∘ (fun j => (1 : ℂ) ⊗ₜ[ℚ] e j) := by
    funext j
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    exact (hkey (e j)).symm
  rw [h2]
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVR
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial

theorem adjoinRoot_uniformiser_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he _
  set f : R[X] := X ^ e - C π with hf
  have hmon : f.Monic := monic_X_pow_sub_C π he.ne'
  have hdeg : f.natDegree = e := natDegree_X_pow_sub_C _
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hmon).finite
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R _
  haveI : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R _
  set x : AdjoinRoot f := AdjoinRoot.root f with hx
  have hxe : x ^ e = algebraMap R (AdjoinRoot f) π := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    rw [hf, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [degree_eq_natDegree hmon.ne_zero, hdeg]; exact_mod_cast he.ne')

  have hdec : ∀ a : AdjoinRoot f, ∃ r : R, ∃ y : AdjoinRoot f, a = algebraMap R _ r + x * y := by
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    refine ⟨p.coeff 0, AdjoinRoot.mk f p.divX, ?_⟩
    conv_lhs => rw [← X_mul_divX_add p]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]
    rfl
  have hπm : π ∈ maximalIdeal R := (mem_maximalIdeal _).2 hπ.not_isUnit

  have hcomap : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal →
      M.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R := by
    intro M hM
    letI : M.IsMaximal := hM
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap R (AdjoinRoot f))
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R (AdjoinRoot f))) M)
  have hxM : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal → x ∈ M := by
    intro M hM
    have : algebraMap R _ π ∈ M := by
      rw [← Ideal.mem_comap, hcomap M hM]; exact hπm
    rw [← hxe] at this
    exact hM.isPrime.mem_of_pow_mem e this
  have hle : ∀ M N : Ideal (AdjoinRoot f), M.IsMaximal → N.IsMaximal → M ≤ N := by
    intro M N hM hN a ha
    obtain ⟨r, y, rfl⟩ := hdec a
    have hr : algebraMap R _ r ∈ M := by
      have := M.sub_mem ha (M.mul_mem_right y (hxM M hM))
      simpa using this
    have hr' : r ∈ maximalIdeal R := by rw [← hcomap M hM]; exact hr
    have hrN : algebraMap R _ r ∈ N := by
      rw [← Ideal.mem_comap, hcomap N hN]; exact hr'
    exact N.add_mem hrN (N.mul_mem_right y (hxM N hN))
  haveI : IsLocalRing (AdjoinRoot f) :=
    IsLocalRing.of_unique_max_ideal (by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot f)
      exact ⟨M, hM, fun N hN => le_antisymm (hle N M hN hM) (hle M N hM hN)⟩)
  have hmax : maximalIdeal (AdjoinRoot f) = Ideal.span {x} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨r, y, rfl⟩ := hdec a
      have hr : algebraMap R _ r ∈ maximalIdeal (AdjoinRoot f) := by
        have := Ideal.sub_mem (maximalIdeal (AdjoinRoot f)) ha
          (Ideal.mul_mem_right y (maximalIdeal (AdjoinRoot f)) (hxM _ (maximalIdeal.isMaximal _)))
        simpa using this
      have hr' : r ∈ maximalIdeal R := by
        rw [← hcomap _ (maximalIdeal.isMaximal _)]; exact hr
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at hr'
      obtain ⟨s, rfl⟩ := hr'
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      rw [map_mul, ← hxe, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self x he.ne') _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxM _ (maximalIdeal.isMaximal _)
  have hx0 : x ≠ 0 := by
    intro h0
    have : algebraMap R (AdjoinRoot f) π = 0 := by rw [← hxe, h0, zero_pow he.ne']
    exact hπ.ne_zero (hinj (by rw [this, map_zero]))
  have hnf : ¬ IsField (AdjoinRoot f) := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hx0
    exact (mem_maximalIdeal x).1 (hxM _ (maximalIdeal.isMaximal _)) (IsUnit.of_mul_eq_one b hb)
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 5 1).1 (show (maximalIdeal (AdjoinRoot f)).IsPrincipal from ⟨⟨x, hmax⟩⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomain
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory


open Polynomial in
theorem adjoinRoot_X_pow_sub_C_uniformizer_isDomain :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ),
      Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  intro R _ _ _ π e hπ he
  have hπp : Prime π := hπ.prime
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  have hmon : (X ^ e - C π : R[X]).Monic := monic_X_pow_sub_C _ he.ne'
  have hdeg : (X ^ e - C π : R[X]).natDegree = e := natDegree_X_pow_sub_C _
  have hirr : Irreducible (X ^ e - C π : R[X]) := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive (by rw [hdeg]; exact he)
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      rw [hdeg] at hn
      rw [coeff_sub, coeff_X_pow, if_neg hn.ne, zero_sub, coeff_C]
      split_ifs
      · exact neg_mem (Ideal.mem_span_singleton_self _)
      · rw [neg_zero]; exact zero_mem _
    · rw [coeff_sub, coeff_X_pow, if_neg he.ne, zero_sub, coeff_C_zero, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : π * (1 + π * c) = 0 := by linear_combination -hc
      have h2 := (mul_eq_zero.1 h1).resolve_left hπp.ne_zero
      exact hπ.not_isUnit (IsUnit.of_mul_eq_one (-c) (by linear_combination -h2))
  exact AdjoinRoot.isDomain_of_prime hirr.prime

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem isFundamentalDomain_of_ae_eq {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X]
    [MulAction Γ X] [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]
    {s t : Set X} (h : IsFundamentalDomain Γ s μ) (hst : t =ᵐ[μ] s) :
    IsFundamentalDomain Γ t μ := by
  refine ⟨h.nullMeasurableSet.congr hst.symm, ?_, ?_⟩
  ·
    have hall : ∀ᵐ x ∂μ, ∀ g : Γ, (g • x ∈ t) = (g • x ∈ s) := by
      rw [ae_all_iff]
      intro g
      exact ((measurePreserving_smul g μ).quasiMeasurePreserving.ae hst).mono fun _ hx => propext hx
    filter_upwards [h.ae_covers, hall] with x ⟨g, hg⟩ hx
    exact ⟨g, by rw [hx g]; exact hg⟩
  · intro a b hab
    have key : ∀ c : Γ, (c • t : Set X) =ᵐ[μ] (c • s : Set X) := fun c => by
      rw [← Set.preimage_smul_inv, ← Set.preimage_smul_inv]
      exact (measurePreserving_smul c⁻¹ μ).quasiMeasurePreserving.preimage_ae_eq hst
    exact (h.aedisjoint hab).congr (key a) (key b)

variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem ae_measure_setOf_smul_mem_eq_zero (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] {W : Set X} (hW : μ W = 0) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ W} = 0 := by
  set W' := toMeasurable μ W
  have hW'm : MeasurableSet W' := measurableSet_toMeasurable μ W
  have hW'0 : μ W' = 0 := by rw [measure_toMeasurable]; exact hW
  have hQ : MeasurableSet {p : X × S | p.2 • p.1 ∈ W'} :=
    hW'm.preimage (measurable_snd.smul measurable_fst)
  have h0 : μ.prod ν {p : X × S | p.2 • p.1 ∈ W'} = 0 := by
    rw [Measure.prod_apply_symm hQ]
    have : ∀ s : S, μ ((fun x => (x, s)) ⁻¹' {p : X × S | p.2 • p.1 ∈ W'}) = 0 := fun s => by
      change μ ((fun x => s • x) ⁻¹' W') = 0
      rw [measure_preimage_smul]; exact hW'0
    exact (lintegral_congr this).trans lintegral_zero
  have h1 := (Measure.measure_prod_null hQ).1 h0
  filter_upwards [h1] with y hy
  exact measure_mono_null (fun s hs => subset_toMeasurable μ W hs) hy

end GlobalTheory.CovolIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalApplyMem
section
namespace GlobalTheory.PolynomialEvaluationMembership

theorem pow_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (n : ℕ) :
    ∀ x ∈ W, (g ^ n) x ∈ W := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hW x hx)

theorem aeval_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : Polynomial F) :
    ∀ x ∈ W, (Polynomial.aeval g p) x ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    rw [map_add (f := _), LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial n a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem a (pow_apply_mem g W hW n x hx)

end GlobalTheory.PolynomialEvaluationMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem isAffineOpen_preimage_and_tensor_equiv_of_isPullback : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  intro k K _ _ _ X X' f f' π h V hV
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine ⟨hV.preimage π, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top)
      (CommRingCat.ofHom (algebraMap k K)) (π.app V)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  letI : Algebra K Γ(X', π ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI : Algebra k Γ(X', π ⁻¹ᵁ V) :=
    ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom).comp
      (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, V) Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun r => by
    exact (congrArg (fun φ => φ.hom r) hpo'.w).symm
  haveI : Algebra.IsPushout k K Γ(X, V) Γ(X', π ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'.flip
  refine ⟨(Algebra.IsPushout.equiv k K Γ(X, V) Γ(X', π ⁻¹ᵁ V)).toRingEquiv, fun a => ?_, fun c => ?_⟩
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCover
section
open AlgebraicGeometry TopologicalSpace

namespace GlobalTheory

theorem affine_inter_finite_basicOpen_cover :
    ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V →
      ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧
        ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  intro X hX W V hW hV
  classical
  have key : ∀ x : ((W ⊓ V : X.Opens) : Set X), ∃ (f : Γ(X, W)) (g : Γ(X, V)),
      X.basicOpen f = X.basicOpen g ∧ (x : X) ∈ X.basicOpen f :=
    fun x => exists_basicOpen_le_affine_inter hW hV x.1 x.2
  choose f g hfg hx using key
  have hc : IsCompact ((W ⊓ V : X.Opens) : Set X) := NoetherianSpace.isCompact _
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩)
  refine ⟨t.image f, ?_, ?_⟩
  · intro h hh
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨g x, hfg x⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Set.mem_iUnion₂.2 ⟨f x, Finset.mem_image_of_mem f hxt, hyx⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAl
section
open AlgebraicGeometry

namespace GlobalTheory

theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
end

