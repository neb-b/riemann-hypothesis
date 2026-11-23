module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulSubMemJacobsonOfFiniteResidueFiel
section
open IsDedekindDomain

namespace GlobalTheory

theorem finite_quotient_jacobson_of_finite_residueField (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] : Finite (A ⧸ (⊥ : Ideal A).jacobson) := by
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ

  have hm : ∀ m ∈ IsLocalRing.maximalIdeal O, algebraMap O A m ∈ J := by
    intro m hm
    rw [hJ, Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have : (M.comap (algebraMap O A)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M
    have h := IsLocalRing.eq_maximalIdeal this
    have : m ∈ M.comap (algebraMap O A) := h ▸ hm
    exact this
  have hfin : Module.Finite O (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ J)
  have hsurj : Function.Surjective (IsLocalRing.residue O) := Ideal.Quotient.mk_surjective
  let f : (Fin n → IsLocalRing.ResidueField O) → A ⧸ J :=
    fun y ↦ ∑ i, Function.surjInv hsurj (y i) • s i
  have : Function.Surjective f := by
    intro q
    have hq : q ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hq
    refine ⟨fun i ↦ IsLocalRing.residue O (c i), ?_⟩
    simp only [f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hd : Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i ∈
        IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, Function.surjInv_eq hsurj, sub_self]
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    have h0 : algebraMap O (A ⧸ J) (Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i)
        = 0 := by
      rw [IsScalarTower.algebraMap_apply O A (A ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hm _ hd
    rw [h0, zero_mul]
  exact Finite.of_surjective f this

theorem exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type)
      [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) →
      ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a →
      ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  intro O _ _ _ A _ _ _ τ hτ θ hθ a ha hτa
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ
  have : Finite (A ⧸ J) := finite_quotient_jacobson_of_finite_residueField O A
  have : IsReduced (A ⧸ J) := by
    refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.isRadical_jacobson ⊥ ⟨k, hk⟩)
  have hτJ : J ≤ J.comap τ := by
    intro x hx
    rw [Ideal.mem_comap, hJ, Ideal.mem_jacobson_bot] at *
    intro b
    have h := (hx (τ b)).map τ
    simpa [hτ] using h
  let τ' : A ⧸ J →+* A ⧸ J := Ideal.quotientMap J τ hτJ
  have hτ' : ∀ x, τ' (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (τ x) := fun x ↦
    Ideal.quotientMap_mk
  have hinv : ∀ x, τ' (τ' x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ', hτ', hτ]
  obtain ⟨c, hc⟩ := norm_surj_of_finite_reduced_involution (A ⧸ J) τ' hinv
    (Ideal.Quotient.mk J θ) (by rw [hτ', ← map_sub]; exact hθ.map _)
    (Ideal.Quotient.mk J a) (ha.map _) (by rw [hτ', hτa])
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, isUnit_of_isUnit_mk_of_le_jacobson le_rfl ?_, ?_⟩
  · have : IsUnit (τ' (Ideal.Quotient.mk J t) * Ideal.Quotient.mk J t) := hc ▸ ha.map _
    exact isUnit_of_mul_isUnit_right this
  · rw [← Ideal.Quotient.eq, map_mul, ← hτ', mul_comm, hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := _root_.GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLe
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.SubLen

theorem exists_relLen_of_smul_le (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M]
    (htf : ∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0)
    (X' X : Submodule (Int0 v) M) (hle : X' ≤ X) (hX : Module.Finite (Int0 v) X)
    (hX' : Module.Finite (Int0 v) X') (c : Int0 v) (hc : c ≠ 0) (hcX : ∀ x ∈ X, c • x ∈ X') :
    ∃ r : ℝ, RelLen v X' X r := by
  haveI tfX : Module.IsTorsionFree (Int0 v) X :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI tfX' : Module.IsTorsionFree (Int0 v) X' :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI := hX
  haveI := hX'
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X')
  let ι : X' →ₗ[Int0 v] X := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  let μ : X →ₗ[Int0 v] X' :=
    { toFun := fun x => ⟨c • (x : M), hcX x x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add c (x : M) y)
      map_smul' := fun r x => Subtype.ext (by
        change c • (r • (x : M)) = r • (c • (x : M))
        exact smul_comm c r (x : M)) }
  have hμ : Function.Injective μ := by
    intro x y hxy
    have : c • ((x : M) - y) = 0 := by
      have h3 : c • (x : M) = c • (y : M) := congrArg Subtype.val hxy
      rw [smul_sub, h3, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (htf c _ hc this))
  have h1 : finrank (Int0 v) X' ≤ finrank (Int0 v) X := LinearMap.finrank_le_finrank_of_injective hι
  have h2 : finrank (Int0 v) X ≤ finrank (Int0 v) X' := LinearMap.finrank_le_finrank_of_injective hμ
  have heq : finrank (Int0 v) X' = finrank (Int0 v) X := le_antisymm h1 h2
  let b := Module.finBasis (Int0 v) X
  let b' := Module.finBasisOfFinrankEq (Int0 v) X' heq
  let A := LinearMap.toMatrix b' b ι
  have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
    intro k
    have e := b.sum_repr (ι (b' k))
    have e2 := congrArg (Submodule.subtype X) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simpa [A, LinearMap.toMatrix_apply, ι] using e2.symm
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    have : ι (b'.equivFun.symm w) = 0 := by
      have := Matrix.toLin_toMatrix b' b ι
      rw [← this, Matrix.toLin_apply]
      simp only [Basis.equivFun_symm_apply, Basis.repr_sum_self]
      change ∑ x, (A.mulVec w) x • b x = 0
      simp [hw]
    have h4 := hι (this.trans (map_zero ι).symm)
    have h5 := congrArg b'.equivFun h4
    rw [LinearEquiv.apply_symm_apply, map_zero] at h5
    exact h5
  have hv : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact_mod_cast hdet
  exact ⟨(v (A.det : C)).untop hv, _, b, b', A, hA, (WithTop.coe_untop _ hv).symm⟩

end GlobalTheory.SubLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFinite
section
open IsLocalRing

namespace GlobalTheory

theorem exists_lift_to_complete_dvr_of_finite : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  intro A R _ _ _ hinj hfin V _ _ _ _ hC h
  classical
  let p : Ideal A := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R) (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  let K := FractionRing V
  let Ω := AlgebraicClosure K
  letI : Algebra (A ⧸ p) (R ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hQp.symm)
  have hcomp : (algebraMap (A ⧸ p) (R ⧸ Q)).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk Q).comp (algebraMap A R) := rfl
  haveI : Algebra.IsIntegral (A ⧸ p) (R ⧸ Q) := by
    constructor
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact IsIntegral.map_of_comp_eq (Ideal.Quotient.mk p) (Ideal.Quotient.mk Q) hcomp
      (Algebra.IsIntegral.isIntegral r)
  have hinj0 : Function.Injective (algebraMap (A ⧸ p) (R ⧸ Q)) :=
    Ideal.quotientMap_injective' (le_of_eq hQp)
  let g0 : (A ⧸ p) →+* Ω := (algebraMap K Ω).comp ((algebraMap V K).comp (RingHom.kerLift h))
  have hg0 : Function.Injective g0 :=
    (algebraMap K Ω).injective.comp ((IsFractionRing.injective V K).comp (RingHom.kerLift_injective h))
  letI : Algebra (A ⧸ p) Ω := g0.toAlgebra
  haveI : Module.IsTorsionFree (A ⧸ p) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj0
  haveI : Module.IsTorsionFree (A ⧸ p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hg0
  haveI : Algebra.IsAlgebraic (A ⧸ p) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (R ⧸ Q) →ₐ[A ⧸ p] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ρ1 : R →+* Ω := σ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hρ1 : ∀ a : A, ρ1 (algebraMap A R a) = algebraMap K Ω (algebraMap V K (h a)) := by
    intro a
    show σ (Ideal.Quotient.mk Q (algebraMap A R a)) = _
    rw [← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, σ.commutes]
    rfl
  obtain ⟨s, hs⟩ := hfin.fg_top
  let M : IntermediateField K Ω := IntermediateField.adjoin K (ρ1 '' (s : Set R))
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ r : R, ρ1 r ∈ M := by
    intro r
    have hr : r ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def, map_mul, hρ1]; exact M.mul_mem (M.algebraMap_mem _) hx
  let ψ : R →+* M := ρ1.codRestrict M hmem
  have hψ : (algebraMap V M).comp h = ψ.comp (algebraMap A R) := by
    ext a
    simp only [RingHom.comp_apply]
    show (algebraMap V M (h a) : Ω) = ρ1 (algebraMap A R a)
    rw [hρ1]
    rfl
  have hint : ∀ r : R, ψ r ∈ integralClosure V M := fun r =>
    IsIntegral.map_of_comp_eq h ψ hψ (Algebra.IsIntegral.isIntegral r)
  let ρ : R →+* integralClosure V M := ψ.codRestrict (integralClosure V M) hint
  haveI hdvr := Formalism.L2.G.IntCl.isDVR V K M hC
  have hfinj := Formalism.L2.G.IntCl.alg_injective V K M
  haveI : FaithfulSMul V (integralClosure V M) := (faithfulSMul_iff_algebraMap_injective _ _).2 hfinj
  refine ⟨integralClosure V M, inferInstance, inferInstance, hdvr,
    (RingHom.charZero_iff hfinj).1 inferInstance, algebraMap V (integralClosure V M), ρ,
    Formalism.L2.G.IntCl.complete V K M hC, hfinj, Algebra.IsIntegral.isLocalHom _ _, ?_⟩
  ext a
  show ρ1 (algebraMap A R a) = (algebraMap V M (h a) : Ω)
  rw [hρ1]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPushoutUnramifiedCharZero
section
open IsLocalRing

namespace GlobalTheory.UnramPushout

open TensorProduct

theorem isReduced_nontrivial_tensor {A k k' : Type} [CommRing A] [Field k] [Field k']
    [Algebra A k] [Algebra A k'] [CharZero k] (P : Ideal A) [P.IsPrime]
    (hk : RingHom.ker (algebraMap A k) = P) (hk' : RingHom.ker (algebraMap A k') = P) :
    IsReduced (k ⊗[A] k') ∧ Nontrivial (k ⊗[A] k') := by
  have hu : ∀ {L : Type} [Field L] [Algebra A L], RingHom.ker (algebraMap A L) = P →
      P.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap A L) := by
    intro L _ _ h s hs
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hs (h ▸ (RingHom.mem_ker.mpr h0))
  let ι := Ideal.ResidueField.lift P (algebraMap A k) hk.ge (hu hk)
  let ι' := Ideal.ResidueField.lift P (algebraMap A k') hk'.ge (hu hk')
  letI : Algebra P.ResidueField k := ι.toAlgebra
  letI : Algebra P.ResidueField k' := ι'.toAlgebra
  haveI : IsScalarTower A P.ResidueField k :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : IsScalarTower A P.ResidueField k' :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap P _ _ _ r).symm
  haveI : CharZero P.ResidueField := ⟨fun m n h => Nat.cast_injective (R := k) (by rw [← map_natCast ι, ← map_natCast ι, h])⟩
  haveI : CompatibleSMul A P.ResidueField k k' := by
    refine ⟨fun x m n => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ P) x
    have hβ := map_ne_zero_of_mem_nonZeroDivisors _ P.injective_algebraMap_quotient_residueField hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [Ideal.algebraMap_quotient_residueField_mk] at hβ ⊢
    set β := algebraMap A P.ResidueField b
    set α := algebraMap A P.ResidueField a
    have e1 : n = b • (β⁻¹ • n) := by
      rw [← algebraMap_smul P.ResidueField b, smul_smul, mul_inv_cancel₀ hβ, one_smul]
    have e2 : b • ((α / β) • m) = a • m := by
      rw [← algebraMap_smul P.ResidueField b, ← algebraMap_smul P.ResidueField a, smul_smul,
        mul_div_cancel₀ _ hβ]
    have e3 : a • (β⁻¹ • n) = (α / β) • n := by
      rw [← algebraMap_smul P.ResidueField a, smul_smul, div_eq_mul_inv]
    conv_lhs => rw [e1]
    rw [← smul_tmul b ((α / β) • m) (β⁻¹ • n), e2, smul_tmul a m (β⁻¹ • n), e3]
  let e := Algebra.TensorProduct.equivOfCompatibleSMul P.ResidueField A A k k'
  have : IsReduced (k ⊗[P.ResidueField] k') := GlobalTheory.ReducedAlg.isReduced_tensor k k'
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toEquiv.nontrivial⟩

theorem exists_local_pushout (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V]
    [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V') (hf' : f'.Flat)
    (hP : (maximalIdeal V).comap f = (maximalIdeal V').comap f')
    (hV : ((maximalIdeal V).comap f).map f = maximalIdeal V)
    (hV' : ((maximalIdeal V').comap f').map f' = maximalIdeal V')
    (h0 : CharZero (ResidueField V)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B),
      g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧
        (maximalIdeal V').map g' = maximalIdeal B := by
  letI : Algebra A V := f.toAlgebra
  letI : Algebra A V' := f'.toAlgebra
  haveI : Module.Flat A V' := hf'
  set P := (maximalIdeal V).comap f with hPdef
  let C := V ⊗[A] V'
  let φ : C →ₐ[A] ResidueField V ⊗[A] ResidueField V' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V (ResidueField V))
      (IsScalarTower.toAlgHom A V' (ResidueField V'))
  set Q := P.map (algebraMap A C) with hQ
  have hL : (maximalIdeal V).map (Algebra.TensorProduct.includeLeft : V →ₐ[A] C) = Q := by
    rw [← hV, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
  have hR : (maximalIdeal V').map (Algebra.TensorProduct.includeRight : V' →ₐ[A] C) = Q := by
    rw [← hV', ← hP, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
    ext a
    exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a
  have hker : RingHom.ker φ = Q := by
    have e1 : RingHom.ker (IsScalarTower.toAlgHom A V (ResidueField V)) = maximalIdeal V :=
      ker_residue
    have e2 : RingHom.ker (IsScalarTower.toAlgHom A V' (ResidueField V')) = maximalIdeal V' :=
      ker_residue
    rw [Algebra.TensorProduct.map_ker _ _ residue_surjective residue_surjective, e1, e2, hL, hR,
      sup_idem]
  have hk : RingHom.ker (algebraMap A (ResidueField V)) = P := by
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V (ResidueField V),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  have hk' : RingHom.ker (algebraMap A (ResidueField V')) = P := by
    rw [hP]
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V' (ResidueField V'),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  obtain ⟨hred, hnt⟩ :=
    isReduced_nontrivial_tensor (k := ResidueField V) (k' := ResidueField V') P hk hk'
  have hrad : Q.IsRadical := by
    rintro x ⟨n, hn⟩
    rw [← hker, RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  have hne : Q ≠ ⊤ := by
    intro h
    have h1 : (1 : C) ∈ RingHom.ker φ := by rw [hker, h]; exact Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hm.isPrime
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q.IsPrime := hq.1.1
  let B := Localization.AtPrime q
  have hmax : Q.map (algebraMap C B) = maximalIdeal B := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes B q Q hq
    rw [← IsLocalization.map_radical q.primeCompl B, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact h1
  let g : V →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeLeft : V →ₐ[A] C) : V →+* C)
  let g' : V' →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeRight : V' →ₐ[A] C) : V' →+* C)
  have hgf : g.comp f = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := V) (B := V')).commutes a)
  have hgf' : g'.comp f' = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a)
  rw [AlgHom.coe_ideal_map] at hL hR
  refine ⟨B, inferInstance, inferInstance, g, g', hgf.trans hgf'.symm, ?_, ?_, ?_⟩
  · have h1 : (algebraMap C B).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat B q.primeCompl)
    have h2 : (algebraMap V C).Flat := RingHom.flat_algebraMap_iff.2 (Module.Flat.baseChange A V V')
    exact RingHom.Flat.comp h2 h1
  · rw [← Ideal.map_map, hL, hmax]
  · rw [← Ideal.map_map, hR, hmax]

end GlobalTheory.UnramPushout
end

