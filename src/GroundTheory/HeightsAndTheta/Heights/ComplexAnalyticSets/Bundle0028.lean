module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

theorem NullSmaller.ringKrullDim_le_of_lt_succ {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'

theorem NullSmaller.proof : NullSmaller.Statement := by
  intro n d J hJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have htop : J = ⊤ := by
      by_contra h
      have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.2 h
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      exact absurd (h0.trans_lt hJ) (by simp)
    have hempty : zeroSetEuc J = ∅ := by
      ext z
      simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
    rw [hempty, measure_empty]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk := ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)
    have hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]
      refine hk.trans_lt ?_
      have : 2 * k < 2 * (k + 1) := by omega
      exact_mod_cast this
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    simpa using h0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothExtensionStep
section
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

theorem exists_isGoodPartialLift_extend (p : ℕ) [hp : Fact p.Prime] [CharP K p] {N : Ideal B}
    {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B} (hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p)
    {L : IntermediateField F K} {φ : L →ₐ[F] B} (hgood : IsGoodPartialLift p N u ψ ⟨L, φ⟩) {x : K}
    (hx : x ∉ L) :
    ∃ σ : Σ L : IntermediateField F K, L →ₐ[F] B,
      IsGoodPartialLift p N u ψ σ ∧ PartialLiftLE ⟨L, φ⟩ σ ∧ x ∈ σ.1 := by
  let _ : Algebra L B := φ.toRingHom.toAlgebra
  have : IsScalarTower F L B := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨hxp, hφx⟩ := hgood.1 x
  let a : L := ⟨x ^ p, hxp⟩
  have hirr : Irreducible (X ^ p - Polynomial.C a) := X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hx (by
    have hb' : (b : K) ^ p = x ^ p := congrArg Subtype.val hb
    have hbx := frobenius_inj K p (show frobenius K p (b : K) = frobenius K p x by
      rw [frobenius_def, frobenius_def]; exact hb')
    rw [← hbx]
    exact b.2)
  have hmonic : (X ^ p - Polynomial.C a).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hxroot : aeval x (X ^ p - Polynomial.C a) = 0 := by simp [a]
  have hmin : minpoly L x = X ^ p - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hxroot hmonic).symm
  have hint : IsIntegral L x := ⟨_, hmonic, hxroot⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
  have hroot : aeval c (minpoly L pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, map_sub, map_pow,
      aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    show c ^ p - φ a = 0
    rw [hφx, hψ x c hc, sub_self]
  let σ₁ := pb.lift c hroot
  let L' : IntermediateField F K := IntermediateField.restrictScalars F (L⟮x⟯)
  let σ : L' →ₐ[F] B := σ₁.restrictScalars F
  have hLL' : L ≤ L' := fun y hy => (L⟮x⟯).algebraMap_mem ⟨y, hy⟩
  have hext : ∀ y : L, σ (IntermediateField.inclusion hLL' y) = φ y := fun y => σ₁.commutes y
  have hring : (Ideal.Quotient.mk N).comp (algebraMap L B) = (u : K →+* B ⧸ N).comp (algebraMap L K) :=
    RingHom.ext fun l => hgood.2 l
  refine ⟨⟨L', σ⟩, ⟨fun z => ?_, fun y => ?_⟩, ⟨hLL', hext⟩, IntermediateField.mem_adjoin_simple_self L x⟩
  · obtain ⟨h, h'⟩ := hgood.1 z
    exact ⟨hLL' h, (hext ⟨_, h⟩).trans h'⟩
  · obtain ⟨f, hf⟩ := pb.exists_eq_aeval' ⟨y.1, y.2⟩
    have hy : (y : K) = aeval x f := by
      have h' := congrArg (algebraMap (L⟮x⟯) K) hf
      rw [← Polynomial.aeval_algebraMap_apply, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.AdjoinSimple.algebraMap_gen] at h'
      exact h'
    show Ideal.Quotient.mk N (σ₁ ⟨y.1, y.2⟩) = u y
    rw [hf, PowerBasis.lift_aeval, hy, aeval_def, aeval_def, Polynomial.hom_eval₂, hring, hc]
    exact (Polynomial.hom_eval₂ _ _ _ _).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

namespace PrimitiveElementFibres

variable {n d : ℕ}

theorem algebraMap_C_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (a : ℂ) :
    projHom J A (C a) = Ideal.Quotient.mk J (C a) := by
  simp [projHom, pullback]
  rfl

theorem adjoin_eq_top (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    (letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤) := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro b -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a) :=
      (algebraMap_C_eq J A a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) (hx : x ∈ zeroSet J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
  Ideal.Quotient.lift J (eval x) (fun q hq => hx q hq)

theorem evalAt_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {y : Fin d → ℂ} {x : Fin n → ℂ} (hx : x ∈ fibre J A y) (P : MvPolynomial (Fin d) ℂ) :
    evalAt J x hx.1 (projHom J A P) = eval y P := by
  change eval x (pullback A P) = _
  rw [FibreBound.eval_pullback, hx.2]

theorem proof : PrimitiveElementFibres.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) := hA.injective
  obtain ⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩ :=
    PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ))
      (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)
  set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ
  have hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact algebraMap_C_eq J A (c j)

  have hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)),
      evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j) := by
    intro y x hx p
    have h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y :=
      RingHom.ext fun P => evalAt_projHom J A hx P
    have h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j := by
      rw [hℓmk]
      change eval x (∑ j, C (c j) * X j) = _
      simp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]
  refine ⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩
  ·
    have h := congrArg (Polynomial.map (eval y)) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]
    exact ⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y),
      by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · have h := congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)
      rw [hev y x hx, map_zero] at h
      exact h
    · have h := congrArg (evalAt J x hx.1) (hQ j)
      have h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) =
          eval y D := evalAt_projHom J A hx D
      have h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j := by simp [evalAt]
      rw [hev y x hx, map_mul, h3, h4] at h
      exact h
  ·
    intro τ hτ
    let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := (Polynomial.aeval ℓ).toRingHom.toAlgebra
    set_option synthInstance.maxHeartbeats 100000 in
      have : IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
        IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
    have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩
    let evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))
    have hmax : (RingHom.ker evτ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)
    have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ := by
      intro p hp
      obtain ⟨q, rfl⟩ := (hdiv p).mp hp
      rw [RingHom.mem_ker, map_mul]
      have : evτ m = 0 := hτ
      rw [this, zero_mul]
    obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker
    have hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ P.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    have hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P := by
      intro p hp
      have : p ∈ (RingHom.ker evτ) := hp
      rw [← hPc] at this
      exact this
    have hxZ : x ∈ zeroSet J :=
      fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)
    refine ⟨x, ⟨hxZ, ?_⟩, ?_⟩
    · funext i
      have h1 := hover (Polynomial.C (X i - C (y i))) (by simp [evτ])
      rw [Polynomial.aeval_C] at h1
      have h2 := hmem (pullback A (X i - C (y i))) h1
      rw [FibreBound.eval_pullback] at h2
      simpa [sub_eq_zero] using h2
    · have h1 := hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk] at h1
      have h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ) := algebraMap_C_eq J A τ
      rw [h3, ← map_sub] at h1
      have h2 := hmem _ h1
      simpa [sub_eq_zero] using h2

end PrimitiveElementFibres

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionBranchLocus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionBranchLocus.proof (hL : ProperOpenProjectionLocalCover.Statement)
    (hH : FibreDiscriminantHolomorphic.Statement) (hM : MaximalCountUnbranched.Statement) :
    ProperOpenProjectionBranchLocus.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hDc hDne hmaps hprop hopen
  have loc := hL σ X B k f d A D hB hf hXB hDo hmaps hprop hopen
  choose! U g n hUo hyU hUD hg hgd hle hgen using loc

  have key : ∀ y₀ ∈ D, ∀ y ∈ U y₀, n y = n y₀ := by
    intro y₀ hy₀ y hy
    have hyD : y ∈ D := hUD y₀ hy₀ hy
    obtain ⟨t₁, ht₁, hgt₁⟩ := hgd y₀ hy₀ (U y ∩ U y₀) ((hUo y hyD).inter (hUo y₀ hy₀))
      Set.inter_subset_right ⟨y, hyU y hyD, hy⟩
    have hWo : IsOpen (U y ∩ (U y₀ ∩ g y₀ ⁻¹' {0}ᶜ)) :=
      (hUo y hyD).inter ((hg y₀ hy₀).continuousOn.isOpen_inter_preimage (hUo y₀ hy₀) isOpen_compl_singleton)
    obtain ⟨t, ht, hgt⟩ := hgd y hyD _ hWo Set.inter_subset_left
      ⟨t₁, ht₁.1, ht₁.2, by simpa using hgt₁⟩
    have e1 := (hgen y hyD t ht.1 hgt).1
    have e2 := (hgen y₀ hy₀ t ht.2.1 (by simpa using ht.2.2)).1
    exact_mod_cast e1.symm.trans e2
  obtain ⟨y₀, hy₀⟩ := hDne
  have hcont : ContinuousOn n D := by
    intro y hy
    have hc0 : ContinuousAt (fun _ : Fin d → ℂ => n y) y := continuousAt_const
    have hca : ContinuousAt n y := by
      refine hc0.congr ?_
      filter_upwards [(hUo y hy).mem_nhds (hyU y hy)] with z hz
      exact (key y hy z hz).symm
    exact hca.continuousWithinAt
  have hN : ∀ y ∈ D, n y = n y₀ := fun y hy => hDc.constant hcont hy hy₀

  have hcov : IsGenericCountCover (X ∩ B) A D (n y₀) := by
    refine ⟨fun y hy => ?_, fun y hy => ⟨U y, g y, hUo y hy, hyU y hy, hUD y hy, hg y hy, hgd y hy,
      fun z hz hgz => ?_⟩⟩
    · have := hle y hy y (hyU y hy)
      rwa [hN y hy] at this
    · obtain ⟨h1, h2⟩ := hgen y hy z hz hgz
      exact ⟨by rw [h1, hN y hy], h2⟩

  obtain ⟨ys, hysU, hgys⟩ := hgd y₀ hy₀ (U y₀) (hUo y₀ hy₀) subset_rfl ⟨y₀, hyU y₀ hy₀⟩
  have hysD : ys ∈ D := hUD y₀ hy₀ hysU
  have hcys : {x | x ∈ X ∩ B ∧ A x = ys}.encard = (n y₀ : ℕ∞) := (hgen y₀ hy₀ ys hysU hgys).1
  have hfin := Set.finite_of_encard_eq_coe hcys
  obtain ⟨l₀, hl₀⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun p : hfin.toFinset.offDiag => (p.1.1 - p.1.2 : σ → ℂ))
    (fun p => sub_ne_zero.2 (Finset.mem_offDiag.1 p.2).2.2)
  let l : (σ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  refine ⟨fibreDiscr (X ∩ B) A l (n y₀), hH σ (X ∩ B) d A D (n y₀) l hDo hmaps hprop hopen hcov,
    ⟨ys, hysD, ?_⟩, ?_⟩
  · unfold fibreDiscr
    rw [dite_eq_left hcys, Finset.prod_ne_zero_iff]
    intro p hp
    have := hl₀ ⟨p, hp⟩
    simpa [l, map_sub, sub_eq_zero] using this
  · intro x hx hδ
    have hc : {x' | x' ∈ X ∩ B ∧ A x' = A x}.encard = (n y₀ : ℕ∞) := by
      by_contra hne
      exact hδ (by unfold fibreDiscr; rw [dite_eq_right hne])
    exact hM σ (X ∩ B) d A D (n y₀) hDo hmaps hprop hopen hcov x hx hc

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRootSumHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Filter Topology

noncomputable section

theorem RootSumHolomorphic.proof : RootSumHolomorphic.Statement := by
  intro d m W Φ hm hW hsep hΦ y₀ hy₀
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (MvPolynomial.eval y₀)).roots.toFinset := ⟨_, rfl⟩
  have hroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).IsRoot τ := fun τ hτ => by
    rw [hR] at hτ
    exact (Polynomial.mem_roots (hm.map _).ne_zero).1 (Multiset.mem_toFinset.1 hτ)
  have hder : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).derivative.eval τ ≠ 0 := fun τ hτ => by
    have h := (hsep y₀ hy₀).eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ)
      (by rw [Polynomial.eval₂_id]; exact hroot τ hτ)
    rwa [Polynomial.eval₂_id] at h
  have hbr := fun τ (hτ : τ ∈ R) => SimpleRootBranch.proof d m y₀ τ (hroot τ hτ) (hder τ hτ)
  choose! U B ψ hUo hyU hBo hτB hψd hψy hψroot using hbr
  have hloc := fun τ (hτ : τ ∈ R) => hΦ y₀ hy₀ τ (hroot τ hτ)
  choose! O hOo hyO Ψ hΨd hΨeq using hloc
  obtain ⟨V, hV, hVdisj⟩ := (R.finite_toSet).t2_separation

  have hev : ∀ᶠ y in 𝓝 y₀, ∀ τ ∈ R, y ∈ U τ ∧ ψ τ y ∈ B τ ∩ V τ ∧ (y, ψ τ y) ∈ O τ := by
    refine (Filter.eventually_all_finset R).2 fun τ hτ => ?_
    have hψc : ContinuousAt (ψ τ) y₀ :=
      ((hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))).continuousAt
    have hBV : B τ ∩ V τ ∈ 𝓝 (ψ τ y₀) := by
      rw [hψy τ hτ]; exact ((hBo τ hτ).inter (hV τ).2).mem_nhds ⟨hτB τ hτ, (hV τ).1⟩
    have hO : O τ ∈ 𝓝 (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hOo τ hτ).mem_nhds (hyO τ hτ)
    have hpc : ContinuousAt (fun y => (y, ψ τ y)) y₀ := continuousAt_id.prodMk hψc
    exact Filter.Eventually.and ((hUo τ hτ).mem_nhds (hyU τ hτ))
      (Filter.Eventually.and (hψc.preimage_mem_nhds hBV) (hpc.preimage_mem_nhds hO))

  have heq : ∀ᶠ y in 𝓝 y₀, ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum =
      ∑ τ ∈ R, Ψ τ (y, ψ τ y) := by
    filter_upwards [hev] with y hy
    have hisroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y)).IsRoot (ψ τ y) := fun τ hτ =>
      ((hψroot τ hτ y (hy τ hτ).1).2 _ (hy τ hτ).2.1.1).2 rfl
    have hinj : ∀ τ ∈ R.val, ∀ τ' ∈ R.val, ψ τ y = ψ τ' y → τ = τ' := by
      intro τ hτ τ' hτ' h
      by_contra hne
      have h' : ψ τ y ∈ V τ' := by rw [h]; exact (hy τ' hτ').2.1.2
      exact Set.disjoint_left.1 (hVdisj hτ hτ' hne) (hy τ hτ).2.1.2 h'
    have hM : R.val.map (fun τ => ψ τ y) = (m.map (MvPolynomial.eval y)).roots := by
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset (Multiset.Nodup.map_on hinj R.nodup)]
        intro s hs
        obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hs
        exact (Polynomial.mem_roots (hm.map _).ne_zero).2 (hisroot τ hτ)
      · have h1 : Multiset.card (R.val.map fun τ => ψ τ y) = m.natDegree := by
          rw [Multiset.card_map, Finset.card_val, hR,
            Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep y₀ hy₀)),
            IsAlgClosed.card_roots_eq_natDegree, hm.natDegree_map]
        rw [h1, ← hm.natDegree_map (MvPolynomial.eval y)]
        exact Polynomial.card_roots' _
    rw [← hM, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun τ hτ => ?_
    exact hΨeq τ hτ (y, ψ τ y) (hy τ hτ).2.2 (hisroot τ hτ)

  have hg : DifferentiableAt ℂ (fun y => ∑ τ ∈ R, Ψ τ (y, ψ τ y)) y₀ := by
    refine DifferentiableAt.fun_sum (A := fun τ y => Ψ τ (y, ψ τ y)) fun τ hτ => ?_
    have hψ : DifferentiableAt ℂ (ψ τ) y₀ :=
      (hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))
    have hΨ : DifferentiableAt ℂ (Ψ τ) (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hΨd τ hτ).differentiableAt ((hOo τ hτ).mem_nhds (hyO τ hτ))
    exact hΨ.comp y₀ (differentiableAt_id.prodMk hψ)
  exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphBound.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      ∀ δ : ℝ≥0, 0 < δ → δ < 1 →
        μH[(k : ℝ)] (realGraphPt F '' A) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ∧
          ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) * μH[(k : ℝ)] (realGraphPt F '' A)

end

end GroundTheory.Heights₂.Heights
end

