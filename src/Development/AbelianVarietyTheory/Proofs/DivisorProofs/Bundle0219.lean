module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFinite
section
open IsLocalRing
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.NormFin

theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationMulEqAevalRoot
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial TensorProduct

theorem tensor_exists_smul_eq_eval₂ (S K L : Type) [CommRing S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] (π : S) (e : ℕ) (D : Type) [CommRing D]
    [Algebra S D] (φ : D ≃ₐ[S] AdjoinRoot (X ^ e - C π)) (z : TensorProduct S D L) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (TensorProduct S D L) s * z =
        f.eval₂ ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp
            (integralClosure S L).val).toRingHom
          (algebraMap D (TensorProduct S D L) (φ.symm (AdjoinRoot.root (X ^ e - C π)))) := by
  set gA : integralClosure S L →ₐ[S] TensorProduct S D L :=
    (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp (integralClosure S L).val
  set t := φ.symm (AdjoinRoot.root (X ^ e - C π))
  have hg : ∀ s : S, gA.toRingHom (algebraMap S (integralClosure S L) s) =
      algebraMap S (TensorProduct S D L) s := fun s => gA.commutes s
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul d l =>
    have hl : IsAlgebraic S l :=
      (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨s, hs, hint⟩ := hl.exists_integral_multiple
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (φ d)
    have hd : d = aeval t p := by
      rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, hp]
      simp [t]
    refine ⟨C ⟨s • l, hint⟩ * p.map (algebraMap S (integralClosure S L)), s, hs, ?_⟩
    rw [eval₂_mul, eval₂_C, eval₂_map]
    have : (gA.toRingHom.comp (algebraMap S (integralClosure S L))) =
        algebraMap S (TensorProduct S D L) := RingHom.ext hg
    rw [this, ← aeval_def]
    have h2 : aeval (algebraMap D (TensorProduct S D L) t) p =
        algebraMap D (TensorProduct S D L) d := by
      rw [hd, aeval_algebraMap_apply]
    rw [h2]
    simp only [gA, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.coe_comp,
      Function.comp_apply, Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨f₁, s₁, hs₁, h₁⟩ := hx
    obtain ⟨f₂, s₂, hs₂, h₂⟩ := hy
    refine ⟨C (algebraMap S _ s₂) * f₁ + C (algebraMap S _ s₁) * f₂, s₁ * s₂,
      mul_ne_zero hs₁ hs₂, ?_⟩
    rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, hg, hg, ← h₁, ← h₂, map_mul]
    ring

theorem normalisation_mul_eq_aeval_root (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (φ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
    (b : integralClosure D (TensorProduct S D L)) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (integralClosure D (TensorProduct S D L)) s * b =
        Polynomial.aeval (algebraMap D (integralClosure D (TensorProduct S D L))
          (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) f := by
  obtain ⟨f, s, hs, h⟩ := tensor_exists_smul_eq_eval₂ S K L π e D φ (b : TensorProduct S D L)
  refine ⟨f, s, hs, Subtype.ext ?_⟩
  rw [aeval_def]
  have hc := Polynomial.hom_eval₂ f
    (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)))
    (integralClosure D (TensorProduct S D L)).val.toRingHom
    (algebraMap D (integralClosure D (TensorProduct S D L))
      (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val] at hc
  rw [hc]
  convert h using 2 <;> first | rfl | exact RingHom.ext fun _ => rfl
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem Reg.not_modEq_of_lt {q N k u v : ℕ} (hq : 2 ≤ q) (h : Reg q N k) (huv : u < v) (hv : v < u + N) :
    ¬ k * q ^ v ≡ k * q ^ u [MOD q ^ N - 1] := by
  intro hmod
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd0 : 0 < d := by omega
  have hdN : d < N := by omega
  have hN : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ N - 1) (q ^ u) := by
    obtain ⟨t, ht⟩ : ∃ t, q ^ N = t + 1 := ⟨q ^ N - 1, by have := Nat.one_le_pow N q (by omega); omega⟩
    have h2 : Nat.Coprime (q ^ N - 1) (q ^ N) := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right t)
    exact (h2.coprime_dvd_right (dvd_pow_self q hN.ne')).pow_right u
  have key : k * q ^ d ≡ k [MOD q ^ N - 1] := by
    apply Nat.ModEq.cancel_right_of_coprime (c := q ^ u) hcop
    have e : k * q ^ d * q ^ u = k * q ^ (u + d) := by ring
    rw [e]
    exact hmod
  exact h d hd0 hdN key

theorem reg_step_of_dvd : ∀ q l m k : ℕ, 2 ≤ q → 0 < l → 0 < m → Reg q (l * m) k →
    (∀ i, Reg (q ^ l) m (k * q ^ i)) ∧ (2 ≤ l * m → ∀ i, ¬ k * q ^ i ≡ 0 [MOD q ^ (l * m) - 1]) ∧
    ∀ i j a, i < l → j < l → a < m →
      (k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1] ↔ i = j ∧ a = 0) := by
  intro q l m k hq hl hm h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj0 hjm hmod
    simp only [← pow_mul] at hmod
    rw [mul_assoc, ← pow_add] at hmod
    have hlj : 0 < l * j := Nat.mul_pos hl hj0
    have hljm : l * j < l * m := (Nat.mul_lt_mul_left hl).mpr hjm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + l * j) (by omega : i + l * j < i + l * m) hmod
  · intro hlm i hmod
    have h1 : k * q ^ (i + 1) ≡ k * q ^ i [MOD q ^ (l * m) - 1] := by
      have e : k * q ^ (i + 1) = k * q ^ i * q := by ring
      rw [e]
      have h0 := hmod.mul_right q
      rw [zero_mul] at h0
      exact h0.trans hmod.symm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + 1) (by omega : i + 1 < i + l * m) h1
  · intro i j a hi hj ha
    constructor
    · intro hmod
      simp only [← pow_mul] at hmod
      rw [mul_assoc, ← pow_add] at hmod
      have hla : l * a + l ≤ l * m := by
        calc l * a + l = l * (a + 1) := by ring
          _ ≤ l * m := Nat.mul_le_mul_left l ha
      rcases lt_trichotomy (i + l * a) j with hlt | heq | hgt
      · exact absurd hmod.symm (Reg.not_modEq_of_lt hq h hlt (by omega))
      · rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · subst ha0
          simp at heq
          exact ⟨heq, rfl⟩
        · have := Nat.le_mul_of_pos_right l ha0
          omega
      · exact absurd hmod (Reg.not_modEq_of_lt hq h hgt (by omega))
    · rintro ⟨rfl, rfl⟩
      simp [Nat.ModEq]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceWeight

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_left {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖x‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)

theorem iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
  have hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V := V) κ κ') := by
    funext y'
    simp only [sliceR_apply, Function.comp_apply]
    exact congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')
  have hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]
  have h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y)
      = iteratedFDeriv ℝ n f (Sum.elim x y) := by
    rw [iteratedFDeriv_comp_add_left]
    congr 1
    exact (congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖(inrL (V := V) κ κ')‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
  calc _ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y

end GlobalTheory.SliceWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLift
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatLift

theorem projective_of_nilpotent_of_reduced_quotient (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hr : IsReduced (D ⧸ Ideal.span {x})) (N : Type 1) [AddCommGroup N] [Module D N]
    [Module.Finite D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    Module.Projective D N := by
  have hflat : Module.Flat D N := by
    apply Module.flat_of_localized_maximal
    intro P _
    have hloc := GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian D x hx hr P
    have hann := GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem D P.primeCompl x N h
    haveI := _root_.GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le (Localization.AtPrime P) (algebraMap D _ x) hloc
      (LocalizedModule P.primeCompl N) inferInstance hann
    exact Module.Flat.trans D (Localization.AtPrime P) _
  haveI : Module.FinitePresentation D N := Module.finitePresentation_of_finite D N
  exact Module.Flat.projective_of_finitePresentation

theorem projective_reduction_of_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  intro p _ F _ _ Λ _ k _ π hπ hker hp2 hann M _ _ _ _ hfin hfree N _ _ f hf hkerf
  have hpk : (p : k) = 0 := by
    have : (p : Λ) ∈ RingHom.ker π := by rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hkerp := _root_.GlobalTheory.ker_smul_le_ideal_smul_of_free Λ (p : Λ) hann M hfree
  have hkerf' : ∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M) := by
    intro m hm; rw [← hker]; exact hkerf m hm
  obtain ⟨ϖ, z, hϖz, ⟨n0, hn0⟩, hred⟩ := _root_.GlobalTheory.exists_global_uniformiser_above_prime p F
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k (k ⊗[ℤ] 𝓞 F)
  haveI : Module.Finite (k ⊗[ℤ] 𝓞 F) N := _root_.GlobalTheory.finite_of_surjective_tensor_semilinear Λ k π (𝓞 F) M hfin N f hf
  have hnil : IsNilpotent ((1 : k) ⊗ₜ[ℤ] ϖ) := by
    refine ⟨n0, ?_⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hn0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hy, mul_comm, ← nsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, mul_one, hpk,
      TensorProduct.zero_tmul]
  have hfinQ : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
    have hne : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
      simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero]
    haveI : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective
      (Ideal.span_mono (by simp : ({(p : 𝓞 F)} : Set (𝓞 F)) ⊆ {(p : 𝓞 F), ϖ})))
  have hredD := _root_.GlobalTheory.reduced_quot_tensor_of_reduced_modp (𝓞 F) k p ϖ hpk (_root_.GlobalTheory.FinRedTensor.isReduced_field_tensor_finite _ k)
  have hannN := GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt p (𝓞 F) Λ k π hpk hp2 M hkerp N f hf hkerf' ϖ z hϖz
  exact projective_of_nilpotent_of_reduced_quotient _ _ hnil hredD N hannN

end GlobalTheory.FlatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
section
open IsLocalRing

namespace GlobalTheory

def PurityFree (R : Type) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 →
    (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
    Module.Free R A

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem QAll.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {p : ℂ → Prop} {f : ℍ → ℂ}
    (h0 : p 0) (hf : QAll p N f) : QAll p N' f := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, hpa⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩
  unfold spread
  split_ifs
  · exact hpa _
  · exact h0

theorem QConj.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, ha'⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩
  have key : (fun n => g (spread M a n)) = spread M (fun n => g (a n)) := by
    funext n
    unfold spread
    split_ifs <;> simp
  rw [key]
  exact hasQ_mul_spread N M f' _ hN hM ha'

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  first | exact @GlobalTheory.QFam.QAllSubring.ring_closed | exact GlobalTheory.QFam.QAllSubring.ring_closed | (intros; apply GlobalTheory.QFam.QAllSubring.ring_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic : ∀ (p : ℕ) [Fact p.Prime], ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧ Function.Bijective (fun a => (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  first | (exact @GlobalTheory.AdeleSplitP.finiteAdele_split) | (exact GlobalTheory.AdeleSplitP.finiteAdele_split) | (intros; apply GlobalTheory.AdeleSplitP.finiteAdele_split  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityExpZModAdditiveCharacterProperties
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
end

