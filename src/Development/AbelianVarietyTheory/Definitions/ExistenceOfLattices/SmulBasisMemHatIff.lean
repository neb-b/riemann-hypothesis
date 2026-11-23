module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

noncomputable section

namespace GlobalTheory.AdLat.Model

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]


open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.integral_iff (x : F) :
    (∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (h v)
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  · rintro ⟨r, rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have hv := HeightOneSpectrum.valuation_le_one (K := F) v r
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv
    exact hv

open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
  simp [_root_.GlobalTheory.AdLat.sg]


open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.hermA_smul_left (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (t : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (t • x) y = t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.hermA_smul_right (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (t : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (t • y) =
      _root_.GlobalTheory.AdLat.sg _ c t * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.AdLat.Model.hermA_symm (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, c (G a b) = G b a) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.hermA c G x y) =
      _root_.GlobalTheory.AdLat.hermA c G y x := by
  have hinv : ∀ z : _root_.GlobalTheory.AdLat.RA F E,
      _root_.GlobalTheory.AdLat.sg _ c (_root_.GlobalTheory.AdLat.sg _ c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [_root_.GlobalTheory.AdLat.sg, hc]
    | add u w hu hw => rw [map_add (f := _), map_add (f := _), hu, hw]
  have hG' : ∀ a b, _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G a b) = 1 ⊗ₜ[F] G b a := by
    intro a b
    simp [_root_.GlobalTheory.AdLat.sg, hG]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.GlobalTheory.AdLat.hermA, map_sum, map_mul, hinv, hG']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.AdLat.Model
