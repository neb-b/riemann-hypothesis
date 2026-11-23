module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

@[expose] public section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]


open MeasureTheory NumberField Matrix Finset in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
theorem _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) {γ : _root_.GlobalTheory.FlagMeas.MatInf E j}
    (hγ : γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ) (g : _root_.GlobalTheory.FlagMeas.MatInf E j) :
    _root_.GlobalTheory.FlagBase.latAt E j Λ (γ * g) = _root_.GlobalTheory.FlagBase.latAt E j Λ g := by
  obtain ⟨γ', hγΛ, hγ'⟩ := hγ
  have hγw : ∀ w : InfinitePlace E,
      Matrix.of (γ w) = (γ' : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    ext a b
    simp [hγ' w a b]
  have hinv : ∀ w : InfinitePlace E, (Matrix.of (γ w))⁻¹ =
      ((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).map w.embedding := fun w => by
    rw [hγw]
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  have key : ∀ (w : InfinitePlace E) (y : Fin j → E),
      (Matrix.of ((γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) =
        (Matrix.of (g w))⁻¹ *ᵥ
          (fun a => w.embedding ((((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a)) := by
    intro w y
    rw [_root_.GlobalTheory.OrbitTerm.of_mul, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    congr 1
    funext a
    exact (RingHom.map_mulVec w.embedding _ y a).symm
  unfold _root_.GlobalTheory.FlagBase.latAt
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨((γ'⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y, ?_, ?_⟩
    · rw [← hγΛ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
      exact hy
    · funext w
      exact (key w y).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(γ' : Matrix (Fin j) (Fin j) E) *ᵥ z, (hγΛ z).mpr hz, ?_⟩
    funext w
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

end GlobalTheory.FlagBase.Test
