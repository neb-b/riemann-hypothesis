module

public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianForms.DefsGH
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

structure GLevH (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v)))
    (lam : ∀ a v h, H a v h →* ℂˣ) where

  fr : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletion F)
  fr_lat : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) (x : Fin n → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ b, G.phi a v h (y b) = x b) ↔
      ∀ b, (((fr a v h)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  mem : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb,
    x ∈ S.Uloc v ↔ ∃ M ∈ H a v h, (M : Matrix (Fin n) (Fin n) (kv F v)) = redM F v (G.mat a v h (fr a v h) x)

  red : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), S.U → H a v h
  red_eq : ∀ a v h (x : S.U), (((red a v h x : H a v h) : GL (Fin n) (kv F v)) : Matrix (Fin n) (Fin n) (kv F v)) =
    redM F v (G.mat a v h (fr a v h) (bc (prV (E := E) v) x.1))

  chi_eq : ∀ x : S.U, (S.chi x : ℂ) = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal),
    (((lam a v h (red a v h x) : ℂˣ) : ℂ))⁻¹

  chi_unit : ∀ x : S.U, ‖(S.chi x : ℂ)‖ = 1

end Loc

end Formalism.L2.Forms
end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.FramesLemmas
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ}

def Frames.tr (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det) (y : Frames G) : Frames G :=
  ⟨fun τ => g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hg τ).mul (y.2 τ)⟩

theorem Frames.isTr_tr (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det) (y : Frames G) :
    IsTr g y (y.tr g hg) := fun _ => rfl

theorem Frames.IsON.tr {y : Frames G} (hy : y.IsON) (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (hu : ∀ τ, (g τ)ᴴ * G τ * g τ = G τ) : (y.tr g hg).IsON := fun τ => by
  have e : (g τ * y.1 τ)ᴴ * G τ * (g τ * y.1 τ) = (y.1 τ)ᴴ * ((g τ)ᴴ * G τ * g τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (g τ * y.1 τ)ᴴ * G τ * (g τ * y.1 τ) = 1 ∨ (g τ * y.1 τ)ᴴ * G τ * (g τ * y.1 τ) = -1
  rw [e, hu τ]
  exact hy τ

variable {E : Type} [Field E]

theorem isUnit_det_atInf (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    IsUnit (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det := by
  have h : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det = emb τ (γ : Matrix (Fin n) (Fin n) E).det := by
    simp only [atInf]
    exact ((emb τ).map_det _).symm
  rw [h]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)

theorem atInf_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem exists_isTr' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Frames G) :
    ∃ y' : Frames G, IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) y' y :=
  ⟨y.tr _ (isUnit_det_atInf emb γ⁻¹), fun τ => by
    show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
      (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]⟩

theorem exists_isON_of_gram (σ : E →+* E) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (J : Matrix (Fin n) (Fin n) E) (C : GL (Fin n) E) (hC : cT σ C.1 * C.1 = J) :
    ∃ o : Frames (gramC J emb), o.IsON := by
  have hu : ∀ τ, IsUnit (atInf emb (C : Matrix (Fin n) (Fin n) E) τ).det := isUnit_det_atInf emb C
  have hJ : ∀ τ, gramC J emb τ = (atInf emb (C : Matrix (Fin n) (Fin n) E) τ)ᴴ * atInf emb (C : Matrix (Fin n) (Fin n) E) τ := by
    intro τ
    rw [← hC]
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramC, atInf, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, conjTranspose_apply, cT, Matrix.transpose_apply, hc]
    rfl
  refine ⟨⟨fun τ => (atInf emb (C : Matrix (Fin n) (Fin n) E) τ)⁻¹, fun τ => ?_⟩, fun τ => Or.inl ?_⟩
  · rw [det_nonsing_inv]; exact (hu τ).ringInverse
  · show ((atInf emb (C : Matrix (Fin n) (Fin n) E) τ)⁻¹)ᴴ * gramC J emb τ * (atInf emb (C : Matrix (Fin n) (Fin n) E) τ)⁻¹ = 1
    rw [hJ τ, conjTranspose_nonsing_inv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [det_conjTranspose]; exact (hu τ).star), Matrix.one_mul, Matrix.mul_nonsing_inv _ (hu τ)]

end Gen

end Formalism.L2.Forms
end
end

