module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.ComplexSpanBlockActionStable
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem at_infinity_unitary (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (τ : ι) :
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ =
      gramC J emb τ := by
  have h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ =
      (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ) := by
    ext a b
    simp [atInf, cT, conjTranspose_apply, hc]
  rw [e]
  simp only [gramC, atInf]
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

theorem frame_translate_is_orthonormal (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) (hy : y.IsON) :
    (frameTranslate emb hc γ hγ y).IsON := fun τ => by
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) =
      (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ *
        atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = 1 ∨
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = -1
  rw [e, at_infinity_unitary emb hc γ hγ τ]
  exact hy τ

theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem forms_from_adelic_function (Tf : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (hφ : φ ∈ (D.fm u).Fi i) :
    ∃ g ∈ AdForms (Tf.cls i hi h0).lev (embT D) (lamT u i),
      ∀ c, φ c = fun z => g ((Tf.cls i hi h0).y c) ((Tf.val i hi h0).eY z) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi h0).Fi φ).1 hφ
  refine ⟨g, hg, fun c => ?_⟩
  funext z
  have := congrFun (congrFun hgφ c) ((Tf.val i hi h0).eY z)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.DiamondCommDistinctPlaces
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem adelic_GL_ext_local (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ w : HeightOneSpectrum (𝓞 F), bc (prV (E := E) w) g = bc (prV (E := E) w) h) : g = h := by
  ext i j
  have key : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w (g.1 i j - h.1 i j) = 0 := by
    intro w
    have := congrArg (fun x : GL (Fin n) (E ⊗[F] w.adicCompletion F) => x.1 i j) (H w)
    rw [map_sub]; exact sub_eq_zero.2 this
  exact sub_eq_zero.1 (Formalism.UG.P.afsplit_inj _ key)

theorem adelic_comm_disjoint_support (δ δ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v v' : HeightOneSpectrum (𝓞 F))
    (hvv : v ≠ v') (h1 : ∀ w, w ≠ v → bc (prV (E := E) w) δ = 1) (h2 : ∀ w, w ≠ v' → bc (prV (E := E) w) δ' = 1) :
    δ * δ' = δ' * δ := by
  apply adelic_GL_ext_local
  intro w
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw; rw [h2 w hvv, mul_one, one_mul]
  · rw [h1 w hw, mul_one, one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 1000000 in
theorem diamond_comm_distinct_places (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (v v' : (D.mem u).A.vT)
    (hvv : v ≠ v') (a : ((D.mem u).A.Fv v')ˣ) (b : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi h0).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi h0).y c) ((Tf.val i hi h0).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi h0).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi h0).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hdia : ∀ v0 a0 (ψ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) c,
      Formalism.MainNotions.product_first_zeroth_parts.dia D u i v0 a0 ψ c = (D.fm u).dilT i v0 a0 c (ψ ((D.fm u).dil i v0 a0 c)) := fun _ _ _ _ => rfl
  obtain ⟨ka, hka, δa, hδa⟩ := hE i hi h0 v' a
  obtain ⟨kb, hkb, δb, hδb⟩ := hE i hi h0 v b
  have hne : (Tf.atT.eV v).1 ≠ (Tf.atT.eV v').1 := fun h => hvv (Tf.atT.eV.injective (Subtype.ext h))
  have hcomm : δa * δb = δb * δa :=
    Subtype.ext (adelic_comm_disjoint_support δb.1 δa.1 _ _ hne hδb.1 hδa.1).symm
  have hga := adelic_function_right_translate_diamond (Tf.cls i hi h0).lev (embT D) _ _ (level_places_not_bad Tf.atT v') hδa hgA
  have hgb := adelic_function_right_translate_diamond (Tf.cls i hi h0).lev (embT D) _ _ (level_places_not_bad Tf.atT v) hδb hgA
  funext c
  have e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v' a c) =
      fun z => g ((Tf.cls i hi h0).y ((D.fm u).dil i v' a c) * δb) ((Tf.val i hi h0).eY z) := by
    rw [hdia, hval, (Tf.val i hi h0).dilT v b kb hkb _ δb hδb g hgA]
  have e2 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ ((D.fm u).dil i v b c) =
      fun z => g ((Tf.cls i hi h0).y ((D.fm u).dil i v b c) * δa) ((Tf.val i hi h0).eY z) := by
    rw [hdia, hval, (Tf.val i hi h0).dilT v' a ka hka _ δa hδa g hgA]
  rw [hdia v' a, e1, (Tf.val i hi h0).dilT v' a ka hka c δa hδa _ hgb,
    hdia v b, e2, (Tf.val i hi h0).dilT v b kb hkb c δb hδb _ hga]
  funext z
  simp only [mul_assoc, hcomm]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
end

