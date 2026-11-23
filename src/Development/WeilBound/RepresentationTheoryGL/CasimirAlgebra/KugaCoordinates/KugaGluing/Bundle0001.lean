module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgLieOpComm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgFormRTensor

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCasDiff
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ)

theorem kg_casR (τ : E →+* ℂ) (t : ℝ) (htrX : ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(t : ℂ))) :
    ∑ i, ∑ j, cx τ (kgR π Ξ σ) i j * cx τ (kgR π Ξ σ) j i =
      (Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V +
        ((2 * (σ / 2 : ℂ)) * (-(t : ℂ)) + (a : ℂ) * (σ / 2 : ℂ) ^ 2) • 1 := by
  let ΦR := (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin Ξ.d)).toAlgHom
  have hΦR : ∀ A : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ, (Matrix.toLin' A).lTensor π.V = ΦR A := fun A => rfl
  simp only [cx_kgR, hΦR]
  refine (kg_cas_shift (fun i j => ΦR (cx τ Ξ.dmat i j)) (σ / 2 : ℂ)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum, htrX, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  set_option synthInstance.maxHeartbeats 100000 in
    module

theorem kg_casA (τ : E →+* ℂ) (c t : ℝ)
    (hcas : ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (c : ℂ))
    (htr : ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (t : ℂ)) :
    ∑ i, ∑ j, cx τ (kgA π Ξ σ) i j * cx τ (kgA π Ξ σ) j i =
      ((c : ℂ) + (2 * (-(σ / 2 : ℂ))) * (t : ℂ) + (a : ℂ) * (-(σ / 2 : ℂ)) ^ 2) • 1 := by
  let ΦA := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hΦA : ∀ f : Module.End ℂ π.V, f.rTensor (Fin Ξ.d → ℂ) = ΦA f := fun f => rfl
  simp only [cx_kgA, hΦA]
  refine (kg_cas_shift (fun i j => ΦA (cx τ (lieOp π) i j)) (-(σ / 2) : ℂ)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum, hcas, htr, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  set_option synthInstance.maxHeartbeats 100000 in
    module

theorem kg_casDiff (hC : FrameCas) (cc tt : (E →+* ℂ) → ℝ)
    (hcas : ∀ τ, ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (cc τ : ℂ))
    (htr : ∀ τ, ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (tt τ : ℂ))
    (htrX : ∀ τ, ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(tt τ : ℂ))) :
    ((∑ k, kgR π Ξ σ (toL (fr k).1) * kgR π Ξ σ (toL (fr k).1) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
      (∑ k, kgA π Ξ σ (toL (fr k).1) * kgA π Ξ σ (toL (fr k).1) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
        Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) =
      (2 : ℂ) • ∑ τ, ((Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V - (cc τ : ℂ) • 1) := by
  rw [hC E a _ (kgR π Ξ σ), hC E a _ (kgA π Ξ σ)]
  refine (smul_sub (2 : ℂ) (_ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _).symm.trans (congrArg _ ?_)
  refine (Finset.sum_sub_distrib (G := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _ _).symm.trans
    (Finset.sum_congr rfl fun τ _ => ?_)
  rw [kg_casR π Ξ σ τ (tt τ) (htrX τ), kg_casA π Ξ σ τ (cc τ) (tt τ) (hcas τ) (htr τ)]
  set_option synthInstance.maxHeartbeats 100000 in
    module

end
end PositivityTheory.Rg.Cz
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCxDmatConj
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
theorem kg_star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (starRingEnd ℂ z) := by
  classical
  unfold atEmb
  funext w
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

theorem kg_cx_dmat_conj (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ)
    (τ : E →+* ℂ) (i j : Fin a) : (cx τ Ξ.dmat i j)ᴴ = cx τ Ξ.dmat j i := by
  have e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ =
      Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z)))) := by
    intro z; rw [← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]
  have e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) =
      -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I))) := by
    rw [← map_neg]
    congr 1
    funext k l
    show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)
    rw [Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]
    split_ifs <;> simp
  unfold cx
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one,
    Complex.conj_I, e2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  module

theorem kg_cas_herm (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) (τ : E →+* ℂ) :
    (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)ᴴ = ∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]

omit [NumberField E] in
theorem kg_star_iM {X : Matrix (Fin a) (Fin a) (Cinf E)} (hX : star X = X) : star (iM X) = -iM X := by
  ext i j w
  have h : star (X j i) = X i j := by rw [← Matrix.star_apply, hX]
  have h' : star (X j i w) = X i j w := congrFun h w
  simp only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul,
    Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]
  ring

def kgL : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a where
  toFun := toL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


omit [NumberField E] in
def kgD (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) : Herm E a →ₗ[ℝ] Herm E a where
  toFun Y := ⟨Z * Y.1 - Y.1 * Z, by
    have hY : star Y.1 = Y.1 := Y.2
    show star (Z * Y.1 - Y.1 * Z) = Z * Y.1 - Y.1 * Z
    rw [star_sub, star_mul, star_mul, hY, hZ, mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub]⟩
  map_add' Y Y' := Subtype.ext (by
    show Z * (Y.1 + Y'.1) - (Y.1 + Y'.1) * Z = (Z * Y.1 - Y.1 * Z) + (Z * Y'.1 - Y'.1 * Z)
    rw [mul_add, add_mul]; abel)
  map_smul' c Y := Subtype.ext (by
    show Z * (c • Y.1) - (c • Y.1) * Z = c • (Z * Y.1 - Y.1 * Z)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub])

omit [NumberField E] in
theorem kgD_val (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) :
    (kgD Z hZ Y).1 = Z * Y.1 - Y.1 * Z := rfl

end
end PositivityTheory.Rg.Cz
end
end

