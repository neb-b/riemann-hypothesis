module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Th.ReducibleThreeDim

open TensorProduct in
private theorem bk_map {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {C : Type} [CommRing C] [Algebra ℚ_[l] C]
    {V : Type} [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
    {V' : Type} [AddCommGroup V'] [Module C V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C V'] [TopologicalSpace V']
    [IsTopologicalAddGroup V'] [ContinuousConstSMul C V']
    (ρ : Representation C (G F Ω) V) (ρ' : Representation C (G F Ω) V') (f : V →ₗ[C] V') (hfc : Continuous f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {γ : G F Ω → V} (h1 : γ ∈ Z1 ρ) (h2 : Af.IsBK l ρ γ) :
    (fun g => f (γ g)) ∈ Z1 ρ' ∧ Af.IsBK l ρ' (fun g => f (γ g)) := by
  refine ⟨⟨hfc.comp h1.1, fun g h => by simp only [h1.2 g h, map_add (f := _), hf]⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by simp only [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc, hcc⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    · have := congrArg f (hcc g h)
      rw [map_add (f := _)] at this
      exact this.trans (congrArg _ (hf _ _))
    · have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
          (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
          Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
            (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Loc.actC, hf]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
      rfl

section Alg

variable {R : Type} [CommRing R]

private def IsBlockSL2Embedding (x : GG (m := 3) (R := R)) : Prop :=
  ∃ a b c d : R, a * d - b * c = 1 ∧ x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]

private theorem theta_eq (X : Matrix (Fin 3) (Fin 3) R) :
    thetaLie X = !![-X 2 2, -X 1 2, -X 0 2; -X 2 1, -X 1 1, -X 0 1; -X 2 0, -X 1 0, -X 0 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thetaLie, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem conj_eq (a b c d : R) (Y : Matrix (Fin 3) (Fin 3) R) :
    !![a, 0, b; 0, 1, 0; c, 0, d] * Y * !![d, 0, -b; 0, 1, 0; -c, 0, a] =
    !![(a * Y 0 0 + b * Y 2 0) * d - (a * Y 0 2 + b * Y 2 2) * c, a * Y 0 1 + b * Y 2 1,
        -(a * Y 0 0 + b * Y 2 0) * b + (a * Y 0 2 + b * Y 2 2) * a;
      Y 1 0 * d - Y 1 2 * c, Y 1 1, -Y 1 0 * b + Y 1 2 * a;
      (c * Y 0 0 + d * Y 2 0) * d - (c * Y 0 2 + d * Y 2 2) * c, c * Y 0 1 + d * Y 2 1,
        -(c * Y 0 0 + d * Y 2 0) * b + (c * Y 0 2 + d * Y 2 2) * a] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem ad_eq {x : GG (m := 3) (R := R)} {a b c d : R} (h : a * d - b * c = 1)
    (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun X = !![a, 0, b; 0, 1, 0; c, 0, d] * (if x.right = 1 then X else thetaLie X) *
      !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
  have : ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    change x.mat * _ = 1
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination h
  rw [GG.adFun, this, hx]

private def pA : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun X := !![X 0 0, X 0 2; X 2 0, X 2 2]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private def sA : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun Y := !![Y 0 0, 0, Y 0 1; 0, 0, 0; Y 1 0, 0, Y 1 1]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private def pB (t : R) : Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 2 → R) where
  toFun X := ![X 0 1 + t * X 1 2, X 2 1 - t * X 1 0]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a X := by ext i; fin_cases i <;> simp <;> ring

private def sB (t : R) : (Fin 2 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun v := !![0, v 0, 0; -(t * v 1), 0, t * v 0; 0, v 1, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

private def pC : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun X := !![0, 0, 0; 0, X 1 1, 0; 0, 0, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem decomp (u : R) (hu : 2 * u = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    X = sA (pA X) + u • sB 1 (pB 1 X) + u • sB (-1) (pB (-1) X) + pC (pC X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, pA, sB, pB, pC]
  · linear_combination (-X 0 1) * hu
  · linear_combination (-X 1 0) * hu
  · linear_combination (-X 1 2) * hu
  · linear_combination (-X 2 1) * hu

private theorem pA_sA (Y : Matrix (Fin 2) (Fin 2) R) : pA (sA Y) = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, pA]

private theorem ad_sA {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (Y : Matrix (Fin 2) (Fin 2) R) :
    sA (pA (x.adFun (sA Y))) = x.adFun (sA Y) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [sA, pA]

private theorem pA_ad {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pA (x.adFun X) = pA (x.adFun (sA (pA X))) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, ad_eq h hx, theta_eq, theta_eq, conj_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [sA, pA]

private def wOf (x : GG (m := 3) (R := R)) : Matrix (Fin 2) (Fin 2) R :=
  if x.right = 1 then corner x.mat else corner x.mat * Matrix.diagonal ![-1, 1]

private theorem wOf_eq {x : GG (m := 3) (R := R)} {a b c d : R} (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) :
    wOf x = if x.right = 1 then !![a, b; c, d] else !![-a, b; -c, d] := by
  have : corner x.mat = !![a, b; c, d] := by
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [wOf, this]
  split_ifs
  · rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem pB_ad {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    pB t (x.adFun X) = ((if x.right = 1 then 1 else t) • wOf x) *ᵥ pB t X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i
  split_ifs <;> fin_cases i <;>
    simp [pB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (a * X 1 2 + b * X 1 0) * ht | linear_combination (c * X 1 2 + d * X 1 0) * ht

private theorem ad_sB {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (v : Fin 2 → R) :
    sB t (((if x.right = 1 then 1 else t) • wOf x) *ᵥ v) = x.adFun (sB t v) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;>
    simp [sB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (c * v 0 - d * v 1) * ht | linear_combination (-a * v 0 + b * v 1) * ht

private theorem pC_ad {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pC (x.adFun X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [pC]

private theorem ad_pC {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun (pC X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [pC]

private theorem pA_ad_one {x : GG (m := 3) (R := R)} (hx : IsBlockSL2Embedding x) (h1 : x.right = 1) (w : GL (Fin 2) R)
    (hw : (w : Matrix (Fin 2) (Fin 2) R) = wOf x) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = (w : Matrix (Fin 2) (Fin 2) R) * Y * ((w⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [wOf_eq hx, if_pos h1] at hw
  have : ((w⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![d, -b; -c, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h
  rw [ad_eq h hx, if_pos h1, this, hw, conj_eq]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [sA, pA] <;> ring

private theorem pA_ad_c {x : GG (m := 3) (R := R)} (hx : x.mat = 1) (h1 : x.right = -1) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = -(Jmat R 2 * Yᵀ * Jmat R 2) := by
  have hx' : x.mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [hx]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [ad_eq (by ring) hx', if_neg (by rw [h1]; decide), theta_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sA, pA, Jmat, Fin.rev, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

private def repA {Γ : Type} [Group Γ] (r : Γ →* GG (m := 3) (R := R)) (hr : ∀ g, IsBlockSL2Embedding (r g)) :
    Representation R Γ (Matrix (Fin 2) (Fin 2) R) where
  toFun g := pA ∘ₗ adRep r g ∘ₗ sA
  map_one' := by
    refine LinearMap.ext fun Y => ?_
    simp [pA_sA]
  map_mul' g h := by
    refine LinearMap.ext fun Y => ?_
    change pA ((r (g * h)).adFun (sA Y)) = pA ((r g).adFun (sA (pA ((r h).adFun (sA Y)))))
    rw [ad_sA (hr h), map_mul, GG.adFun_mul]

private theorem pair_eq (w : Matrix (Fin 2) (Fin 2) R) :
    wᵀ * Jmat R 2 * (!![-1, 0; 0, 1] * w * !![-1, 0; 0, 1]) = w.det • Jmat R 2 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, Fin.rev] <;> ring

private theorem isBlock_reducible_three_dim {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) : IsBlockSL2Embedding (r0 η Ψ g) := by
  refine ⟨(Ψ g : R), 0, 0, ((Ψ g)⁻¹ : Rˣ), by simp, ?_⟩
  rw [GG.mat, unitaryThreeReflection_left, tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wt1]

private theorem pC_mem (X : Matrix (Fin 3) (Fin 3) R) : pC X ∈ gw R 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd (by decide) hab

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
private theorem cont_pA : Continuous (pA : Matrix (Fin 3) (Fin 3) R → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> exact continuous_id.matrix_elem _ _

private theorem cont_pB (t : R) : Continuous (pB t) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_id.matrix_elem 0 1).add (continuous_const.mul (continuous_id.matrix_elem 1 2))
  · exact (continuous_id.matrix_elem 2 1).sub (continuous_const.mul (continuous_id.matrix_elem 1 0))

omit [IsTopologicalRing R] in
private theorem cont_pC : Continuous (pC : Matrix (Fin 3) (Fin 3) R → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact continuous_id.matrix_elem 1 1

end Alg

end UpperTheory.V.Th.ReducibleThreeDim

