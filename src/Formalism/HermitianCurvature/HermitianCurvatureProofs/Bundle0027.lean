module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.StatementC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HsVecApply
section
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : Wq →L[ℂ] Wp :=
  LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => v i))

lemma hsInv_basis (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (i : Fin (Module.finrank ℂ Wq)) :
    hsInv v (stdOrthonormalBasis ℂ Wq i) = v i := by
  have := (stdOrthonormalBasis ℂ Wq).toBasis.constr_basis ℂ (fun i => v i) i
  simpa [hsInv] using this

lemma hsVec_apply' (A : Wq →L[ℂ] Wp) (i : Fin (Module.finrank ℂ Wq)) :
    hsVec A i = A (stdOrthonormalBasis ℂ Wq i) := rfl

lemma hsInv_hsVec (A : Wq →L[ℂ] Wp) : hsInv (hsVec A) = A := by
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis]
  rw [hsInv_basis, hsVec_apply']

lemma hsVec_hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : hsVec (hsInv v) = v := by
  ext i
  rw [hsVec_apply', hsInv_basis]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by ext i; simp [hsVec_apply']
  map_smul' c A := by ext i; simp [hsVec_apply']
  invFun := hsInv
  left_inv := hsInv_hsVec
  right_inv := hsVec_hsInv

def conjE (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)

def adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap
    (hsE.symm.toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (conjE T)).toLinearMap ∘ₗ hsE.toLinearMap)

lemma hsE_adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsVec (adjH T B) = ContinuousLinearMap.adjoint (conjE T) (hsVec B) := by
  show hsE (hsE.symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma conjE_hsVec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by
  show hsE (T (hsE.symm (hsE A))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem adjH_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by
  unfold hsInner
  rw [hsE_adjH, ContinuousLinearMap.adjoint_inner_left, conjE_hsVec]

lemma adjH_add (T S : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (T + S) = adjH T + adjH S := by
  ext B : 1
  apply hsE.injective
  simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
  show hsVec (adjH (T + S) B) = hsVec (adjH T B) + hsVec (adjH S B)
  rw [hsE_adjH, hsE_adjH, hsE_adjH]
  have : conjE (T + S) = conjE T + conjE S := by
    ext v : 1; simp [conjE]
  rw [this, map_add (f := _), ContinuousLinearMap.add_apply]

lemma adjH_smulC (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = (starRingEnd ℂ c) • adjH T := by
  ext B : 1
  apply hsE.injective
  show hsVec (adjH (c • T) B) = hsE (((starRingEnd ℂ c) • adjH T) B)
  rw [ContinuousLinearMap.smul_apply, map_smul]
  show _ = (starRingEnd ℂ c) • hsVec (adjH T B)
  rw [hsE_adjH, hsE_adjH]
  have : conjE (c • T) = c • conjE T := by
    ext v : 1; simp [conjE]
  rw [this, map_smulₛₗ, ContinuousLinearMap.smul_apply]

lemma adjH_smul (c : ℝ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = c • adjH T := by
  rw [← Complex.coe_smul, adjH_smulC, Complex.conj_ofReal, Complex.coe_smul]

def adjR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
  LinearMap.toContinuousLinearMap
    { toFun := adjH
      map_add' := adjH_add
      map_smul' := adjH_smul }

end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
section
namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

open scoped ComplexOrder

noncomputable section

open Classical

namespace Cx1

theorem psd_pullback {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by
  simp only [TB.PSDOn] at h ⊢
  exact h.submatrix (fun x : Y => (⟨φ x, hZ x x.2⟩ : Z))

theorem psd_zero {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (0 : ℂ)) := by
  simp only [TB.PSDOn]
  exact Matrix.PosSemidef.zero

end Cx1

theorem gram_positive_semidefinite : C.GramPSDOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hP _ Kr hK0 Th e ε hε i w Y
  show TB.PSDOn Y (S.gram ε i w.1)
  have prodPSD : ∀ (s : Finset (Fin S.f)) (k : Fin S.f → TB.Pt E → TB.Pt E → ℂ),
      (∀ v, TB.PSDOn Y (k v)) → TB.PSDOn Y (fun p q => ∏ v ∈ s, k v p q) := by
    intro s k hk
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, TB.PSDOn]
      let A : Matrix Unit Y ℂ := Matrix.of fun _ _ => 1
      have h2 := Matrix.posSemidef_conjTranspose_mul_self A
      convert h2 using 1
      ext x y
      simp [A, Matrix.mul_apply]
    | @insert a s ha ih =>
      simp only [TB.PSDOn] at ih ⊢
      have h1 : (Matrix.of fun x y : Y => ∏ v ∈ insert a s, k v x y) =
          (Matrix.of fun x y : Y => k a x y).hadamard (Matrix.of fun x y : Y => ∏ v ∈ s, k v x y) := by
        ext x y
        simp [Finset.prod_insert ha, Matrix.hadamard]
      rw [h1]
      exact (hk a).hadamard ih
  by_cases hi : i ≤ S.G.r + 1
  · have hg : S.gram ε i w.1 =
        fun p q => ∏ v, S.gramLoc v ε i (w.1 v) (loc (S.σ v) p) (loc (S.σ v) q) := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact prodPSD Finset.univ _ fun v =>
      Cx1.psd_pullback Y (loc (S.σ v)) _ _ (fun x hx => Finset.mem_image_of_mem _ hx)
        (hP v ε hε i hi w _)
  · have hg : S.gram ε i w.1 = fun _ _ => 0 := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact Cx1.psd_zero Y

theorem words_pos_of_parts : C.WordsPosOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG Kr hK0 Th e w
  show 0 < Word.size S.P w.1
  unfold Word.size
  apply Finset.prod_pos
  intro v _
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply abs_pos.mpr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hadm := w.2.1.1 v j hj
  by_cases hb : ((w.1 v)[j]'hj).1 = true
  · rw [if_pos hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact ((hG v).2.2.2.2.2 _ hy).2.2.1
  · rw [if_neg hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := ((hG v).2.2.2.2.2 _ hy).2.2.2
    rwa [sub_add_cancel] at this

theorem wave_estimate_of_integral : C.EstWaveOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG hI hP Kr hK0 Th e ε hε i hi1 hi2 w hw hcnt
  obtain ⟨θ, hθ, hb⟩ := hP ε hε i hi1 hi2 w hw hcnt
  exact ⟨θ, hθ, fun Y hY κ hκ => ⟨(hI ε hε i hi1 hi2 w Y hY κ hκ).2,
    fun l hl hl0 => ⟨S.bigPlaces i l, hb Y hY κ hκ l hl hl0⟩⟩⟩

theorem lift_estimate_of_base : C.EstLiftOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S h Kr hK0 Th e
  exact h

theorem block_estimate_of_base : C.EstBlockOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S C₄ h Kr hK0 Th e
  exact h

theorem level_zero_estimate_product : C.EstEOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S jv hG hE Kr hK0 Th e w _
  have hgram : ∀ ε, (S.mkData Kr hK0 Th e).gram ε 0 w [] [] = ∏ v, (S.pd v).RR ε 0 (w.1 v) [] [] := by
    intro ε
    show S.gram ε 0 w.1 [] [] = _
    simp [HidaSetting.gram, HidaSetting.gramLoc, loc, nLoc, nAux]
  have hsize : (S.mkData Kr hK0 Th e).wt w = ∏ v, S.sizeAt v (w.1 v) := rfl
  have hpos : 0 < ∏ v, S.sizeAt v (w.1 v) := by
    rw [← hsize]
    exact words_pos_of_parts E Wp Wq S hG Kr hK0 Th e w
  have hlim : Tendsto (fun ε => ∏ v, (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) :=
    tendsto_finsetProd _ (fun v _ => hE w v)
  have hre := ((Complex.continuous_re.tendsto _).comp hlim).div_const (∏ v, S.sizeAt v (w.1 v))
  have key : (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ)).re /
      (∏ v, S.sizeAt v (w.1 v)) = ∏ v, jv v := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
      mul_div_cancel_left₀ _ hpos.ne']
  rw [key] at hre
  simp_rw [hgram, hsize]
  exact hre

theorem cutoff_of_parts : C.CutoffOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S H _ _ Vt hPG Kr hK0 Th e Y hY
  filter_upwards [hPG Y hY] with ε hε p hp q hq _
  exact hε p hp q hq

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x2

variable {m : ℕ}

lemma ut_bt {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.BlockTriangular id :=
  fun i j h => hu.1 i j h

lemma lt_bt {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.BlockTriangular OrderDual.toDual :=
  fun i j h => hl.1 i j (OrderDual.toDual_lt_toDual.mp h)

lemma bt_mul_diag {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

lemma bt_inv_facts {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1) (hu : IsUnit M.det) :
    M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by
  haveI := M.invertibleOfIsUnitDet hu
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨hi, fun i => ?_⟩
  have := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) i) i
  rw [bt_mul_diag hb hM hi, hd, one_mul, Matrix.one_apply_eq] at this
  exact this

lemma ut_det {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (ut_bt hu)]
  simp [hu.2]

lemma lt_det {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (lt_bt hl)]
  simp [hl.2]

lemma ut_unit {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : IsUnit u.det := by
  rw [ut_det hu]; exact isUnit_one

lemma lt_unit {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : IsUnit l.det := by
  rw [lt_det hl]; exact isUnit_one

lemma ut_inv {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u⁻¹ ∈ C2.UTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts Function.injective_id (ut_bt hu) hu.2 (ut_unit hu)
  exact ⟨fun i j h => h1 h, h2⟩

lemma lt_inv {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l⁻¹ ∈ C2.LTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts OrderDual.toDual.injective (lt_bt hl) hl.2 (lt_unit hl)
  exact ⟨fun i j h => h1 (OrderDual.toDual_lt_toDual.mpr h), h2⟩

lemma ut_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hv : v ∈ C2.UTset m) :
    u * v ∈ C2.UTset m :=
  ⟨fun i j h => ((ut_bt hu).mul (ut_bt hv)) h,
   fun i => by rw [bt_mul_diag Function.injective_id (ut_bt hu) (ut_bt hv), hu.2, hv.2, one_mul]⟩

lemma lt_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.LTset m) (hv : v ∈ C2.LTset m) :
    u * v ∈ C2.LTset m :=
  ⟨fun i j h => ((lt_bt hu).mul (lt_bt hv)) (OrderDual.toDual_lt_toDual.mpr h),
   fun i => by rw [bt_mul_diag OrderDual.toDual.injective (lt_bt hu) (lt_bt hv), hu.2, hv.2, one_mul]⟩

lemma ut_conjT {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : uᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hu.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hu.2, star_one]⟩

lemma lt_conjT {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : lᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hl.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hl.2, star_one]⟩

lemma monomialMatrix_inv_left (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) * C2.monoP w d = 1 := by
  ext i j
  simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (w j)]
  · by_cases hij : i = j
    · subst hij; simp [hd i]
    · rw [if_neg (by simpa using hij), zero_mul, Matrix.one_apply_ne hij]
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

lemma isUnit_det_monomialMatrix (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) : IsUnit (C2.monoP w d).det :=
  Matrix.isUnit_det_of_left_inverse (monomialMatrix_inv_left w d hd)

lemma monomialMatrix_inv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP w d)⁻¹ = C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) :=
  Matrix.inv_eq_left_inv (monomialMatrix_inv_left w d hd)

lemma monomialMatrix_conj_apply (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((C2.monoP w d)⁻¹ * l * C2.monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, C2.monoP, Matrix.of_apply]
  rw [Finset.sum_eq_single (w b)]
  · rw [if_pos rfl, Finset.sum_eq_single (w a)]
    · simp
    · intro k _ hk
      rw [if_neg (fun e => hk (by rw [e]; simp)), zero_mul]
    · simp
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

lemma isMonomial_unit {P : Matrix (Fin m) (Fin m) ℂ} (hP : C2.IsMonomial P) : IsUnit P.det := by
  obtain ⟨w, d, hd, rfl⟩ := hP
  exact isUnit_det_monomialMatrix w d hd

end C2x2

open C2x2

theorem unipotent_radical_image : C2.URImage := by
  intro m P hP
  have hPu := isMonomial_unit hP
  ext u
  simp only [Set.mem_setOf_eq, C2.Lstg]
  constructor
  · rintro ⟨hu, u', hu', he⟩
    refine ⟨hu, ut_conjT hu, ?_⟩
    have : P⁻¹ * uᴴ * P = u'⁻¹ := by
      calc P⁻¹ * uᴴ * P = P⁻¹ * uᴴ * P * (u' * u'⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ (ut_unit hu'), Matrix.mul_one]
        _ = P⁻¹ * (uᴴ * P * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
    rw [this]; exact ut_inv hu'
  · rintro ⟨hu, _, hX⟩
    refine ⟨hu, (P⁻¹ * uᴴ * P)⁻¹, ut_inv hX, ?_⟩
    have e : uᴴ * P = P * (P⁻¹ * uᴴ * P) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_unit hX), Matrix.mul_one]

lemma c2x2_lowOf_sub {m : ℕ} (p : Fin m × Fin m → Prop) [DecidablePred p] (v : {q : Fin m × Fin m // p q} → ℂ)
    (i j : Fin m) :
    C2.lowOf (fun q : {q : Fin m × Fin m // p q} => q.1) v i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : p (i, j) then v ⟨(i, j), h⟩ else 0 := by
  simp only [C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e; apply hq; exact Subtype.ext e
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro e; apply h; rw [← e]; exact q.2

theorem lower_parabolic_coordinates : C2.LPCoords := by
  intro m w d hd
  have hPu := isUnit_det_monomialMatrix w d hd
  constructor
  · ext l
    simp only [Set.mem_range, C2.LPg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dite_eq_right (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_lt hab) (w.injective e)), dite_eq_right]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dite_eq_right (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm i < w.symm j := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact h'
            · exact absurd ⟨hij, h'⟩ h
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj
  · ext l
    simp only [Set.mem_range, C2.Lstg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dite_eq_right (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_gt hab) (w.injective e)), dite_eq_right]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dite_eq_right (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dite_eq_right (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm j < w.symm i := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact absurd ⟨hij, h'⟩ h
            · exact h'
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj

end Formalism.FourierDecayAlt.P
end

