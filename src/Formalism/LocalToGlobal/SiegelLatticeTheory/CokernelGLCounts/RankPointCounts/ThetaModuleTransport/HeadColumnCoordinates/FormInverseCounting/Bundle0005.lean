module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ProjPSurjective
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) {r : ℕ}

theorem kap_mul_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    kap O Z * (Z.map O.subtype).det = ((Z.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold kap
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, mul_comm (Ring.inverse _), mul_assoc,
    Ring.inverse_mul_cancel _ hu, mul_one, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [Fin.succAbove_last, ← two_mul, pow_mul]

theorem kap_eq (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hrel : ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₂.map O.subtype).det =
      ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₁.map O.subtype).det) :
    kap O Z₂ = kap O Z₁ := by
  have h1 := kap_mul_det O Z₁ hu₁
  have h2 := kap_mul_det O Z₂ hu₂
  rw [← h1, ← h2] at hrel
  apply (hu₁.mul hu₂).mul_right_cancel
  linear_combination -hrel

theorem stepPairG_of_fwd_bwd (hf : FwdEx) (hb : BwdEx) : StepPairG := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂
  let t : O := ⟨T, hT⟩
  let t' : O := ⟨T', hT'⟩
  have hk : kap O Z₂ = kap O Z₁ := kap_eq O Z₁ Z₂ hu₁ hu₂ hrel
  have hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E) := fun u h => eta_nzd O cj hcj Z₂ hu₂ T T' hG₂ u h
  have hf' := hf E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hG₁ hG₂
  have hb' := hb E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hG₁ hG₂
  choose F hF using hf'
  choose B hBmem hB using hb'
  have lamP : ∀ (p : PairSet O cj hO Z₁ Z₂) (m : MbMod Z₁),
      lamLQ O Z₂ hu₂ (p.1.1 m) = lamLQ O Z₁ hu₁ m := by
    intro p m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (p.1.1 (Submodule.Quotient.mk y))
    rw [← hy₂]
    exact lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y y₂ hy₂.symm
  have lamSP : ∀ (p : PairSet O cj hO Z₁ Z₂) (m : MbMod (cjT O cj hO Z₁)),
      lamSQ O cj hO Z₂ hu₂ (p.1.2 m) = lamSQ O cj hO Z₁ hu₁ m := by
    intro p m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (Submodule.Quotient.mk y))
    rw [← hy₂]
    exact p.2.2.1 y y₂ hy₂.symm
  refine Nat.card_congr
    { toFun := fun θ => F θ.1 θ.2
      invFun := fun p => ⟨B p, hBmem p⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨θ, hθ⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro d
    obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show B (F θ hθ) (Submodule.Quotient.mk Y) = θ (Submodule.Quotient.mk Y)
    rw [elim_eta O Y, mk_elim O cj hO Z₁ t t', map_add (f := _), map_add (f := _), (hB _).1, (hB _).2, (hF θ hθ).1,
      (hF θ hθ).2]
  · intro p
    set q := F (B p) (hBmem p)
    have hq := hF (B p) (hBmem p)
    apply Subtype.ext
    refine Prod.ext (LinearEquiv.ext fun m => ?_) (LinearEquiv.ext fun m => ?_)
    · refine uniqL O cj hO Z₂ hu₂ t t' hη₂ _ _ ?_ ?_
      · show iL O cj hO Z₂ t t' (q.1.1 m) = iL O cj hO Z₂ t t' (p.1.1 m)
        rw [← hq.1, (hB p).1]
      · show lamLQ O Z₂ hu₂ (q.1.1 m) = lamLQ O Z₂ hu₂ (p.1.1 m)
        rw [lamP, lamP]
    · refine uniqR O cj hO Z₂ hu₂ t t' hη₂ _ _ ?_ ?_
      · show iR O cj hO Z₂ t t' (q.1.2 m) = iR O cj hO Z₂ t t' (p.1.2 m)
        rw [← hq.2, (hB p).2]
      · show lamSQ O cj hO Z₂ hu₂ (q.1.2 m) = lamSQ O cj hO Z₂ hu₂ (p.1.2 m)
        rw [lamSP, lamSP]

theorem algAll_of (h : StepPairG) : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂
  rw [h E O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨stepInj E O cj hcj hO r Z₁ Z₂ hu₁ hu₂, stepAdjG E O cj hcj hO r Z₁ Z₂ hu₁ hu₂⟩)

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormPair
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem form_pair (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) (Y W : Ix r → O) :
    formC O cj (Z₂.map O.subtype) t t'
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
        (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
          (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
      formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.1.toLinearMap y) : MbMod Z₂) =
      p.1.1.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hr : ∀ y : Fin (r + 1) → O, (Submodule.Quotient.mk (liftOf O p.1.2.toLinearMap y) : MbMod (cjT O cj hO Z₂)) =
      p.1.2.toLinearMap (Submodule.Quotient.mk y) := fun y => liftOf_spec O _ y
  have hb : ∀ y y' : Fin (r + 1) → O,
      bRaw O cj Z₂ (liftOf O p.1.1.toLinearMap y) (liftOf O p.1.2.toLinearMap y') - bRaw O cj Z₁ y y' ∈ O :=
    fun y y' => p.2.2.2 y y' _ _ (hl y).symm (hr y').symm
  have hL : ∀ y : Fin (r + 1) → O,
      lamC (Z₂.map O.subtype) (fun j => ((liftOf O p.1.1.toLinearMap y j : O) : E)) =
        lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
    intro y
    have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y _ (hl y).symm
    simpa [lamL_apply] using key
  have hS : ∀ y : Fin (r + 1) → O,
      lamStarC cj (Z₂.map O.subtype) (fun j => ((liftOf O p.1.2.toLinearMap y j : O) : E)) =
        lamStarC cj (Z₁.map O.subtype) (fun j => ((y j : O) : E)) :=
    fun y => p.2.2.1 y _ (hr y).symm
  rw [formC_eq O cj hcj Z₂ hu₂ hκ₂ _ _ hG₂, formC_eq O cj hcj Z₁ hu₁ hκ₁ _ _ hG₁]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL, hL, hS, hS]
  have key := O.add_mem (hb (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)))
    (hO _ (hb (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))))
  rw [map_sub] at key
  convert key using 1
  ring

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.GramMapSecondProjTranspose
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem corner_mul {K : Type} [Field K] {r : ℕ} (a d : K) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0) * X *
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) =
      Matrix.of fun i j => cor r i j (d * X (Fin.last r) (Fin.last r) * a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, cor]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
    simp [hi, hj, Finset.sum_ite_eq', Finset.sum_ite_eq, mul_assoc]

theorem det_corner_blocks_ne {K : Type} [Field K] {r : ℕ} (a d : K) (B C : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hB : B.det ≠ 0)
    (h : B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0) :
    (Matrix.fromBlocks (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then a else 0) B C
      (Matrix.of fun i j : Fin (r + 1) => if i = Fin.last r ∧ j = Fin.last r then d else 0)).det ≠ 0 := by
  set A : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then a else 0
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then d else 0
  set J : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K := Matrix.fromBlocks 0 1 1 0
  have hJ : Matrix.fromBlocks B A D C * J = Matrix.fromBlocks A B C D := by
    simp [J, Matrix.fromBlocks_multiply]
  have hJJ : J * J = 1 := by
    simp [J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hJd : J.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← hJ, Matrix.det_mul]
  refine mul_ne_zero ?_ hJd
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, corner_mul]
  have hsub : C - (Matrix.of fun i j => cor r i j (d * B⁻¹ (Fin.last r) (Fin.last r) * a)) =
      C + Matrix.of fun i j => cor r i j (-(d * B⁻¹ (Fin.last r) (Fin.last r) * a)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  have hinv : B⁻¹ (Fin.last r) (Fin.last r) = (B.submatrix Fin.castSucc Fin.castSucc).det / B.det := by
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last,
      Ring.inverse_eq_inv', smul_eq_mul]
    have h2 : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [Fin.val_last]; exact Even.neg_one_pow ⟨r, rfl⟩
    rw [h2, one_mul, div_eq_inv_mul]
  rw [hsub, det_add_cor, hinv]
  intro h0
  apply h
  have : B.det * (C.det + -(d * ((B.submatrix Fin.castSucc Fin.castSucc).det / B.det) * a) *
      (C.submatrix Fin.castSucc Fin.castSucc).det) = B.det * C.det - a * d * ((B.submatrix Fin.castSucc Fin.castSucc).det *
      (C.submatrix Fin.castSucc Fin.castSucc).det) := by
    field_simp
    ring
  rw [← this, h0]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem splitSecondProj_algebraMap (a : F) : ph2 g (algebraMap F E a) = a := by
  show (g.e (algebraMap F E a)).2 = a
  rw [AlgEquiv.commutes]
  rfl

theorem ph2_cj_eq_ph1 (x : E) : ph2 g (M.L.cj x) = ph1 g x := by
  show (g.e (M.L.cj x)).2 = (g.e x).1
  rw [g.e_cj]
  rfl

theorem gram_map_secondProj_transpose (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph2 g) =
      ((gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
        (algebraMap F E T')).map (ph1 g)).transpose := by
  have hcor : ∀ (φ : E →+* F) (a b : Fin (r + 1)) (c : E), φ (cor r a b c) = cor r a b (φ c) := by
    intro φ a b c
    unfold cor
    split_ifs <;> simp
  have hcorS : ∀ (a b : Fin (r + 1)) (c : F), cor r a b c = cor r b a c := by
    intro a b c
    unfold cor
    simp only [and_comm]
  have h1 : ∀ x, ph1 g (M.L.cj x) = ph2 g x := by
    intro x
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have ha1 : ∀ a : F, ph1 g (algebraMap F E a) = a := by
    intro a
    show (g.e (algebraMap F E a)).1 = a
    rw [AlgEquiv.commutes]
    rfl
  unfold gramG
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  congr 1
  · ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_neg, splitSecondProj_algebraMap, ha1]
    exact hcorS _ _ _
  all_goals
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hcor, map_mul, map_add (f := _), map_neg,
      map_sub, RingHom.coe_coe, splitSecondProj_algebraMap, ph2_cj_eq_ph1, h1, ha1]
    first | ring1 | (rw [hcorS]; done) | (rw [hcorS]; ring1)

theorem det_pM_ne (x : F) (hx : x ≠ 0) : (pM r x⁻¹).det ≠ 0 := by
  unfold pM
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (inv_ne_zero hx)

theorem gramUnit_split_holds : GramUnitG := by
  intro F _ _ _ E _ _ _ _ M g r T T' TT Zh Z Zσ h
  obtain ⟨-, -, -, -, -, hdet, hx⟩ := h
  have hq := q_ne g
  have h1 : ph1 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, map_gramG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (mul_ne_zero (det_pM_ne _ hq) ?_) (det_pM_ne _ hq)
    unfold gHat
    obtain ⟨-, hd2⟩ := (isUnit_iff_ph (g := g) _).1 hdet
    obtain ⟨hx1, -⟩ := (isUnit_iff_ph (g := g) _).1 hx
    refine det_corner_blocks_ne (-T) (-T') _ _ (by rwa [← det_ph]) ?_
    have hm : ((Zh.map (ph1 g)).transpose.submatrix Fin.castSucc Fin.castSucc).det =
        ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [det_ph]
      exact Matrix.det_transpose _
    rw [hm, Matrix.det_transpose]
    simp only [Matrix.submatrix_map, ← det_ph]
    convert hx1 using 1
    simp only [map_sub, map_mul, splitFirstProj_conj, splitFirstProj_algebraMap]
    ring
  have h2 : ph2 g (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det ≠ 0 := by
    rw [det_ph, gram_map_secondProj_transpose, Matrix.det_transpose, ← det_ph]
    exact h1
  exact (isUnit_iff_ph (g := g) _).2 ⟨h1, h2⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

