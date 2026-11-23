module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.RestrictionSymmetric
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blkRowS (Tf : FormsTiedSym D u Ch chOf) (G : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blkRow (fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
              Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose) P) =
      blkRow (fun τ => (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) (Formalism.L2.Ker.brTen D u P) := by
  have hS : ∀ τ, Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    fun τ => Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  rw [blkRow_eq_blk, blkRow_eq_blk]
  unfold Formalism.L2.Ker.brTen
  rw [Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m) ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose).toLinearMap)) =
      fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m - 1) (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose).toLinearMap ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) := by
    funext τ f
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact brOne_rowAct (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (hS τ) (G τ) f
  rw [e]

theorem shift_lamT_sgTS (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    shiftOf (lamT u D.R.m) τ = shiftOf (sgT u) τ := by
  have hS : Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  have hS' : (sgTr D u τ).detShift = (lamTr D u τ).detShift := hS
  unfold lamTr sgTr at hS'
  rw [detShift_wSh _ _ h1, detShift_wSh _ _ h2] at hS'
  simp only [shiftOf, lamT, sgT]
  rw [detShift_shW _ _ h1, detShift_shW _ _ h2]
  unfold cTw at hS'
  omega

theorem exP_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) :
    ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c))) := by
  intro w φ hφ c
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  refine ⟨P, hP, hv, fun z hz => ?_⟩
  have hBc := hB w c
  have hU1 := atInf_inv_isUnit _ hBc
  have hbZ := bZ_isUnitS Tf
  have hbZg := bZg_isUnitS Tf (B w c) hBc
  have hU2 := atInf_inv_isUnit _ hbZg

  have hL : coPTS Tf B w z c = (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹).det ^ shiftOf (sgT u) τ) •
      blkRow (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
        (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹) (Formalism.L2.Ker.brTen D u P) := by
    have e1 : coPTS Tf B w z c = fnInv (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹) (Tf.valP.eW z c) := by
      simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
    rw [e1, hz, fnOf_change _ _ (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹) 1 hU1, fnInv_fnOf _ _ _ hU1]

  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hR : coMTS Tf B w c (φ ((D.fm u).til c)) = (∏ τ, (atInf (Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ *
      (atInf (Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => atInf (Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) P := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hM, mZ, fnOf_change _ _ (atInf (Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (atInf (Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹) hU2,
      fnInv_fnOf _ _ _ hU2]
  have hKm : (fun τ => atInf (Formalism.L2.Forms.embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) =
      fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (B w c) hBc τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [embGL_glT, atInf_inv_inv _ hbZg, bZg_eq_mul]
    show (bZ u Tf.til.z0)⁻¹.map (Formalism.L2.Forms.embT D τ) * (bZ u Tf.til.z0 * dgE (B w c)).map (Formalism.L2.Forms.embT D τ) = _
    rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
  have hKp : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹ τ)⁻¹) = fun τ => ((glT (B w c) hBc τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [glT_val, Matrix.transpose_transpose, Pi.one_apply, Matrix.one_mul, atInf_inv_inv _ hBc]
    rfl
  rw [hL, hR, hKm, hKp, map_smul, brTen_blkRowS Tf]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrFun hKm τ
  have h2 := congrFun hKp τ
  rw [h1, h2, shift_lamT_sgTS Tf τ, embGL_glT, glT_val, Matrix.det_transpose]
  unfold dgE
  rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]

structure RestrictionSymmetric (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem pendRest_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    PendRestS Tf B gP :=
  ⟨exP_ofS Tf B hB, h.lat_co, h.pt_co, h.ipV_co, h.re_petersson_self_eq_sum_coord⟩

theorem brExists_of_rest4S (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_restS Tf B hB hL gP (pendRest_ofS Tf B hB gP h)

theorem weightedInner_self_eq_sum_coords_of_orthonormal' (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : o.IsON) :
    ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))
        (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))).re := by
  classical
  intro w z hz
  have hQ : ∀ c, blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c) ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    intro c
    have h0 := coP_mem_of_isUnit_det' Tf B hB w z hz c
    rw [← cspan_sgTr] at h0
    have h1 := Formalism.L2.Ker.lc_blk_sqAct_mem _ (gPof B hB o w c) _ h0
    rw [cspan_sgTr] at h1
    exact h1
  have hE : ∀ c, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹)
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c)) := by
    intro c
    obtain ⟨Q, _, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
    have hc : coPTS Tf B w z c = Q := by
      simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
      rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
    have hs : shiftOf (sgT u) = fun τ => (sgTr D u τ).detShift := funext fun τ => (shift_sgTr τ).symm
    rw [hc, hq, hs, fnOf_sqAct _ (sgTr D u) (atInf (Formalism.L2.Forms.embT D) (B w c)⁻¹) o.1 o.2 _ (fun τ => rfl)]
  rw [Tf.valP.ipP o ho z z _ _ hQ hQ hE hE, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ = (((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.TilEqLevel
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7}

section IsExtAlg

variable {z0 : Fin (D.R.N D.R.m) → D.host.E} {R : Type} [CommRing R] {φ : D.host.E →+* R}

theorem isExt_mul {a b : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A B : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hb : IsExt D z0 φ b B) : IsExt D z0 φ (a * b) (A * B) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc]
  · rw [← mulVec_mulVec, hb2, ha2]

theorem isExt_inv {a a' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A A' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hA : A' * A = 1) (ha' : a * a' = 1) : IsExt D z0 φ a' A' := by
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨?_, ?_⟩
  · calc A' * (iXm D).map φ = A' * ((iXm D).map φ * (a * a')) := by rw [ha', Matrix.mul_one]
      _ = (A' * A) * (iXm D).map φ * a' := by rw [← Matrix.mul_assoc ((iXm D).map φ), ← ha1]; simp only [Matrix.mul_assoc]
      _ = (iXm D).map φ * a' := by rw [hA, Matrix.one_mul]
  · conv_lhs => rw [← ha2]
    rw [mulVec_mulVec, hA, one_mulVec]

theorem isExt_map {a : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E} {A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (ha : IsExt D z0 (RingHom.id D.host.E) a A) : IsExt D z0 φ (a.map φ) (A.map φ) := by
  obtain ⟨ha1, ha2⟩ := ha
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  rw [hm] at ha1
  refine ⟨?_, ?_⟩
  · rw [← Matrix.map_mul, ha1, Matrix.map_mul]
  · have hz : (fun i => (RingHom.id D.host.E) (z0 i)) = z0 := rfl
    rw [hz] at ha2
    funext i
    have := congrArg (fun w => φ (w i)) ha2
    rw [← this, RingHom.map_mulVec]; rfl

end IsExtAlg

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


set_option maxHeartbeats 2000000 in
theorem til_eq_level (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
      (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y) ∧
      IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1 ∧
      G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U ∧
      (Tf.clsP.y c').1.1 * k = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
  set incl : D.host.E →+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F :=
    inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hincl
  obtain ⟨δ, hδE, hδi⟩ := til_eq_ext Tf hC hSD hdeg v c c' h
  have hdet : ∀ d : (D.fm u).clsP, IsUnit ((Tf.clsP.y d).1.1).det := fun d =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y d).1.isUnit
  have ext_of : ∀ d : (D.fm u).clsP, ∃ Gd : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsExt D Tf.til.z0 incl (Tf.clsP.y d).1.1 Gd.1 := by
    intro d
    obtain ⟨g, hg, hu⟩ := til_ext Tf incl (Tf.clsP.y d).1.1
    exact ⟨((Matrix.isUnit_iff_isUnit_det g).mpr (hu (hdet d))).unit, hg⟩
  obtain ⟨Gc, hGc⟩ := ext_of c
  obtain ⟨Gc', hGc'⟩ := ext_of c'
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have e2 := Tf.tilAd.til_ad c' Gc' hGc'
  rw [← h] at e2
  have hGc1 : Gc = bc incl (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hGc2 : Gc' = bc incl (Tf.til.ga c').1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c').1)⁻¹ := eq_mul_inv_of_mul_eq e2.symm
  set Γ := bc incl (Tf.til.ga c').1 * (bc incl (Tf.til.ga c).1)⁻¹ with hΓ
  refine ⟨δ, ((Tf.clsP.y c').1.1)⁻¹ * δ.map incl * (Tf.clsP.y c).1.1, Gc'⁻¹ * Γ * Gc, hδE, hδi, ?_, ?_, ?_⟩
  · have hinv : IsExt D Tf.til.z0 incl ((Tf.clsP.y c').1.1)⁻¹ (Gc'⁻¹).1 :=
      isExt_inv hGc' (Units.inv_mul Gc') (Matrix.mul_nonsing_inv _ (hdet c'))
    have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
        ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).map incl := by
      rw [hΓ, Units.val_mul, Matrix.map_mul]
      congr 1
    have hG : IsExt D Tf.til.z0 incl (δ.map incl) Γ.1 := by rw [hΓ1]; exact isExt_map hδE
    rw [Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hG) hGc
  · have : Gc'⁻¹ * Γ * Gc = (Tf.tilAd.ka c').1 * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hGc1, hGc2, hΓ]; group
    rw [this]
    exact Subgroup.mul_mem _ (Tf.tilAd.ka c').2 (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet c'), Matrix.one_mul]

end Formalism.L2.GlobalTheoryTheory.Br
end
end

