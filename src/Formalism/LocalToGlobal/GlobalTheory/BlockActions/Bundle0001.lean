module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FixOrthogonalVector
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.HermitianForms.TiedBrUnit
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExtendOneMulVecSingleLast

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrExistsOfRestS
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

structure PendClausesS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
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

def pendOfS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) : Pend D u where
  br τ := Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
  coM := coMTS Tf B
  coP := coPTS Tf B
  coM_mem := h.coM_mem
  coM_inj := h.coM_inj
  coP_mem := h.coP_mem
  coP_inj := h.coP_inj
  Pt_eq := by
    intro w φ hφ c
    obtain ⟨P, hP, hv, hz⟩ := h.exP w φ hφ c
    exact hz _ (hL.map.pt_eq (bZ_isUnitS Tf) φ c P hP hv)
  lat_co := h.lat_co
  pt_co := h.pt_co
  gP := gP
  ipV_co := h.ipV_co
  re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord
  beOn_eq := hL.beOn
  interlace := sg_interlace Tf.valP

theorem brExists_of_tiedS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  ⟨pendOfS Tf hL B gP h, archimedeanSignatureMatching_of_trivial_branching_symm Tf _ fun _ => rfl⟩

section Cl

theorem bZg_isUnitS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (bZg u Tf.til.z0 B').det := by
  have hBi : Function.Injective B'.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB')
  refine isUnit_det_cols (Nm_succ D.R) (iXm D * B') (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) ?_ ?_
  · intro x y h
    simp only [← Matrix.mulVec_mulVec] at h
    exact hBi (iXm_mulVec_injective D h)
  · intro x h
    apply quotient_not_in_range_symmetric Tf (B' *ᵥ x)
    rw [Matrix.mulVec_mulVec]; exact h

theorem trEv_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), trEvS Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (atInf (Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 B')⁻¹) Q := by
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hU := atInf_inv_isUnit _ (bZg_isUnitS Tf B' hB')
  rw [hM]
  exact exists_change _ _ _ _ _ hU P hP

theorem eW_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan (D.fm u).sg, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (atInf (Formalism.L2.Forms.embT D) B'⁻¹) Q := by
  have hF := (Tf.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (Tf.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hU := atInf_inv_isUnit _ hB'
  rw [he]
  exact exists_change _ _ _ _ _ hU Q0 hQ0'

variable (Tf : FormsTiedSym D u Ch chOf)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB

theorem coM_mem_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  intro w c φ hφ
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    show fnInv _ _ _ (trEvS Tf c (φ ((D.fm u).til c))) = Q
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  rw [this]; exact hQ

theorem coP_mem_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  intro w z hz c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    show fnInv _ _ _ (Tf.valP.eW z c) = Q
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  rw [this]; exact hQ

theorem coP_inj_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0 := by
  intro w z hz h0
  apply Tf.valP.eW.injective
  rw [map_zero]
  funext c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    show fnInv _ _ _ (Tf.valP.eW z c) = Q
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  have hQ0 : Q = 0 := by rw [← this, h0]; rfl
  rw [hq, hQ0, map_zero]; rfl

theorem coM_inj_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0 := by
  intro w c φ hφ h0
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have hc : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    show fnInv _ _ _ (trEvS Tf c (φ ((D.fm u).til c))) = Q
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  have ht : trEvS Tf c (φ ((D.fm u).til c)) = 0 := by rw [hq, ← hc, h0, map_zero]
  funext s'
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun ht (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (Formalism.L2.Forms.embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (Formalism.L2.Forms.embT D) ga))
  simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hy
  have hback : (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (Formalism.L2.Forms.embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (Formalism.L2.Forms.embT D) ga)).tr
      (atInf (Formalism.L2.Forms.embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E)) (isUnit_det_atInf (Formalism.L2.Forms.embT D) ga⁻¹) =
      (Tf.val D.R.m le_rfl (Or.inr rfl)).eY s' := by
    apply Subtype.ext
    funext τ
    show atInf (Formalism.L2.Forms.embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (Formalism.L2.Forms.embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ) = ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ
    have h1 := atInf_mul_inv (Formalism.L2.Forms.embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hback, Equiv.symm_apply_apply] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)


omit hB in
structure PendRestS (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
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

theorem brExists_of_restS (hL : LowerSymmetricCompatible Tf)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendRestS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_tiedS Tf hL B gP
    { coM_mem := coM_mem_ofS Tf B hB, coM_inj := coM_inj_ofS Tf B hB, coP_mem := coP_mem_of_isUnit_det' Tf B hB,
      coP_inj := coP_inj_of_isUnit_det' Tf B hB, exP := h.exP, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
      re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

end Cl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.MulLatMulLat
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

structure CrdFacts (D : D7) : Prop where
  conj : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ ((sigD D : D.host.E →+* D.host.E) x) = (starRingEnd ℂ) (φ x)
  defN : ∀ (φ : D.host.E →+* ℂ) (x : Fin (D.R.N D.R.m) → D.host.E), ∃ r : ℝ, 0 ≤ r ∧
    φ (hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x x) = r ∧ (r = 0 → x = 0)
  iso : ∀ x x', hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D x') =
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) x x'
  orth : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 ∧
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0
  span : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • zc D

section Unit

variable {E : Type} [Field E] {n : ℕ}

theorem hform_eq_dot (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform σ J x y = dotProduct (fun i => σ (x i)) (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem hform_UJ (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E) (hg : cT σ g * J * g = J)
    (x y : Fin n → E) : hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have h1 : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  have key : ∀ (A : Matrix (Fin n) (Fin n) E) (v w : Fin n → E), (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
    intro A v w; rw [dotProduct_mulVec, vecMul_transpose]
  rw [hform_eq_dot, hform_eq_dot, h1, key, mulVec_mulVec, mulVec_mulVec]
  congr 2

end Unit

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem ga_herm (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (x y : Fin (D.R.N D.R.m) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) ((Tf.til.ga c).1.1 *ᵥ x) ((Tf.til.ga c).1.1 *ᵥ y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) x y :=
  hform_UJ _ _ _ (Tf.til.ga c).2 x y

section Glue

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem mulLat_mulLat {E : Type} [Field E] [NumberField E] {n : ℕ} (A B : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : mulLat A (mulLat B L) = mulLat (A * B) L := by
  unfold mulLat
  rw [← Submodule.map_comp]
  congr 1
  ext x i
  simp

theorem fv_pr_congr (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) (a b : (D.mem u).C.cls D.R.m) (hab : a = b)
    (x : Fin (D.R.N D.R.m) → D.host.E) (hxa : x ∈ Ld D u D.R.m le_rfl a) (hxb : x ∈ Ld D u D.R.m le_rfl b) :
    (D.fm u).fv D.R.m v a ((Tf.lv D.R.m le_rfl).pr v a ⟨x, hxa⟩) =
      (D.fm u).fv D.R.m v b ((Tf.lv D.R.m le_rfl).pr v b ⟨x, hxb⟩) := by
  subst hab; rfl

theorem T_mem_Pv (Tf : FormsTiedSym D u Ch chOf) (v : (D.mem u).A.vT) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ Tf.atT.Pv v := by
  let pb : 𝓞 D.host.E := ⟨D.host.conj (Tf.atT.piU : D.host.E), (Tf.atT.piU.2).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = Tf.atT.piU * pb := by
    apply RingOfIntegers.ext
    have e1 : ((Tf.atT.piU * pb : 𝓞 D.host.E) : D.host.E) = (Tf.atT.piU : D.host.E) * (pb : D.host.E) := rfl
    have e2 : ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by simp
    rw [e1, e2, ← Tf.atT.piU_norm]; rfl
  rw [hT]
  show Tf.atT.res v (Tf.atT.piU * pb) = 0
  rw [map_mul, Tf.atT.res_pi, zero_mul]

theorem til_eq_fix (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set g1 := (Tf.til.ga c).1.1 with hg1
  set g2 := (Tf.til.ga c').1.1 with hg2
  set gi := ((Tf.til.ga c)⁻¹).1.1 with hgi
  have hgi1 : gi * g1 = 1 := by simp [hgi, hg1]
  have hg1i : g1 * gi = 1 := by simp [hgi, hg1]
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have ha0 : a ≠ 0 := by
    intro h0
    have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ gi * J * gi = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J ((g2 * gi) *ᵥ x) ((g2 * gi) *ᵥ y) = hform σ J x y := fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J gi hUgi]
  have hlat : mulLat (g2 * gi) ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}) =
      (Tf.clsP.lat c').map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
    rw [← Tf.til.til_lat c, ← Tf.til.til_lat c', mulLat_mulLat, Matrix.mul_assoc, hgi1, Matrix.mul_one, h]
  have hres : ∀ y : Fin (D.R.N D.R.m) → D.host.E,
      (∀ w ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) →
      ∀ r r' : 𝓞 D.host.E, (r : D.host.E) = hform σ J z0 y → (r' : D.host.E) = hform σ J z0 ((g2 * gi) *ᵥ y) →
        r - r' ∈ Tf.atT.Pv v := by
    intro y hy r r' hr hr'
    have hxy : g1 *ᵥ (gi *ᵥ y) = y := by rw [mulVec_mulVec, hg1i, one_mulVec]
    have hxa : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c) := by
      apply Submodule.subset_span
      intro l hl
      have hl' : g1 *ᵥ l ∈ (Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} := by
        rw [← Tf.til.til_lat c]; exact Submodule.mem_map.2 ⟨l, hl, rfl⟩
      have := hy _ hl'
      rw [← hxy, ga_herm Tf c] at this
      exact this
    have hxb : gi *ᵥ y ∈ Ld D u D.R.m le_rfl ((D.fm u).til c') := h ▸ hxa
    have e1 := Tf.til.til_fv v c ⟨gi *ᵥ y, hxa⟩ r (by rw [hr]; show _ = hform σ J z0 (g1 *ᵥ (gi *ᵥ y)); rw [hxy])
    have e2 := Tf.til.til_fv v c' ⟨gi *ᵥ y, hxb⟩ r' (by rw [hr', ← mulVec_mulVec])
    rw [fv_pr_congr Tf v _ _ h _ hxa hxb, e2] at e1
    show Tf.atT.res v (r - r') = 0
    rw [map_sub, e1, sub_self]
  exact fix_orthogonal_vector σ hC.conj J (gramP D) hC.defN (iXc D) z0 hC.iso horth hspan _ hTp hdeg hzz
    (Tf.clsP.lat c) (Tf.clsP.lat c')
    ⟨fun y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := fun x hx => hy x hx
      rw [hSD c'] at this; exact this,
     fun x hx y hy => by
      have : y ∈ dualSet σ (gramP D) (Tf.clsP.lat c') := by rw [hSD c']; exact hy
      exact this x hx⟩
    (g2 * gi) hγ hlat (Tf.atT.Pv v) inferInstance (T_mem_Pv Tf v) hres

theorem til_eq_ext (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  have hfix := til_eq_fix Tf hC hSD hdeg v c c' h
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  set γ := (Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1 with hγdef
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz' := hzz
    rw [ha, h0, zero_smul] at hzz'
    apply hT0; rw [← hzz']; simp [hform]
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hspan : ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • z0 := fun y => by
    obtain ⟨x, s, hy⟩ := hC.span y
    exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩
  have hUgi : cT σ ((Tf.til.ga c)⁻¹).1.1 * J * ((Tf.til.ga c)⁻¹).1.1 = J := ((Tf.til.ga c)⁻¹).2
  have hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y := fun x y => by
    rw [hγdef, ← mulVec_mulVec, ← mulVec_mulVec, ga_herm Tf c', hform_UJ σ J _ hUgi]
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth hspan
    (by rw [hzz]; exact hT0) γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem til_ext (Tf : FormsTiedSym D u Ch chOf) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R) :
    ∃ g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R, IsExt D Tf.til.z0 φ g' g ∧ (IsUnit g'.det → IsUnit g.det) := by
  obtain ⟨G, h1, h2, h3⟩ := ext_general φ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D)
    (fun a => Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) (by exact bZ_isUnitS Tf) g'
  refine ⟨G, ⟨h1, ?_⟩, h3⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hz : (fun a => φ (Tf.til.z0 a)) = φ ((D.mem u).A.T : D.host.E) • (fun a => φ (Tf.til.z0 a / ((D.mem u).A.T : D.host.E))) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, mul_div_cancel₀ _ hT]
  rw [hz, mulVec_smul, h2]

end Glue

end Formalism.L2.GlobalTheoryTheory.Br
end
end

