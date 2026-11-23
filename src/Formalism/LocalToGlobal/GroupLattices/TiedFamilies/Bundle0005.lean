module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem chi_mem_subfield {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t nb skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t nb skip fc zl) (K : Subfield ℂ) (hψ : ∀ i v h x, G.psi0 i v h x ∈ K)
    (hχ : ∀ i v h b, b < nb → ∀ x, G.chiB i v h b x ∈ K) (κ : S.U) : ((S.chi κ : ℂˣ) : ℂ) ∈ K := by
  rw [X.chi_eq κ]
  refine prod_mem fun i _ => ?_
  refine finprod_induction (fun z : ℂ => z ∈ K) (one_mem K) (fun _ _ hx hy => mul_mem hx hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => z ∈ K) (one_mem K) (fun _ _ hx hy => mul_mem hx hy) fun h => ?_
  refine inv_mem ?_
  unfold lamJ
  exact mul_mem (hψ i v h _) (prod_mem fun b hb => hχ i v h b (Finset.mem_range.1 hb) _)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem adExt_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    AdExt ((T u).cls0).lev (embT D) D.what₂.embLL (embFr T u) ((T u).cls0).y := by
  intro x
  have h1 : (D.fm u).emb 0 x ∈ (D.fm u).Fi 0 := ((((T u).val0).rat _).1 ⟨x, rfl⟩).1
  obtain ⟨fa, hfa, e⟩ := (((T u).val0).Fi _).1 h1
  exact ⟨fa, hfa.1, fun c => congrFun e c⟩

def LevelZeroCharacterRational (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Prop :=
  ∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = (T u).gl.psi0 i v h x

theorem chiRatAll_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (h : LevelZeroCharacterRational T u) :
    ChiRatAll ((T u).cls0).lev D.what₂.embLL := by
  intro κ
  exact RingHom.mem_fieldRange.1 (chi_mem_subfield ((T u).glev0) D.what₂.embLL.fieldRange
    (fun i v hv x => RingHom.mem_fieldRange.2 (h i v hv x)) (fun _ _ _ b hb => absurd hb (Nat.not_lt_zero b)) κ)

variable {X : Formalism.L2.Herm.Herm0 D}


set_option maxHeartbeats 4000000 in
theorem ex_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hO : PtOne ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B))
    (h1 : EvRatRep (embT D) D.what₂.embLL (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u))
    (h2 : LevelZeroCharacterRational T u) :
    ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
      (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y :=
  valEx_of_rep' (tEL D) (tEL_emb D) (embT_conj D) (locAt_std u w hg I.B I.B_std) (adExt_rec T u)
    (ptEx_rec X T u w hg I.B) hO h1 (chiRatAll_rec T u h2)

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix MvPolynomial
open scoped TensorProduct

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def genericBlockMatrix (v : Fin P.nV) (s : Fin (P.n' v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (XR P ℂ) :=
  Matrix.of fun a b => X (⟨v, (s, (a, b))⟩ : Var P)

def genDet : XR P ℂ := ∏ v, ∏ s : Fin (P.n' v), (genericBlockMatrix P v s).det

theorem eval_genDet (x : Var P → ℂ) :
    eval x (genDet P) = ∏ v, ∏ s : Fin (P.n' v), (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
      Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det := by
  unfold genDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [genericBlockMatrix]

theorem genDet_ne_zero : genDet P ≠ 0 := by
  intro h
  have h1 := eval_genDet P (fun x => if x.2.2.1 = x.2.2.2 then 1 else 0)
  rw [h, map_zero] at h1
  have h2 : ∀ (v : Fin P.nV) (s : Fin (P.n' v)),
      (Matrix.of fun a b => (fun x : Var P => if x.2.2.1 = x.2.2.2 then (1 : ℂ) else 0) ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det = 1 := by
    intro v s
    have : (Matrix.of fun a b => (fun x : Var P => if x.2.2.1 = x.2.2.2 then (1 : ℂ) else 0) ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) = 1 := by
      ext a b
      simp [Matrix.one_apply]
    rw [this, Matrix.det_one]
  simp only [h2, Finset.prod_const_one] at h1
  exact zero_ne_one h1

theorem eq_zero_of_blocks (Q : XR P ℂ)
    (h : ∀ z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ, (∀ v s, IsUnit (z v s).det) →
      eval (fun x : Var P => z x.1 x.2.1 x.2.2.1 x.2.2.2) Q = 0) : Q = 0 := by
  have h0 : Q * genDet P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_genDet]
    by_cases hx : ∀ v (s : Fin (P.n' v)), IsUnit (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det
    · have h1 := h (fun v s => Matrix.of fun a b => x ⟨v, (s, (a, b))⟩) hx
      have h2 : (fun y : Var P => (fun v (s : Fin (P.n' v)) => (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
          Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) y.1 y.2.1 y.2.2.1 y.2.2.2) = x := by
        funext y
        rfl
      rw [h2] at h1
      rw [h1, zero_mul]
    · push Not at hx
      obtain ⟨v, s, hvs⟩ := hx
      have h3 : (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det = 0 := by
        by_contra hne
        exact hvs (isUnit_iff_ne_zero.2 hne)
      have h4 : (∏ v, ∏ s : Fin (P.n' v), (Matrix.of fun a b => x ⟨v, (s, (a, b))⟩ :
          Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (Finset.prod_eq_zero (Finset.mem_univ s) h3)
      rw [h4, mul_zero]
  exact (mul_eq_zero.1 h0).resolve_right (genDet_ne_zero P)

variable {Tau : Type} [Fintype Tau] {n : ℕ}

def cRev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  ((z.submatrix id Fin.rev)ᵀ)⁻¹

theorem isUnit_det_rev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) :
    IsUnit ((z.submatrix id Fin.rev)ᵀ).det := by
  have h1 : (z.submatrix id Fin.rev).det = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (P.m + 1))) * z.det :=
    Matrix.det_permute' Fin.revPerm z
  rw [Matrix.det_transpose, h1]
  refine IsUnit.mul ?_ hz
  exact (Units.isUnit (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (P.m + 1))))).map (Int.castRingHom ℂ)

theorem cRev_spec (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) :
    ((cRev P z)⁻¹)ᵀ.submatrix id Fin.rev = z := by
  unfold cRev
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_rev P z hz), Matrix.transpose_transpose]
  ext a b
  simp

theorem isUnit_det_cRev (z : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : IsUnit z.det) : IsUnit (cRev P z).det := by
  unfold cRev
  rw [Matrix.det_nonsing_inv]
  exact (isUnit_det_rev P z hz).ringInverse

def blockPreimageMatrix (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (x : Σ v : Fin P.nV, Fin (P.n' v)) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ :=
  if Even x.2.val then z x.1 x.2 else cRev P (z x.1 x.2)

theorem isUnit_det_block_preimage (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)
    (hz : ∀ v s, IsUnit (z v s).det) (x : Σ v : Fin P.nV, Fin (P.n' v)) : IsUnit (blockPreimageMatrix P z x).det := by
  unfold blockPreimageMatrix
  split_ifs
  · exact hz _ _
  · exact isUnit_det_cRev P _ (hz _ _)

def frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) : Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (M τ)⁻¹ * (blockPreimageMatrix P z (pos.symm τ)).submatrix (finCongr h).symm (finCongr h).symm

theorem isUnit_det_frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : ∀ v s, IsUnit (z v s).det) (τ : Tau) :
    IsUnit (frameOf P h pos M z τ).det := by
  unfold frameOf
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  refine IsUnit.mul ?_ (isUnit_det_block_preimage P z hz _)
  rw [Matrix.det_nonsing_inv]
  exact (hM τ).ringInverse

theorem zAt_frameOf (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (z : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (hz : ∀ v s, IsUnit (z v s).det)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    zAt P h pos M (frameOf P h pos M z) v s = z v s := by
  have key : reM P h (M (pos ⟨v, s⟩) * frameOf P h pos M z (pos ⟨v, s⟩)) = blockPreimageMatrix P z ⟨v, s⟩ := by
    unfold frameOf
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hM _), Equiv.symm_apply_apply]
    ext a b
    simp [reM]
  unfold zAt
  rw [key]
  unfold blockPreimageMatrix
  by_cases hs : Even s.val
  · simp only [hs, if_true]
  · simp only [hs, if_false]
    exact cRev_spec P (z v s) (hz v s)

theorem evC_inj (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (Q : XR P ℂ) (hQ : evC P h pos G M Q = 0) : Q = 0 := by
  apply eq_zero_of_blocks P Q
  intro z hz
  have h1 := congrFun hQ (⟨frameOf P h pos M z, isUnit_det_frameOf P h pos M hM z hz⟩ : Frames G)
  have h2 : (∏ v, ∏ s : Fin (P.n' v), (zAt P h pos M (frameOf P h pos M z) v s).det ^ (eAt P v s)) *
      eval (fun x : Var P => zAt P h pos M (frameOf P h pos M z) x.1 x.2.1 x.2.2.1 x.2.2.2) Q = 0 := h1
  simp only [zAt_frameOf P h pos M hM z hz] at h2
  refine (mul_eq_zero.1 h2).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => zpow_ne_zero _ (hz v s).ne_zero

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Tau : Type} [Fintype Tau] {p : ℕ}

theorem isUnit_det_crdB (emb : Tau → E →+* ℂ) (B : GL (Fin n) E) (τ : Tau) : IsUnit (crdB emb B τ).det := by
  have h1 : (crdB emb B τ).det = emb τ ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (RingHom.map_det (emb τ) _).symm
  rw [h1]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (B⁻¹ : GL (Fin n) E))).map (emb τ)

theorem evInj_pf (emb : Tau → E →+* ℂ) (G : GAtP p) (A : LocAt F E n G)
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau) : EvInj emb G A pos (J := J) :=
  fun Q hQ => evC_inj G.P A.rk pos (gramC J emb) (crdB emb A.B) (isUnit_det_crdB emb A.B) Q hQ

end Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evInj_rec {D : D7} {X : Formalism.L2.Herm.Herm0 D} (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    EvInj (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg) (J := gramN D 0 (Nat.zero_le _)) :=
  evInj_pf (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg)

end Formalism.L2.G
end
end

