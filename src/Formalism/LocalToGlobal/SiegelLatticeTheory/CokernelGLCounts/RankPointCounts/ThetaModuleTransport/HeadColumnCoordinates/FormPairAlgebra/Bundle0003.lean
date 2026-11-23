module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.LamSZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BwdExists
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

private theorem exists_cj_combination_of_isUnit_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (y' : Fin (r + 1) → O) :
    ∃ w : Fin (r + 1) → E, ∀ b, (y' b : E) = ∑ a, cj (Z.map O.subtype a b) * w a := by
  set N : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (Z.map O.subtype).transpose.map cj with hN
  have hdet : IsUnit N.det := by
    have h1 : N.det = cj (Z.map O.subtype).det := by
      rw [hN, ← Matrix.det_transpose (Z.map O.subtype)]
      exact (RingHom.map_det cj _).symm
    rw [h1]
    exact hu.map cj
  refine ⟨N⁻¹.mulVec (fun j => (y' j : E)), fun b => ?_⟩
  have h2 : N.mulVec (N⁻¹.mulVec (fun j => (y' j : E))) = fun j => (y' j : E) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have h3 := congrFun h2 b
  rw [← h3]
  simp [Matrix.mulVec, dotProduct, hN]

theorem pair_eG (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁) (p : PairSet O cj hO Z₁ Z₂) :
    p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  have hlam : lamS O cj Z₂ y₂' = lamS O cj Z₁ (Pi.single (Fin.last r) 1) :=
    p.2.2.1 (Pi.single (Fin.last r) 1) y₂' hy₂'.symm
  set d : Fin (r + 1) → O := y₂' - Pi.single (Fin.last r) 1 with hd
  obtain ⟨w, hw⟩ := exists_cj_combination_of_isUnit_det O cj Z₂ hu₂ d
  have hlast : w (Fin.last r) = 0 := by
    rw [← lamS_cjT O cj Z₂ hu₂ d w hw, hd, lamS_sub, hlam, lamS_e', lamS_e', hκ, sub_self]
  have hmem : ∀ a, w a ∈ O := by
    intro a
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1.symm (Submodule.Quotient.mk (Pi.single a 1)))
    have h1 : p.1.1 (Submodule.Quotient.mk c) = Submodule.Quotient.mk (Pi.single a 1) := by
      rw [hc]
      simp
    have hB := p.2.2.2 c (Pi.single (Fin.last r) 1) (Pi.single a 1) y₂' h1 hy₂'.symm
    have hL := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 c (Pi.single a 1) h1
    have hsplit : y₂' = d + Pi.single (Fin.last r) 1 := by
      rw [hd]
      abel
    rw [hsplit, bRaw_add_right, bRaw_e, bRaw_e, hL, add_sub_cancel_right,
      bRaw_cjT O cj hcj Z₂ hu₂ _ d w hw] at hB
    have hs : (∑ b : Fin (r + 1), cj (w b) * ((Pi.single a (1 : O) : Fin (r + 1) → O) b : E)) = cj (w a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [hs] at hB
    have := hO _ hB
    rwa [hcj] at this
  have hdmem : d ∈ headCols (cjT O cj hO Z₂) := by
    rw [mem_headCols_iff]
    refine ⟨fun a => ⟨w a, hmem a⟩, Subtype.ext hlast, ?_⟩
    funext b
    apply Subtype.ext
    rw [cjT_mulVec_coe]
    exact hw b
  rw [← hy₂']
  exact (Submodule.Quotient.eq _).2 hdmem

section Bwd

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
  (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
  (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
  (hκ : kap O Z₂ = kap O Z₁)
  (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
  (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)


include hcj hu₁ hu₂ hκ hG₁ hG₂ in
theorem form_diff (p : PairSet O cj hO Z₁ Z₂) (Y Y₂ W W₂ : Ix r → O)
    (hy : p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j))
    (hy' : p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j))
    (hw : p.1.1 (Submodule.Quotient.mk fun j => W (Sum.inl j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inl j))
    (hw' : p.1.2 (Submodule.Quotient.mk fun j => W (Sum.inr j)) = Submodule.Quotient.mk fun j => W₂ (Sum.inr j)) :
    formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W ∈ O := by
  have hl : lamC (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Y (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hy
  have hs : lamStarC cj (Z₂.map O.subtype) (fun j => ((Y₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Y (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hy'
  have hlw : lamC (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inl j) : O) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((W (Sum.inl j) : O) : E)) :=
    lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 _ _ hw
  have hsw : lamStarC cj (Z₂.map O.subtype) (fun j => ((W₂ (Sum.inr j) : O) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((W (Sum.inr j) : O) : E)) :=
    p.2.2.1 _ _ hw'
  obtain ⟨hc1, hc2⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ _ _ hG₁ hG₂ hκ Y Y₂ hl hs
  have hb1 := p.2.2.2 _ _ _ _ hy hw'
  have hb2 := p.2.2.2 _ _ _ _ hw hy'
  rw [formC_eqG O cj hcj Z₂ hu₂ _ _ hG₂, formC_eqG O cj hcj Z₁ hu₁ _ _ hG₁, hc1, hc2, hlw, hsw]
  have key : ∀ a b c d X X' : E,
      (a + cj b + X + X') - (c + cj d + X + X') = (a - c) + cj (b - d) := by
    intro a b c d X X'
    rw [map_sub]
    ring
  rw [key]
  exact add_mem hb1 (hO _ hb2)

end Bwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ElimSplit
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

section Props

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

theorem elim_split (Y : Ix r → O) :
    (Submodule.Quotient.mk Y : DDc O cj (Z₂.map O.subtype) t t') =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) := by
  have e1 : iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) =
      (Submodule.Quotient.mk (elimL O (fun a => Y (Sum.inl a))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  have e2 : iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) =
      (Submodule.Quotient.mk (elimR O (fun b => Y (Sum.inr b))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  rw [e1, e2, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  rcases i with i | i <;> simp [elimL, elimR]

theorem gs_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  have sp := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  have hp : ((Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) (Pi.single (Fin.last r) 1)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((0 : E), (1 : E))) ∈ GamC' O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim 0 (Pi.single (Fin.last r) 1), fun b => Pi.single_eq_of_ne (Fin.castSucc_ne_last b) _,
      by simp [lamC, Matrix.mulVec, dotProduct]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd' O cj t t' Z₁ Z₂ θ hΓ' _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hr : (fun b => Y₂ (Sum.inr b)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h3.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set gs := gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (gs (eCl (cjT O cj hO Z₁)))
  have key : iR O cj hO Z₂ t t' (gs (eCl (cjT O cj hO Z₁))) =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y₂ (Sum.inl a))) +
        iR O cj hO Z₂ t t' (eCl (cjT O cj hO Z₂)) := by
    rw [← sp.1, eCl, iR_mk]
    show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hr]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (fun a => Y₂ (Sum.inl a)) (Pi.single (Fin.last r) 1 - v)) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, map_sub, ← eCl, hv, key]
    abel
  have hl : lamL O Z₂ (fun a => Y₂ (Sum.inl a)) = 0 := by rw [lamL_apply]; exact h2.symm
  have hl' : lamS O cj Z₂ (Pi.single (Fin.last r) 1 - v) = 0 := by
    have e1 := sp.2
    rw [← hv, lamSQ_mk, eCl, lamSQ_mk, lamS_e'] at e1
    rw [lamS_sub, lamS_e', e1, hκ, sub_self]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').2
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, ← this]
  rfl

theorem g_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁) = eCl Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁)
  have hp : ((Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) (0 : Fin (r + 1) → O)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((1 : E), (0 : E))) ∈ GamC O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim (Pi.single (Fin.last r) 1) 0, fun a => Pi.single_eq_of_ne (Fin.castSucc_ne_last a) _,
      by simp [lamStarC]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd O cj t t' Z₁ Z₂ θ hΓ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hl0 : (fun a => Y₂ (Sum.inl a)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h2.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set g := gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ'
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (g (eCl Z₁))
  have key : iL O cj hO Z₂ t t' (g (eCl Z₁)) =
      iL O cj hO Z₂ t t' (eCl Z₂) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y₂ (Sum.inr b))) := by
    rw [← sp.1, eCl, iL_mk]
    show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hl0]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (v - Pi.single (Fin.last r) 1) (-(fun b => Y₂ (Sum.inr b)))) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, Submodule.Quotient.mk_neg, map_sub, map_neg, ← eCl,
      hv, key]
    abel
  have hl : lamL O Z₂ (v - Pi.single (Fin.last r) 1) = 0 := by
    have e1 := sp.2
    rw [← hv, lamLQ_mk, eCl, lamLQ_mk, lamL_e'] at e1
    rw [map_sub, lamL_e', e1, hκ, sub_self]
  have hl' : lamS O cj Z₂ (-(fun b => Y₂ (Sum.inr b))) = 0 := by
    have : lamS O cj Z₂ (fun b => Y₂ (Sum.inr b)) = 0 := h3.symm
    rw [show (-(fun b => Y₂ (Sum.inr b)) : Fin (r + 1) → O) = 0 - (fun b => Y₂ (Sum.inr b)) by rw [zero_sub],
      lamS_sub, lamS_zero, this, sub_zero]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').1
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, this]
  rfl

theorem g_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁) = bCls Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁)
  have sps := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  apply uniqL O cj hO Z₂ hu₂ t t' hη₂
  · rw [← sp.1, rel_b, map_smul, map_smul, sps.1, gs_e O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hκ hΓ hΓ', rel_b,
      map_smul]
  · rw [sp.2, bCls, bCls, lamLQ_mk, lamLQ_mk, lamL_b O Z₁ hu₁, lamL_b O Z₂ hu₂]

end Props

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
end
end

