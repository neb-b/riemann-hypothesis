module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZOrb

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Typed

variable (p : PlF D) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq

theorem zz1' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
        (Z * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm1 : ∀ k : ℕ, p1 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, fst_proj_symm,
    apply_ite (p1 sg.e), map_zero, Prod.fst_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj1, hf1, hf2, hm1, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem zz2' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        ((Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm2 : ∀ k : ℕ, p2 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, snd_proj_symm,
    apply_ite (p2 sg.e), map_zero, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj2, hf1, hf2, hm2, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one,
    Matrix.transpose_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem mm1' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) *
        Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x := fun s x => by
    simp only [twist, hR]; rw [fst_proj_symm]; rfl
  have hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply]
  by_cases hb : b = sgF w a
  · subst hb
    simp only [if_true, modMat_blk, map_sub, map_mul, fst_proj_algebraMap, htw1, hqi, apply_ite (p1 sg.e), hta1, map_zero,
      hφ1, RingHom.comp_apply]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem mm2' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
        (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then (T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x := fun s x => by
    simp only [twist, hR]; rw [snd_proj_symm]; rfl
  have hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply, Sg]
  by_cases hb : b = sgF w a
  · subst hb
    have hsr := sign_rel (R := (D.s.atP p).Fp) _ _ _ (nu_parity w a)
    simp only [if_true, modMat_blk, map_sub, map_mul, snd_proj_algebraMap, htw2, hqi, apply_ite (p2 sg.e), hta2, map_zero,
      hφ2, RingHom.comp_apply, hsr]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem zzpSgn_orb_typed (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z L B : PairVal.MatR D}
    (hL : IsLo L) (hB : IsUp B) (hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * B) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hA' : Z = L * ptMat w * B * Sg D.host.E D.R.rS := by
    rw [← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_map ((p1 sg.e).comp (D.s.atP p).ιE) hL) (isUp_map ((p1 sg.e).comp (D.s.atP p).ιE) hB)
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hL)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsUp (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (L := Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (B := Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
      Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  have e2 : (Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
    rw [hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
    exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
  refine goal_of (isLo_glue sg.e hL1 hL2) (isUp_glue sg.e hU1 hU2) (mat_eq sg.e ?_ ?_)
  · rw [zz1' Zd p sg hR g hM hge hgq, hf']
    conv_lhs => rw [Matrix.map_mul, Matrix.map_mul]
    rw [h1]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst]
    rw [mm1' Zd p sg hR g hM hge hgq]
  · rw [zz2' Zd p sg hR g hM hge hgq, e2, h2]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd]
    rw [mm2' Zd p sg hR g hM hge hgq]

end Typed

theorem zzpSgn_orb (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z)
    (p : PlF D) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  obtain ⟨L, U, hL, hU, e⟩ := hZ
  have hL' := isLo_of_uni hL
  have hU' := isUp_of_uni hU
  have hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set ι := (D.s.atP p).ιE
    set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
    have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
        modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w := by
      ext a b
      rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
      by_cases hb : b = sgF w a
      · rw [if_pos hb, if_pos hb, modMat_blk Zd]
        simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
        subst hb
        ring
      · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
    rw [zzp_sgn_ord Zd u u' p hM Z, hf', Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, hmod]
    exact goal_of (isLo_conj (isLo_map ι hL') fr fri hfr') (isUp_conj (isUp_map ι hU') fri fr hfr) rfl
  · exact zzpSgn_orb_typed Zd p sg hR g hM hAg.1 hAg.2 u u' hL' hU' hf'

end ZOrb

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.PCount

namespace IntegralGeneration

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_smul_right (x y : V) (c : E) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem fst_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).1 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).1 := by
    have := hx.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem snd_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).2 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).2 := by
    have := hx.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem mem_R_of_split {g : Loc.SplitG M.L} (hM : M.split = some g) (x : E) :
    x ∈ M.R ↔ g.e x ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[F]) (g.q : F) := by
  obtain ⟨L, s, mu⟩ := M
  simp only at hM g ⊢
  subst hM
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x

theorem e_alg (g : Loc.SplitG M.L) (c : F) : g.e (algebraMap F E c) = (c, c) := by
  rw [g.e.commutes]; rfl

theorem zzplus_int {r : ℕ} {t : Loc.Term V M r} (ht : H.IsGeneric t) (a b : Fin (r + 1)) :
    H.ZZplus t a b ∈ M.R := by
  obtain ⟨⟨hSD, hF, hF', -, -, hG⟩, hP⟩ := ht
  have hfL : ∀ a, t.f a ∈ t.abelian₂ := hF.1.1
  have hfL' : ∀ a, t.f' a ∈ t.abelian₂ := hF'.1.1
  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := fun x hx y hy => (hSD.2.2 x).1 hx y hy
  have hff : ∀ a b : Fin (r + 1), H.h (t.f b) (t.f a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF.2.2.1
    · exact hF.2.1 b a (not_and_or.mp hc).symm
  have hff' : ∀ a b : Fin (r + 1), H.h (t.f' b) (t.f' a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T' else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF'.2.2.1
    · exact hF'.2.1 b a (not_and_or.mp hc).symm
  rcases hM : M.split with _ | g
  ·
    have hR : M.R = M.L.O := by simp only [Loc.Model.R, hM]
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [hR]
    exact hint _ (hfL' b) _ (hfL a)
  ·
    obtain ⟨-, ⟨c, hc⟩, -⟩ := hG g hM
    have hq : (g.q : F) ≠ 0 := by
      intro h; apply g.q_irr.ne_zero; exact_mod_cast h
    set q : F := (g.q : F) with hq_def
    set k : E := algebraMap F E q with hk
    set n : Fin (r + 1) → V := fun a => algebraMap F E q⁻¹ • (t.f' a - t.f a) with hn_def
    have hnL : ∀ a, n a ∈ t.abelian₂ := fun a => by
      have := hP.1 (Sum.inr a)
      simpa only [Loc.HermSp.MMfam, hM, Sum.elim_inr] using this
    have hf' : ∀ a, t.f' a = t.f a + k • n a := fun a => by
      simp only [hn_def, hk, smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
      abel
    have hcjk : M.L.cj k = k := M.L.cj.commutes q
    have hek : g.e k = (q, q) := e_alg g q

    have E1 : H.h (t.f' b) (t.f a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) := by
      rw [hf' b, H.h_add_left, H.h_smul_left]
    have E2 : H.h (t.f' a) (t.f b) = H.h (t.f a) (t.f b) + k * H.h (n a) (t.f b) := by
      rw [hf' a, H.h_add_left, H.h_smul_left]
    have E3 : H.h (t.f' b) (t.f' a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) +
        k * H.h (t.f b) (n a) + k * k * H.h (n b) (n a) := by
      rw [hf' b, hf' a]
      simp only [H.h_add_left, H.h_smul_left, h_add_right, h_smul_right, hcjk]
      ring
    have hswap : (g.e (H.h (n a) (t.f b))).2 = (g.e (H.h (t.f b) (n a))).1 := by
      rw [H.h_herm (t.f b) (n a), g.e_cj]; rfl
    have hA := fst_mem (g := g) (hint _ (hnL b) _ (hfL a))
    have hB := snd_mem (g := g) (hint _ (hnL a) _ (hfL b))
    have hC := fst_mem (g := g) (hint _ (hnL b) _ (hnL a))
    have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    have F1 : (g.e (H.h (t.f' b) (t.f a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 := by
      rw [E1]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    have F2 : (g.e (H.h (t.f' a) (t.f b))).2 = (g.e (H.h (t.f a) (t.f b))).2 + q * (g.e (H.h (n a) (t.f b))).2 := by
      rw [E2]; simp only [map_add (f := _), map_mul, hek, Prod.snd_add, Prod.snd_mul]
    have F3 : (g.e (H.h (t.f' b) (t.f' a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 +
        q * (g.e (H.h (n a) (t.f b))).2 + q * q * (g.e (H.h (n b) (n a))).1 := by
      rw [E3, hswap]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    generalize (g.e (H.h (n b) (t.f a))).1 = A at hA F1 F3
    generalize (g.e (H.h (n a) (t.f b))).2 = B at hB F2 F3
    generalize (g.e (H.h (n b) (n a))).1 = C at hC F3
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [mem_R_of_split hM]
    by_cases hcn : a = Fin.last r ∧ b = Fin.last r
    · obtain ⟨rfl, rfl⟩ := hcn
      have h1 := hff (Fin.last r) (Fin.last r)
      have h1' := hff' (Fin.last r) (Fin.last r)
      simp only [and_self, if_true] at h1 h1' ⊢
      rw [h1, map_neg, e_alg] at F1 F2 F3
      rw [h1', map_neg, e_alg] at F3
      simp only [Prod.fst_neg, Prod.snd_neg] at F1 F2 F3
      rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · simp only [Prod.fst_sub]
        have : (-t.T + q * A) / q - -t.T / q = A := by linear_combination A * hqq
        rw [this]; exact hA
      · simp only [Prod.snd_sub]
        have : -((-t.T + q * B) / q) - t.T' / q = q * c - B := by
          linear_combination q⁻¹ * hc + (q * c - B) * hqq
        rw [this]; exact sub_mem (mul_mem g.q.2 c.2) hB
      · simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq
    · have h1 := hff a b
      have h1' := hff' a b
      have h2 : H.h (t.f a) (t.f b) = 0 := by
        have := hff b a
        rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hcn ⟨rfl, rfl⟩)] at this
        exact this
      rw [if_neg hcn] at h1 h1' ⊢
      rw [h1, map_zero] at F1 F3
      rw [h2, map_zero] at F2
      rw [h1', map_zero] at F3
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at F1 F2 F3
      rw [sub_zero, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · have : q * A / q = A := by linear_combination A * hqq
        simp only; rw [this]; exact hA
      · have : -(q * B / q) = -B := by linear_combination (-B) * hqq
        simp only; rw [this]; exact neg_mem hB
      · simp only
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq

end IntegralGeneration

variable {D : Formalism.BasicNotions.D7}

theorem intGenP_holds (Zd : LocDat D) : IntGenP Zd :=
  fun p _ ht a b => IntegralGeneration.zzplus_int (locH Zd p) ht a b

end Formalism.L2.SG.Pf.PCount
end
end

