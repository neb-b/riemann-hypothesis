module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpCovOf
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FibreCounting

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem smul_cov (r χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (O O' : V' →L[ℂ] V) (U : V' →L[ℂ] V') (hO : O' = b • O.comp U) :
    r • (χ' • O') = (χ' * b * χ⁻¹) • (r • (χ • O)).comp U := by
  have hχ0 : χ ≠ 0 := by intro h; rw [h, norm_zero] at hχ; exact zero_ne_one hχ
  rw [hO]
  simp only [ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  field_simp

theorem norm_cov (χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (hχ' : ‖χ'‖ = 1) (hb : ‖b‖ = 1) : ‖χ' * b * χ⁻¹‖ = 1 := by
  rw [norm_mul, norm_mul, norm_inv, hχ, hχ', hb]; norm_num

end Gen

section Amp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}


set_option maxHeartbeats 400000 in
theorem oot_cov (hR : RatPt) (hC : ChiTrivialC) {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ (b : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖b‖ = 1 ∧ OOt s' = b • (OOt s).comp (cl U) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  obtain ⟨hl, n, hn, ν, hν, c, hc, hg, hfix, he⟩ := fib_dec h
  have hm : s.lam' = s'.lam' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨xν, hxν⟩ := hR D X ν (nlam_isom hν)
  obtain ⟨xc, hxc⟩ := hR D X c hc
  have hpt : s'.pt = xn * s.pt * xν * xc :=
    ratLink_unique X s'.rep.2.1
      (ratLink_congr (ratLink_mul X (ratLink_mul X (ratLink_mul X hxn s.rep.2.1) hxν) hxc) he.symm)
  have hIA : IsAutLam (VS D) s.lam' c := ⟨hc, gmap_congr hg hm.symm⟩
  have hset : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) :=
    (roset_congr hl.symm hm.symm he).trans (roset_c _ hIA hfix)
  have hconj : ∀ y, y ∈ ROinf s ↔ xn.1 * y * xn.1⁻¹ ∈ ROinf s' := fun y =>
    (roset_conj X hn hν hxn y).trans (Set.ext_iff.1 hset.symm _)
  have hex : (∃ Ω, IsSFund X.B.I (ROinf s) Ω) ↔ (∃ Ω, IsSFund X.B.I (ROinf s') Ω) := by
    constructor
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1 (fun y => ?_) hΩ⟩
      have e : xn.1 * (xn.1⁻¹ * y * xn.1) * xn.1⁻¹ = y := by group
      rw [hconj, e]
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1⁻¹ (fun y => ?_) hΩ⟩
      rw [inv_inv]
      exact hconj y
  by_cases hE : ∃ Ω, IsSFund X.B.I (ROinf s') Ω
  · have hE0 := hex.2 hE
    have hΩp : IsSFund X.B.I (ROinf s) (FundOf s) := by
      unfold FundOf; rw [dite_eq_left hE0]; exact hE0.choose_spec
    have hΩq : IsSFund X.B.I (ROinf s') (FundOf s') := by
      unfold FundOf; rw [dite_eq_left hE]; exact hE.choose_spec
    have key := oo_rel nLamNinf_holds hC Y s.mem s.mem' s.rep hn hν hxn hxν hΩp (isSFund_congr hset hΩq)
    have hsinv : xc.1⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hfix)
    have hB : ∀ x, X.Wu u' (xc.1⁻¹ * x) =
        X.psiInfU u' xc.1⁻¹ • (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv) (X.Wu u' x) :=
      fun x => (X.Wu_spec u').1 _ hsinv x
    have e1 : OOt s' = conj (X.psiInfU u' xc.1⁻¹) •
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1).comp
          ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
            X.Vpi u' →L[ℂ] X.Vpi u') := by
      unfold OOt
      rw [hpt, Prod.fst_mul]
      exact OO_right _ _ _ _ _ xc.1 _ _ hB
    refine ⟨conj (X.psiInfU u' xc.1⁻¹) * (X.psiInfU u xn.1 * X.psiInfU u' xν.1),
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_conj, norm_mul, psiInfU_norm, psiInfU_norm, psiInfU_norm]; norm_num
    · have key' : OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1 =
          (X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s := key
      rw [e1, key']
      have hU : ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
          X.Vpi u' →L[ℂ] X.Vpi u') = cl (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm := by
        ext x; rfl
      rw [hU, ContinuousLinearMap.smul_comp, smul_smul]
  · have hE0 : ¬ ∃ Ω, IsSFund X.B.I (ROinf s) Ω := fun h0 => hE (hex.1 h0)
    have h1 : OOt s' = 0 := by
      unfold OOt FundOf; rw [dite_eq_right hE]; exact OO_empty _ _ _ _
    have h2 : OOt s = 0 := by
      unfold OOt FundOf; rw [dite_eq_right hE0]; exact OO_empty _ _ _ _
    refine ⟨1, LinearIsometryEquiv.refl ℂ _, norm_one, ?_⟩
    rw [h1, h2]
    simp

theorem ampCov_of (hR : RatPt) (hC : ChiTrivialC) (Y : Full X) : AmpCov Y := by
  intro u u' t s s'
  have h : s.1.toTerm = s'.1.toTerm := s.2.trans s'.2.symm
  obtain ⟨b, U, hb, hO⟩ := oot_cov hR hC h
  unfold amp ampN
  refine ⟨_, U, ?_, smul_cov _ _ _ b (norm_chiN _) (OOt s.1) (OOt s'.1) (cl U) hO⟩
  exact norm_cov _ _ b (norm_chiN _) (norm_chiN _) hb

end Amp

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section LocRel

variable {n r : ℕ} (ε : Fin n → Bool)

theorem relA_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hSi : InS e z Si) (hT : InS e z' T) (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (a b : Fin (r + 1)) :
    (∑ c : Fin r, if c.castSucc < a then conj (hJ ε (f c) (Si *ᵥ fam e z a)) *
        RealObj.Zhat ε (fam e z) (fam e z') G c.castSucc b else 0) =
      ∑ c : Fin r, if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) *
        RealObj.Zhat ε (fam e z) (fam e z') G a c.castSucc else 0 := by
  have L : hJ ε (fam e z a) ((S * G) *ᵥ fam e z' b) = hJ ε (fam e z a) ((G * T) *ᵥ fam e z' b) := by
    rw [hrel]
  rw [← Matrix.mulVec_mulVec, hadj, flag_expand ε e f z hfe hfz Si hSi a, hJ_sum_l'] at L
  rw [← Matrix.mulVec_mulVec, flag_expand ε e f z' hfe hfz' T hT b, Matrix.mulVec_add, Matrix.mulVec_sum] at L
  simp only [Matrix.mulVec_smul] at L
  rw [hJ_add_r', hJ_sum_r'] at L
  have L2 := add_left_cancel L
  calc _ = ∑ c : Fin r, conj (if c.castSucc < a then hJ ε (f c) (Si *ᵥ fam e z a) else 0) *
        hJ ε (e c) (G *ᵥ fam e z' b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp
    _ = ∑ c : Fin r, (if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) else 0) *
        hJ ε (fam e z a) (G *ᵥ e c) := L2
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp

theorem rootCoord_one (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0) (a : Fin r) :
    rootCoord ε e f z 1 a = 0 := by
  unfold rootCoord nxt
  rw [Matrix.one_mulVec]
  split_ifs with hlt
  · rw [hfe, if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp at this
  · exact hfz a

theorem rel_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hS : InS e z S) (hSi : InS e z Si) (hSiS : Si * S = 1) (hT : InS e z' T)
    (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y) (hrel : S * G = G * T)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hP2 : ∀ k : Fin r, ((π k.succ).val + 1 = (π k.castSucc).val ∧
        RealObj.Zhat ε (fam e z) (fam e z') G (π k.succ) k.succ = - RealObj.Zhat ε (fam e z) (fam e z') G (π k.castSucc) k.castSucc) ∨
        (π k.castSucc).val < (π k.succ).val) :
    ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re := by
  have h := relAlg (RealObj.Zhat ε (fam e z) (fam e z') G) π hπ hP1 hP2
    (fun c a => hJ ε (f c) (Si *ᵥ fam e z a)) (fun c b => hJ ε (f c) (T *ᵥ fam e z' b))
    (relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel)
  have hU : ∀ k : Fin r, rootCoord ε e f z' T k = hJ ε (f k) (T *ᵥ fam e z' k.succ) := by
    intro k; unfold rootCoord; rw [nxt_eq_fam]
  have hm : ∀ k : Fin r, hJ ε (f k) (Si *ᵥ fam e z k.succ) = - rootCoord ε e f z S k := by
    intro k
    have h1 := Formalism.L2.SG.Pf.Vanish2.rootCoord_mul ε e f z hfe hfz hSi hS k
    rw [hSiS, rootCoord_one ε e f z hfe hfz] at h1
    have h2 : rootCoord ε e f z Si k = hJ ε (f k) (Si *ᵥ fam e z k.succ) := by
      unfold rootCoord; rw [nxt_eq_fam]
    rw [← h2]; linear_combination -h1
  simp only [hU]
  rw [h]
  simp only [hm, Complex.neg_re, Finset.sum_neg_distrib, neg_neg]

theorem sum_add_star {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ∑ a, (x a + star (x a)) = ((2 * ∑ a, (x a).re : ℝ) : ℂ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem psiR_eq_of (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (S T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re) :
    psiR ε gg e f z S = psiR ε gg e f z' T := by
  unfold psiR
  rw [sum_add_star, sum_add_star, h]

theorem psiR_mul_star (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (S : Matrix (Fin n) (Fin n) ℂ) :
    psiR ε gg e f z S * star (psiR ε gg e f z S) = 1 := by
  unfold psiR
  rw [sum_add_star, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring

end LocRel

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a; simp [famSc]

theorem stRel_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StRel X u u' := by
  intro w hw s hs
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dite_eq_left hw.1]; exact hw.1.choose_spec
  unfold psiU psiInf
  rw [Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [← Complex.star_def]
  set ε := X.B.I.ε v
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
  set z := rv X.B.I v (X.zR u)
  set z' := rv X.B.I v (X.zR u')
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e]
    split_ifs <;> simp
  have hfz : ∀ (u : D.what₂.Word) a, hJ ε (f a) (rv X.B.I v (X.zR u)) = 0 := by
    intro u a
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  have hS : InS e z (uMat (s v)) := (hs.1 v).1
  have hT : InS e z' (uMat ((γ⁻¹ * s * γ) v)) := (hs.2 v).1
  have hSiS : uMat (s v)⁻¹ * uMat (s v) = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)
  have hSi : InS e z (uMat (s v)⁻¹) := Formalism.L2.SG.RealObj.InfCut.inS_inv e z _ _ hSiS hS
  have hrel : uMat (s v) * uMat (γ v) = uMat (γ v) * uMat ((γ⁻¹ * s * γ) v) := by
    have e1 : s v * γ v = γ v * (γ⁻¹ * s * γ) v := by
      simp only [Pi.mul_apply, Pi.inv_apply]; group
    have e2 : uMat (s v * γ v) = uMat (γ v * (γ⁻¹ * s * γ) v) := by rw [e1]
    simpa [uMat] using e2

  have hZ : ZX X u u' 1 γ v = RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hP2 : ∀ k : Fin D.R.rS, ((π k.succ).val + 1 = (π k.castSucc).val ∧
      RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.succ) k.succ =
        - RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.castSucc) k.castSucc) ∨
      (π k.castSucc).val < (π k.succ).val := by
    intro k
    have hsz : ∀ b ∈ w.1, 1 ≤ b.2 := fun b hb => (w.2.1 b hb).2
    rcases ptPar_consec w.1 hsz k.val (by rw [hsum]; omega) with h3 | h3
    · left
      refine ⟨h3.1, ?_⟩
      rw [hZe, hZe, if_pos rfl, if_pos rfl]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [h3.2]
      have hk : D.R.rS - k.val = (D.R.rS - (k.val + 1)) + 1 := by omega
      rw [hk, pow_succ]; ring
    · right; exact h3
  have hR := rel_loc ε e f z z' hfe (hfz u) (hfz u') (uMat (s v)) (uMat (s v)⁻¹) (uMat (γ v))
    (uMat ((γ⁻¹ * s * γ) v)) hS hSi hSiS hT (fun x y => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (s v) x y)
    hrel π hπ hP1 hP2
  rw [psiR_eq_of ε X.B.g e f z z' _ _ hR]
  exact psiR_mul_star ε X.B.g e f z' _

end Glob

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CovolIdx
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Formalism.L2.SG.Pf.CovolIdx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem fd_sub (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A]
    (hinv : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R)
    (KA : Set G) (hKA : MeasurableSet KA) (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA)
    (hfin : B.relIndex A ≠ 0) :
    ∃ KC : Set G, MeasurableSet KC ∧ (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ KC) ∧
      μ KC = (B.relIndex A : ℝ≥0∞) * μ KA := by
  classical
  haveI : Finite (A ⧸ B.subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_eq_card]; exact hfin)
  letI : Fintype (A ⧸ B.subgroupOf A) := Fintype.ofFinite _
  have hmk : ∀ q : A ⧸ B.subgroupOf A, ((Quotient.out q : A) : A ⧸ B.subgroupOf A) = q :=
    fun q => QuotientGroup.out_eq' q
  refine ⟨⋃ q : A ⧸ B.subgroupOf A, (fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA,
    MeasurableSet.iUnion fun q => measurable_const_mul _ hKA, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ⟨ha, har⟩, hau⟩ := hKAu r hr
    obtain ⟨q, hq⟩ : ∃ q : A ⧸ B.subgroupOf A, q = ((⟨a, ha⟩ : A) : A ⧸ B.subgroupOf A) := ⟨_, rfl⟩
    have hqB : ((Quotient.out q : A) : G)⁻¹ * a ∈ B := by
      have h1 := QuotientGroup.eq.mp ((hmk q).trans hq)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    refine ⟨((Quotient.out q : A) : G)⁻¹ * a, ⟨⟨A.mul_mem (A.inv_mem (Quotient.out q).2) ha, hqB⟩, ?_⟩, ?_⟩
    · refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      show ((Quotient.out q : A) : G) * (((Quotient.out q : A) : G)⁻¹ * a * r) ∈ KA
      rw [mul_assoc, mul_inv_cancel_left]
      exact har
    · rintro s' ⟨⟨hs'A, hs'B⟩, hs'K⟩
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.mp hs'K
      have hq'' : ((Quotient.out q' : A) : G) * s' * r ∈ KA := by
        rw [mul_assoc]
        exact hq'
      have e1 : ((Quotient.out q' : A) : G) * s' = a :=
        hau _ ⟨A.mul_mem (Quotient.out q').2 hs'A, hq''⟩
      have e2 : q' = q := by
        rw [hq, ← hmk q']
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        have e3 : ((((Quotient.out q' : A))⁻¹ * ⟨a, ha⟩ : A) : G) = s' :=
          (eq_inv_mul_of_mul_eq e1).symm
        rw [e3]
        exact hs'B
      subst e2
      exact eq_inv_mul_of_mul_eq e1
  · have hdisj : Pairwise (fun q q' : A ⧸ B.subgroupOf A =>
        AEDisjoint μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA)
          ((fun x => ((Quotient.out q' : A) : G) * x) ⁻¹' KA)) := by
      intro q q' hne
      show μ (_ ∩ _) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro x hx hxR
      apply hne
      have e := (hKAu x hxR).unique ⟨(Quotient.out q).2, hx.1⟩ ⟨(Quotient.out q').2, hx.2⟩
      have e' := congrArg (fun z : A => (z : A ⧸ B.subgroupOf A)) (Subtype.ext e : Quotient.out q = Quotient.out q')
      simp only [hmk] at e'
      exact e'
    have hmeas : ∀ q : A ⧸ B.subgroupOf A,
        μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA) = μ KA := by
      intro q
      rw [← Measure.map_apply (measurable_const_mul _) hKA, hinv _ (Quotient.out q).2]
    rw [measure_iUnion₀ hdisj (fun q => (measurable_const_mul _ hKA).nullMeasurableSet), tsum_fintype]
    simp only [hmeas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem covol_commens (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A] [Countable B]
    (hinvA : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hinvB : ∀ s ∈ B, μ.map (fun x => s * x) = μ)
    (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R) (hBR : ∀ s ∈ B, ∀ r ∈ R, s * r ∈ R)
    (KA KB : Set G) (hKA : MeasurableSet KA) (hKB : MeasurableSet KB)
    (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA) (hKBu : ∀ r ∈ R, ∃! s, s ∈ B ∧ s * r ∈ KB)
    (hfinA : B.relIndex A ≠ 0) (hfinB : A.relIndex B ≠ 0) :
    μ KA * (B.relIndex A : ℝ≥0∞) = μ KB * (A.relIndex B : ℝ≥0∞) := by
  classical
  obtain ⟨K1, hK1m, hK1u, hK1μ⟩ := fd_sub μ R hR A B hinvA hAR KA hKA hKAu hfinA
  obtain ⟨K2, hK2m, hK2u, hK2μ⟩ := fd_sub μ R hR B A hinvB hBR KB hKB hKBu hfinB
  rw [inf_comm] at hK2u
  haveI : Countable ↥(A ⊓ B) :=
    Function.Injective.countable (Subgroup.inclusion_injective (inf_le_left : A ⊓ B ≤ A))
  letI : MeasurableSpace ↥(A ⊓ B) := ⊤
  haveI : MeasurableSMul ↥(A ⊓ B) G :=
    { measurable_const_smul := fun c => measurable_const_mul (c : G)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : SMulInvariantMeasure ↥(A ⊓ B) G μ := ⟨fun c s hs => by
    show μ ((fun x => (c : G) * x) ⁻¹' s) = μ s
    rw [← Measure.map_apply (measurable_const_mul _) hs, hinvA _ c.2.1]⟩
  have hRa : ∀ᵐ x ∂μ, x ∈ R := ae_iff.mpr hR
  have mkfd : ∀ K : Set G, MeasurableSet K → (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ K) →
      IsFundamentalDomain ↥(A ⊓ B) K μ := by
    intro K hK hu
    refine ⟨hK.nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hRa] with x hx
      obtain ⟨s, ⟨hs, hsK⟩, -⟩ := hu x hx
      exact ⟨⟨s, hs⟩, hsK⟩
    · intro g h hgh
      show μ (((fun x => g • x) '' K) ∩ ((fun x => h • x) '' K)) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro y hy hyR
      apply hgh
      obtain ⟨x1, hx1, e1⟩ := hy.1
      obtain ⟨x2, hx2, e2⟩ := hy.2
      have k1 : (g : G)⁻¹ * y ∈ K := by
        rw [← e1]
        show (g : G)⁻¹ * ((g : G) * x1) ∈ K
        rw [inv_mul_cancel_left]
        exact hx1
      have k2 : (h : G)⁻¹ * y ∈ K := by
        rw [← e2]
        show (h : G)⁻¹ * ((h : G) * x2) ∈ K
        rw [inv_mul_cancel_left]
        exact hx2
      have e := (hu y hyR).unique ⟨(A ⊓ B).inv_mem g.2, k1⟩ ⟨(A ⊓ B).inv_mem h.2, k2⟩
      exact Subtype.ext (inv_injective e)
  have key : μ K1 = μ K2 := (mkfd K1 hK1m hK1u).measure_eq (mkfd K2 hK2m hK2u)
  rw [mul_comm, ← hK1μ, key, hK2μ, mul_comm]

end Formalism.L2.SG.Pf.CovolIdx
end
end

