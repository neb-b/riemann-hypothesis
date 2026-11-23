module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_unique {x y : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x γ)
    (hy : RatLink X y γ) : x = y := by
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  obtain ⟨N, -, k1, k2, k3⟩ := hy
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    obtain ⟨w, hw⟩ : ∃ w, X.crd w = Pi.single j 1 :=
      ⟨Formalism.L2.SG.Pf.LatDictK.vOf X (Pi.single j 1), Formalism.L2.SG.Pf.LatDictK.crd_vOf X _⟩
    have e := (h3 w).symm.trans (k3 w)
    rw [hw] at e
    have := congrFun e i
    simpa [Matrix.mulVec_single_one] using this
  have hMN' : M = N := Units.ext hMN
  subst hMN'
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1 v).trans (k1 v).symm))
  · exact Subtype.ext (Units.ext (h2.trans k2.symm))

variable {X} (TR : TypedRed X)

theorem levi_eq_one_of {a : X.B.I.Gf} (ga : Good X a)
    (hb : ∀ j, (X.B.I.fmat a - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)) : levi TR a = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR ga]
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have hI := hA_int X.B.I (hbwd i) (K_mv X.B.I ga.1.1 (hbw j))
  have hZ1 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat a - 1) *ᵥ X.bw j)) :=
    Z_pair_Mo X (hbwd i) (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b) _ (hb j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right] at hZ1
  have hZ := Z_add X.B.I X.B.g hZ1 (X.bw_dual i j)
  rw [show hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - hA X.B.I (X.bwd i) (X.bw j) +
    (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) =
    hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - if i = j then X.ew else 0 by ring] at hZ
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j)) = _
  rw [resT_of_mem TR v hI, res_of_Z_delta TR v hI (i = j) hZ, Pi.one_apply, Units.val_one, Matrix.one_apply]

theorem rep_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u') (p q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ')
    (hpq : GRel X u u' (X.Fu u) (X.Fu u') Λ Λ' p q) :
    ∃ (n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (xn xn' : X.B.I.GA),
      n ∈ NLam Λ (lf D (X.Fu u)) ∧ n' ∈ NLam Λ' (lf D (X.Fu u')) ∧ RatLink X xn n ∧ RatLink X xn' n' ∧
      q.1.2 = n * p.1.2 * n' ∧ q.1.1 = xn * p.1.1 * xn' := by
  obtain ⟨n, hn, n', hn', hq⟩ := hpq
  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xn', hxn'⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n' hn'.1.1
  refine ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, ?_⟩
  have h1 : RatLink X q.1.1 q.1.2 := q.2.1
  have h2 : RatLink X (xn * p.1.1 * xn') (n * p.1.2 * n') := ratLink_mul X (ratLink_mul X hxn p.2.1) hxn'
  rw [← hq] at h2
  exact ratLink_unique X h1 h2

end Formalism.L2.SG.Pf.AmpIota

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaRepC_holds : Formalism.L2.SG.Pf.SatGramRep.IotaRepC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', -, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, -⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, -⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have ga : Good X a := good_of_ncong X ha1.1 ⟨ha1.2.1, ha1.2.2.1⟩
  have ga' : Good X a' := good_of_ncong X ha1'.1 ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have gκ := good_of_ncong X hκK
    (adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X) hΛ hΛ' p hκK)
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group

  have hlev : ∀ (w : D.what₂.Word) (Lw : Submodule (𝓞 D.host.E) (VS D).V) (hh : Hfin X w) (m : X.B.I.GA)
      (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X m nm → nm ∈ NLam Lw (lf D (X.Fu w)) →
      ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
      Good X (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) →
      levi Y.TR (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) = 1 := by
    intro w Lw hh m nm hm hnm hK gA
    obtain ⟨C, hC⟩ := Formalism.L2.SG.Pf.exists_goodC X w
    have hN0 := Formalism.L2.SG.Pf.nLamNfin_holds D X w Lw m nm hm hnm
    have hN1 := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X w hh⁻¹ m.2 hN0).1
    simp only [Subgroup.coe_inv, inv_inv] at hN1
    have e : ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) =
        (X.xu w)⁻¹ * ((hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf)) * X.xu w := by group
    have hK1 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) ∈ X.B.I.Kset := by
      have e2 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) =
          X.xu w * (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) * (X.xu w)⁻¹ := by group
      rw [e2]
      exact K_mul X.B.I (K_mul X.B.I (X.xu_K w) hK) (K_inv X.B.I (X.xu_K w))
    refine levi_eq_one_of Y.TR gA (fun j => ?_)
    rw [e]
    exact Formalism.L2.SG.Pf.cong_b hC hN1 hK1 j
  have hla := hlev u Λ ((Y.cs u).h ((Y.cs u).base Λ)) xn n hxn hn ha1.1 ga
  have hla' := hlev u' Λ' ((Y.cs u').h ((Y.cs u').base Λ')) xn' n' hxn' hn' ha1'.1 ga'
  show levi Y.TR (kOf X u u' hb hb' q.1.1) = levi Y.TR (kOf X u u' hb hb' p.1.1)
  rw [hk, levi_mul Y.TR (good_mul X ga gκ) ga', levi_mul Y.TR ga gκ, hla, hla', one_mul, mul_one]

theorem ampRepNC_holds : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq Ωp Ωq hΩp hΩq _
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, ha3⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, ha3'⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have hκN := adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X)
    hΛ hΛ' p hκK
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group
  have haN : NCong X a := ⟨ha1.2.1, ha1.2.2.1⟩
  have haN' : NCong X a' := ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hχ : chiN X (kOf X u u' hb hb' q.1.1) =
      X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 := by
    rw [hk, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I ha1.1 hκK) (ncong_mul X ha1.1 haN hκN) haN',
      Formalism.L2.SG.Pf.ChiNMul.chiN_mul X ha1.1 haN hκN]
    have e1 := (ha3 1 Y.hK.1).1
    have e2 := (ha3' 1 Y.hK.1).1
    rw [mul_one, Formalism.L2.SG.Pf.ChiNMul.chiN_one, mul_one] at e1 e2
    rw [e1, e2]
  have hΩq' : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n')) Ωq := by
    rw [← hq]; exact hΩq
  have hoo := oo_rel Formalism.L2.SG.Pf.nLamNinf_holds chiTrivialC_outright Y hΛ hΛ' p hn hn' hxn hxn' hΩp hΩq'
  have hP1 := Formalism.L2.SG.Pf.psiProd_all D X u xn (ratLink_mem X hxn)
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u _ xn n hxn hn) (Formalism.L2.SG.Pf.nLamNfin_holds D X u _ xn n hxn hn)
  have hP2 := Formalism.L2.SG.Pf.psiProd_all D X u' xn' (ratLink_mem X hxn')
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u' _ xn' n' hxn' hn') (Formalism.L2.SG.Pf.nLamNfin_holds D X u' _ xn' n' hxn' hn')
  rw [hχ, hq1]
  rw [hoo, smul_smul]
  have hc : X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 *
      (X.psiInfU u xn.1 * X.psiInfU u' xn'.1) = chiN X (kOf X u u' hb hb' p.1.1) := by
    linear_combination (chiN X (kOf X u u' hb hb' p.1.1)) *
      (X.psiInfU u xn.1 * X.psiFinU u xn.2 * hP2 + hP1)
  rw [hc]

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

def IdMeetKeyC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    ∀ (ρ ρ' : (Y.cs u).Cl) (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)), t.isId →
      Meets (Y.cs u) (Y.cs u) t ρ ρ' →
        ρ = ρ' ∧ t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))

def VolColC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (Ω : Set X.B.I.Ginf),
    IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω → X.muN u Ω = X.muN u (Y.FN u)

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealFramesCharacters
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealFramesCharacters

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fam_rv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  induction a using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u]; rfl
  | cast b => simp only [fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u]; rfl

theorem rv_sum (v : InfinitePlace X.B.I.F) {ι : Type} (t : Finset ι) (c : ι → X.B.I.E) (y : ι → Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (∑ i ∈ t, c i • y i) = ∑ i ∈ t, X.B.I.φ v (c i) • rv X.B.I v (y i) := by
  unfold rv
  have h : (fun j => X.B.I.φ v ((∑ i ∈ t, c i • y i) j)) =
      ∑ i ∈ t, X.B.I.φ v (c i) • (fun j => X.B.I.φ v (y i j)) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_sum]
  congr 1
  funext i
  rw [Matrix.mulVec_smul]

theorem real_frame (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) (v : InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    uMat (x.1 v) *ᵥ fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a =
      ∑ c, X.B.I.φ v (X.ιE.symm (un c a)) • fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) c := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  simp only [fam_rv]
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd, hun, Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  rw [rv_sum]

theorem psiInf_rat (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp un) := by
  refine FormRegularity.psi_of_frame X u x.1 (fun v => (un.map (fun t => X.B.I.φ v (X.ιE.symm t)))ᵀ)
    (fun v a => by simpa [Matrix.transpose_apply, Matrix.map_apply] using real_frame X u hRL un hun v a) _ fun v => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.transpose_apply, Matrix.map_apply, FormRegularity.sgUp_eq, map_sum, star_sum, ← Finset.sum_add_distrib]

end Formalism.L2.SG.RealObj.RealFramesCharacters
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfCol
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ColUniqPf

theorem colUniq_of {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')
    (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs') : ColUniq cs cs' := by
  intro ρ ρ₁ ρ₂ γ₁ γ₂ h₁ h₂ hs
  have hB : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') ∈ X.K2 := by
    have e : ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') =
        (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₁ : X.B.I.Gf) γ₁)⁻¹ *
          kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ₂ : X.B.I.Gf) γ₂ := by
      simp only [kOf, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.2.1 _ h₁.2) _ h₂.2
  obtain ⟨hsI, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hs
  obtain ⟨ν, η, hνη, -, -, hνf, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hs).1 hsI hsf
  have hs2 : (γ₁⁻¹ * γ₂).2 = ν.2 * η.2 := by rw [hνη, Prod.snd_mul]
  have hio : ((iotaF X u' ⟨η, hη⟩ : Hfin X u') : X.B.I.Gf) = η.2 := rfl
  have hn := ((Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u') (cs'.h ρ₁)⁻¹ ν.2 hνf).1
  have hlev := Formalism.L2.SG.Pf.levelDec_holds X u' _ hn
    ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂) (by
      have e : (X.xu u')⁻¹ * ((((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf) * ν.2 *
          (((cs'.h ρ₁)⁻¹ : Hfin X u') : X.B.I.Gf)⁻¹ *
          (((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂ : Hfin X u') : X.B.I.Gf)) * X.xu u' =
          ((cs'.h ρ₁ : X.B.I.Gf) * X.xu u')⁻¹ * (γ₁⁻¹ * γ₂).2 * ((cs'.h ρ₂ : X.B.I.Gf) * X.xu u') := by
        rw [hs2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hio]
        group
      rw [e]
      exact hB)
  obtain ⟨ρ0, -, huniq⟩ := hR (cs'.h ρ₂)
  have e1 := huniq ρ₂ ⟨1, 1, by simp⟩
  have e2 := huniq ρ₁ ⟨(⟨η, hη⟩ : Gam X u')⁻¹,
    ⟨(cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂, hlev.1⟩, by
      show cs'.h ρ₂ = iotaF X u' (⟨η, hη⟩ : Gam X u')⁻¹ * cs'.h ρ₁ *
        ((cs'.h ρ₁)⁻¹ * iotaF X u' ⟨η, hη⟩ * cs'.h ρ₂)
      rw [map_inv]
      group⟩
  exact e2.trans e1.symm

end ColUniqPf

theorem column_uniqueness : ColUniqC := by
  intro D X Y u u' _
  exact ColUniqPf.colUniq_of (Y.cs u) (Y.cs u') Y.hK (Y.colReps u')

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfColCover
section
noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section ColCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
open Matrix

def NStrongApproxC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ n ∈ X.NfinU u, ∀ c : X.B.I.Gf, ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧
      c⁻¹ * ((ν.2)⁻¹ * n) * c ∈ X.K2

theorem hfin_le_sfinU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf)
    (hx : x ∈ Hfin X u) : x ∈ SfinU X u := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) := hx (X.eR a) (Or.inl (Or.inl ⟨a, rfl⟩))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) := hx (X.zR u) (Or.inr rfl)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _

theorem colCoverC_of (hSA : NStrongApproxC) : ColCoverC := by
  intro D X Y u u' hH ρ δ hδ hdec
  obtain ⟨n, h, k, hn, hk, hy⟩ := hdec
  obtain ⟨ρ', ⟨γ0, κ, hh⟩, -⟩ := Y.colReps u' h
  have hK := Y.hK
  have hγ := Subgroup.mem_inf.mp γ0.2
  have hγp := Subgroup.mem_prod.mp hγ.2
  have hh' : (h : X.B.I.Gf) = (γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) *
      ((κ : Hfin X u') : X.B.I.Gf) := by
    rw [hh]
    rfl
  have hκ : (X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u' ∈ X.K2 := κ.2
  obtain ⟨ν, hν, hν1, hν2, hνk⟩ := hSA D X u' hK hH.1 n hn
    ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')
  have hd2 := eq_mul_inv_of_mul_eq hy
  refine ⟨ρ', δ⁻¹ * ν * (γ0 : X.B.I.GA), ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hδ) hν) hγ.1
  · show (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2
    have hT : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') =
        k⁻¹ * ((X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u')⁻¹ *
          (((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * (ν.2⁻¹ * n) *
            ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u'))⁻¹ := by
      simp only [Prod.snd_mul, Prod.snd_inv]
      rw [hd2, hh']
      simp only [aC]
      group
    rw [hT]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hk) _ (hK.2.2.1 _ hκ)) _ (hK.2.2.1 _ hνk)
  · have hcancel : δ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)) = ν * (γ0 : X.B.I.GA) := by group
    rw [hcancel]
    refine Subgroup.mem_inf.mpr ⟨mul_mem hν hγ.1, mul_mem ?_ ?_⟩
    · exact Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩
    · exact Subgroup.subset_closure ⟨hinf_le_sinf X u' _ hγp.1, hfin_le_sfinU X u' _ hγp.2⟩

end ColCoverPf

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfWellDef
section
namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem phase_well_defined_all_words : PhWellDefC := fun _ X _ u _ => Formalism.L2.SG.Pf.phWellDef_holds X u

end Formalism.L2.SG.Pf.RegroupPf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLFinal
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.SatGramActL

theorem left_action_of_local_data (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D)
    (hGen : ∀ D : D7, Formalism.L2.SG.Saturated.GenIso (VS D) D.R.rS (gS D))
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hCB : ChiNBiAll) :
    LeftActC' :=
  left_action_three_families hPD betaLift_holds (sMemLeft_holds hGen hPD) iotaLeft_holds (chiNLeft_holds hCB) ooLeft_holds
    fundConj_holds hIR hAR

end Formalism.L2.SG.Pf.SatGramActL
end
end

