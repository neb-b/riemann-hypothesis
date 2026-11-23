module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerConj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def locL (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) * A.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))
  | some g => glue g.e (Matrix.diagonal (cf Zd p) * A.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p))

def locR (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) * B.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
  | some g => glue g.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
      (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))

theorem tr_lem {K : Type*} [CommRing K] {n : ℕ} (S L X B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1)
    (hSt : S.transpose = S) :
    (L * (X * S) * B * S).transpose * S = (S * B.transpose * S) * (X.transpose * S) * (S * L.transpose * S) := by
  simp only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S, hS, Matrix.one_mul]

theorem corner_conj {K : Type*} [CommRing K] {r : ℕ} {L U Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hL : IsLo L)
    (hU : IsUp U) (c : K) : L * (Y - c • Ecorner r) * U = L * Y * U - c • Ecorner r := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]

theorem locMove (u u' : D.what₂.Word) (p : PlF D) {Z₁ Z₂ A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B)
    (h : Z₂ * Sg D.host.E D.R.rS = A * (Z₁ * Sg D.host.E D.R.rS) * B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p =
      locL Zd p A B * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A B := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    rw [zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul,
      regroup fr fri hfr]
    simp only [locL, locR, hM]
    rfl
  · obtain ⟨hge, hgq⟩ := hAg
    have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
    have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p
    have hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) :=
      isLo_conj (isLo_map _ hA) _ _ hcc
    have hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) :=
      isUp_conj (isUp_map _ hB) _ _ hcc'
    have hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hL2 := isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc
    have hU2 := isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'
    have hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS := by
      rw [← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    simp only [locL, locR, hM, hge]
    apply mat_eq sg.e
    · have l1 := zz1' Zd p sg hR g hM hge hgq u u' Z₂
      have r1 := zz1' Zd p sg hR g hM hge hgq u u' Z₁
      have key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) =
          A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) *
            B.map ((p1 sg.e).comp (D.s.atP p).ιE) := by simp only [Matrix.map_mul]
      rw [h, key1, fact1 (cf Zd p) (cfi Zd p) hcc'] at l1
      refine l1.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]
    · have e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
          (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
        rw [hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
        exact tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)
      have l2 := zz2' Zd p sg hR g hM hge hgq u u' Z₂
      have r2 := zz2' Zd p sg hR g hM hge hgq u u' Z₁
      rw [e2, fact1 (cf Zd p) (cfi Zd p) hcc'] at l2
      refine l2.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]

end Formalism.L2.SG.Pf.TupGlob
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdCut

def liftF {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') : LFlag (D.sp.Y 0) D.R.rS T' := ⟨F'.fl, F'.fl.z⟩

theorem isom_of_N0F {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
  hn.1

theorem mapL_lf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    mapL n (isom_of_N0F hn) (lf D F0) = lf D F0 := by
  apply mapL_eq_self
  · intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.2
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.1 i
  · exact hn.2.2.2.2

theorem zhatL_mapL_N0F {T' : D.host.E} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') : ZhatL (lf D F0) (mapL n (isom_of_N0F hn) F') = ZhatL (lf D F0) F' := by
  conv_lhs => rw [← mapL_lf hn]
  exact zhat_mapL n (isom_of_N0F hn) (lf D F0) F'

theorem mem_EZ_of {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : PairVal.MatR D)
    (hT : IsTerm Λ₂ (gS D) (lf D F0) F'₂) (hA : AdmWit Λ₂ (gS D) (lf D F0) F'₂ 1)
    (hG : IsGeneric Λ₂ (gS D) (lf D F0) F'₂) (hO : FrameOK D Λ₂ F'₂) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    mapL n (isom_of_N0F hn) F'₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z := by
  have hβ := isom_of_N0F hn
  have hF := mapL_lf hn
  subst hΛ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hF]
    refine ⟨(IsLift_mapL n hβ Λ₂ F'₂).2 hT.1, (IsAdmissible_mapL n hβ _ Λ₂ _ F'₂).2 hT.2.1, ?_⟩
    exact (gval_mapL n hβ (lf D F0) F'₂).symm ▸ hT.2.2
  · rw [← hF]
    exact (AdmWit_mapL n hβ _ Λ₂ _ F'₂ 1).2 hA
  · rw [← hF]
    exact (generic_isomorphism_holds (S := VS D) (r := D.R.rS) (gS D) _ _ n hβ Λ₂ (lf D F0) F'₂).2 hG
  · have h := (positive_definite_isomorphism D u' n hβ Λ₂ (lf D F0) F'₂).2 ⟨hT.1, hT.2.1, hO⟩
    exact h.2.2
  · exact (zhatL_mapL_N0F hn F'₂).trans hZ

theorem gmap_eq_of_image {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (Λ : Set (VS D).V)) : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ := by
  apply SetLike.coe_injective
  rw [coe_gmap]
  exact h

end BwdCut

open BwdCut

variable (u u' F0 what₂)

def BwdN : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ n ∈ unipotentFrameFixers F0,
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def BwdPair : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
          Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls (mapL n (isom_of_N0F hn) (liftF F'₂))

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPart
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def OmV {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (v : S.V) : Prop :=
  v ∈ Submodule.span E (Set.range F'.fvec) ∧ ∀ a, S.hT (F.fvec a) v = if a = Fin.last r then 1 else 0

theorem fvec_cs {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem hT_comb {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) (a : Fin (r + 1)) :
    S.hT (F.fvec a) (∑ b, c b • F'.fvec b) = (Zhat F F' *ᵥ c) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eq_zero_of_orth {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0)
    {d : S.V} (hd : d ∈ Submodule.span E (Set.range F'.fvec)) (h : ∀ a, S.hT (F.fvec a) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hd
  have hc : Zhat F F' *ᵥ c = 0 := funext fun a => by rw [← hT_comb]; exact h a
  rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hc]
  simp

theorem exists_om {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) :
    ∃ v, OmV F F' v := by
  set c : Fin (r + 1) → E := (Zhat F F')⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc
  refine ⟨∑ b, c b • F'.fvec b, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩
  rw [hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  by_cases ha : a = Fin.last r
  · subst ha; simp
  · simp [ha]

theorem om_unique {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {v w : S.V}
    (hv : OmV F F' v) (hw : OmV F F' w) : v = w := by
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hv.1 hw.1) fun a => by
    rw [map_sub, hv.2, hw.2, sub_self]
  exact sub_eq_zero.1 this

theorem comb_eq {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {Ω : S.V}
    (hΩ : OmV F F' Ω) (c : Fin (r + 1) → E) (hc : ∀ i : Fin r, S.hT (F.e i) (∑ b, c b • F'.fvec b) = 0) :
    ∑ b, c b • F'.fvec b = S.hT F.z (∑ b, c b • F'.fvec b) • Ω := by
  set v := ∑ b, c b • F'.fvec b with hv
  have hvs : v ∈ Submodule.span E (Set.range F'.fvec) := (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hvs (Submodule.smul_mem _ (S.hT F.z v) hΩ.1))
    fun a => by
      rw [map_sub, map_smul, hΩ.2, smul_eq_mul]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [fvec_last]; simp
      · rw [fvec_cs, hc i]; simp [Fin.castSucc_ne_last]
  exact sub_eq_zero.1 this

end OmP

open OmP

section Cls

variable {D : Formalism.BasicNotions.D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem omCls_of_om {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hZ : ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F') (hdet : (ZhatL (lf D F0) F'₂).det ≠ 0) {Ω₂ Ω' : (VS D).V}
    (h₂ : OmV F0 F'₂.fl Ω₂) (h' : OmV F0 F'.fl Ω') (hX : Ω' - Ω₂ ∈ Xsp (lf D F0)) : OmCls F0 F'₂ F' := by
  intro c hc
  have hZ' : Zhat F0 F'₂.fl = Zhat F0 F'.fl := hZ
  have hdet₂ : (Zhat F0 F'₂.fl).det ≠ 0 := hdet
  have hdet' : (Zhat F0 F'.fl).det ≠ 0 := by rw [← hZ']; exact hdet
  have hc₂ : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'₂.fl.fvec b) = 0 := hc
  have hc' : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'.fl.fvec b) = 0 := by
    intro i
    rw [← fvec_cs, hT_comb, ← hZ', ← hT_comb, fvec_cs]
    exact hc₂ i
  have hμ : (VS D).hT F0.z (∑ b, c b • F'.fl.fvec b) = (VS D).hT F0.z (∑ b, c b • F'₂.fl.fvec b) := by
    rw [← fvec_last, hT_comb, hT_comb, hZ']
  have e₂ := comb_eq F0 F'₂.fl hdet₂ h₂ c hc₂
  have e' := comb_eq F0 F'.fl hdet' h' c hc'
  have hs : ∑ b, c b • (frame F' b - frame F'₂ b) =
      ∑ b, c b • F'.fl.fvec b - ∑ b, c b • F'₂.fl.fvec b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => smul_sub _ _ _
  rw [hs, e', e₂, hμ, ← smul_sub]
  exact Submodule.smul_mem _ _ hX

end Cls

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmDet : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' →
        (ZhatL (lf D F0) (repF γ)).det ≠ 0 ∧ Matrix.det Z ≠ 0

def OmLoc : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 → ∀ Ω₂ Ωγ : (VS D).V, OmV F0 F'₂.fl Ω₂ → OmV F0 (repF γ).fl Ωγ →
        Ω₂ - Ωγ ∈ Xsp (lf D F0)

def OmRep : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 →
    ∀ F', IsPartner γ Z F' → ∀ Ω' Ωγ : (VS D).V, OmV F0 F'.fl Ω' → OmV F0 (repF γ).fl Ωγ →
      Ω' - Ωγ ∈ Xsp (lf D F0)

variable {u u' F0 what₂}

theorem omPart_of (h0 : OmDet Zd u u' F0 what₂) (h1 : OmLoc Zd u u' F0 what₂) (h2 : OmRep u u' F0 what₂) :
    OmPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'₂ φ φ' hS F' hP
  obtain ⟨hdγ, hdZ⟩ := h0 hrows γ Z hC F'₂ φ φ' hS F' hP
  have hZ₂ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hZ' : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hd₂ : (ZhatL (lf D F0) F'₂).det ≠ 0 := by rw [hZ₂]; exact hdZ
  have hd' : (ZhatL (lf D F0) F').det ≠ 0 := by rw [hZ']; exact hdZ
  obtain ⟨Ωγ, hγ⟩ := exists_om F0 (repF γ).fl hdγ
  obtain ⟨Ω₂, h₂⟩ := exists_om F0 F'₂.fl hd₂
  obtain ⟨Ω', h'⟩ := exists_om F0 F'.fl hd'
  have e1 := h1 hrows γ Z hC F'₂ φ φ' hS hdγ hdZ Ω₂ Ωγ h₂ hγ
  have e2 := h2 hrows γ Z hC hdγ hdZ F' hP Ω' Ωγ h' hγ
  refine omCls_of_om F0 F'₂ F' (hZ₂.trans hZ'.symm) hd₂ h₂ h' ?_
  have : Ω' - Ω₂ = (Ω' - Ωγ) - (Ω₂ - Ωγ) := by abel
  rw [this]
  exact Submodule.sub_mem _ e2 e1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starFrame (γ : TermDef.Term D u u' F0 what₂) : Fin (D.R.rS + 1) → (VS D).V :=
  frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹

def starZh (f f' : Fin (D.R.rS + 1) → (VS D).V) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => brS (VS D) (f' b) (f a)

def starOm (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ b, (starZh f f').adjugate b (Fin.last D.R.rS) • f' b

def starCompat (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) =
    leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) ∧
  leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) • starOm (frame (lf D F0)) (starFrame γ) -
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) • starOm (frame (lf D F0)) (frame F'₂) ∈
    Xsp (lf D F0)

variable (u u' F0 what₂)

def StarGenLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Gam1TieCHolds
section
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc MeasureTheory
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem Gam1TieC_holds (Y : Formalism.L2.SG.Full.Full X) :
    LevelOneLatticeAgreement X hb hK FdN FdN' u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq := by
  unfold LevelOneLatticeAgreement
  show Formalism.L2.SG.TermOp.Gam1 Y.TR = _
  rw [Formalism.L2.SG.Pf.gamma_one_typed_places_holds X Y.TR]
  rfl

end Formalism.L2.SG.IntegralApproximation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol MeasureTheory

theorem typFacts_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u u' : D.what₂.Word) : TypFacts X u u' := by
  apply typFacts_of (h1 := gSplitX_holds X) (h3 := Formalism.L2.SG.LocVolKap.kapX X hb u u')
  exact tCongX X u u'

end Formalism.L2.SG.Pf
end
end

