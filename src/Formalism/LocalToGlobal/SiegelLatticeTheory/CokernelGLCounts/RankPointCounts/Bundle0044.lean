module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrameLA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardAutLzGmap
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem inv_apply' (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) : (δ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) y = δ.symm y :=
  rfl

theorem xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp [Fin.is_lt]

theorem st_mul {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (hδ : δ ∈ stabF D F0) :
    γ * δ ∈ stabF D F0 := by
  refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
  · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
  · show γ (δ F0.z) = F0.z
    rw [hδ.2.2, hγ.2.2]

theorem st_inv {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ⁻¹ ∈ stabF D F0 := by
  refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← hγ.2.1 j]
    rw [← kmap_mul, inv_mul_cancel, kmap_one]
  · show γ.symm F0.z = F0.z
    conv_lhs => rw [← hγ.2.2]
    exact γ.symm_apply_apply _

theorem stab_X_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact Submodule.mem_map_of_mem hx

theorem stab_perp_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 := hy _ (stab_X_mem F0 (st_inv F0 hγ) hx)
  have h2 := hγ.1 (γ⁻¹ x) y
  rw [inv_apply', LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact h1

def ind {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun y hy => stab_perp_mem F0 hγ hy))
    (fun x hx => stab_X_mem F0 hγ hx)

theorem ind_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ind F0 hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, stab_perp_mem F0 hγ x.2⟩ := rfl

theorem autLz_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) :
    φ ∈ autLz D F0 Λ ↔ ∃ γ, ∃ hγ : γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ φ = ind F0 hγ := by
  constructor
  · rintro ⟨γ, hγ, hΛ, hφ⟩
    refine ⟨γ, hγ, hΛ, funext fun q => ?_⟩
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    exact (hφ x (stab_perp_mem F0 hγ x.2)).trans rfl
  · rintro ⟨γ, hγ, hΛ, rfl⟩
    exact ⟨γ, hγ, hΛ, fun x hx => rfl⟩

theorem ind_inv_cancel {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 (st_inv F0 hδ) (ind F0 hδ q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ⁻¹ (δ x.1) = x.1
  rw [inv_apply', LinearEquiv.symm_apply_apply]

theorem card_autLz_gmap {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card ↥(autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ)) = Nat.card ↥(autLz D F0 Λ) := by
  let c : (WbQ D F0 → WbQ D F0) → (WbQ D F0 → WbQ D F0) := fun φ => ind F0 hδ ∘ φ ∘ ind F0 (st_inv F0 hδ)
  have hc : Function.Injective c := by
    intro φ ψ hφψ
    funext q
    have h1 := congrFun hφψ (ind F0 hδ q)
    simp only [c, Function.comp, ind_inv_cancel] at h1
    have h2 := congrArg (ind F0 (st_inv F0 hδ)) h1
    rwa [ind_inv_cancel, ind_inv_cancel] at h2
  have hset : autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ) = c '' autLz D F0 Λ := by
    ext ψ
    rw [autLz_iff, Set.mem_image]
    constructor
    · rintro ⟨γ', hγ', hΛ', rfl⟩
      refine ⟨ind F0 (st_mul F0 (st_mul F0 (st_inv F0 hδ) hγ') hδ),
        (autLz_iff F0 Λ _).2 ⟨_, _, ?_, rfl⟩, ?_⟩
      · rw [gmap_mul', gmap_mul', hΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => ?_)
        simp only [c, Function.comp]
        rw [ind_mk, ind_mk, ind_mk, ind_mk]
        congr 1
        apply Subtype.ext
        show δ ((δ⁻¹ * γ' * δ) (δ⁻¹ x.1)) = γ' x.1
        show δ (δ⁻¹ (γ' (δ (δ⁻¹ x.1)))) = γ' x.1
        rw [inv_apply', inv_apply', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨γ, hγ, hΛ, rfl⟩ := (autLz_iff F0 Λ φ).1 hφ
      refine ⟨δ * γ * δ⁻¹, st_mul F0 (st_mul F0 hδ hγ) (st_inv F0 hδ), ?_, ?_⟩
      · rw [gmap_mul', ← gmap_mul' δ⁻¹ δ, inv_mul_cancel, gmap_one', gmap_mul', hΛ]
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => rfl)
  rw [hset]
  exact Nat.card_image_of_injective hc _

end Ind

end Formalism.L2.SG.RhoPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def CohLp : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite

def CohIota : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ g, (Zd.M p).split = some g →
      Prod.map ⇑(φ' p) ⇑(LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
          (locH Zd p).iotaGraph g (tLoc Zd p γ) =
        (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))}.Finite

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrame
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_fvec_zero {r : ℕ} {T : E} (F : FlagG S r T) :
    ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → gram S F.fvec F.fvec i j = 0 := by
  intro i j hij
  have hfe : ∀ a : Fin r, F.fvec (Fin.castSucc a) = F.e a := fun a => by simp [FlagG.fvec]
  have hfz : F.fvec (Fin.last r) = F.z := by simp [FlagG.fvec]
  simp only [gram]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp at hij
    | cast b =>
      rw [hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]
      exact F.z_orth b
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [hfz, hfe]; exact F.z_orth a
    | cast b => rw [hfe, hfe]; exact F.e_iso a b

theorem gram_fvec_last {r : ℕ} {T : E} (F : FlagG S r T) :
    gram S F.fvec F.fvec (Fin.last r) (Fin.last r) = -T := by
  simp only [gram, FlagG.fvec, Fin.snoc_last]
  exact F.z_norm

theorem comb_frame {r : ℕ} {T : E} (F : FlagG S r T) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ a b, b < a → A a b = 0) (hA1 : ∀ a, A a a = 1) :
    (∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (comb S F.fvec A a) (comb S F.fvec A b) = 0) ∧
      S.hT (comb S F.fvec A (Fin.last r)) (comb S F.fvec A (Fin.last r)) = -T := by
  have hg : ∀ a b, S.hT (comb S F.fvec A a) (comb S F.fvec A b) =
      star (A (Fin.last r) a) * (-T) * A (Fin.last r) b := by
    intro a b
    have e := congrFun (congrFun (show gram S (comb S F.fvec A) (comb S F.fvec A) = Aᴴ * (gram S F.fvec F.fvec * A) by
      rw [gram_comb_right, gram_comb_left]) a) b
    simp only [gram] at e
    rw [e, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r), gram_fvec_last, Matrix.conjTranspose_apply, mul_assoc]
      · intro c _ hc; rw [gram_fvec_zero F _ _ (Or.inr hc), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc
      rw [Matrix.mul_apply, Finset.sum_eq_zero fun d _ => by rw [gram_fvec_zero F _ _ (Or.inl hc), zero_mul], mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hl : ∀ a, a ≠ Fin.last r → A (Fin.last r) a = 0 := fun a ha => hA _ _ (Fin.lt_last_iff_ne_last.2 ha)
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [hg]
    rcases hab with h | h
    · rw [hl a h, star_zero, zero_mul, zero_mul]
    · rw [hl b h, mul_zero]
  · rw [hg, hA1, star_one, one_mul, mul_one]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem star_frame_orthogonal (γ : TermDef.Term D u u' F0 what₂) :
    (∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (starFrame γ a) (starFrame γ b) = 0) ∧
      (VS D).hT (starFrame γ (Fin.last D.R.rS)) (starFrame γ (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  exact FsLA.comb_frame (repF γ).fl
    (fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E))
    (fun a b h => by simp [hξ1 a b h]) (fun a => by simp [hξ2 a])

variable (u u' F0 what₂)

def StarMinors : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    Z.det ≠ 0 ∧ (starZh (frame (lf D F0)) (starFrame γ)).det ≠ 0 ∧
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS * Z.det =
        leadMinorE Z D.R.rS * (starZh (frame (lf D F0)) (starFrame γ)).det

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmDetPf
section
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  apply hG
  apply Eq.trans (fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm))
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIso
section
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

def BridgeIso : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∀ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m →
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m → M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

section Det

variable {K : Type*} [CommRing K] {m : ℕ}

theorem det_shift {n s : K} {P X L U : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hL : IsLo L) (hU : IsUp U)
    (hP : P = L * X * U) (hX : ∀ a : Fin m, X a.castSucc (Fin.last m) = 0 ∧ X (Fin.last m) a.castSucc = 0)
    (hs : X (Fin.last m) (Fin.last m) = s) : (P + n • Ecorner m).det = (s + n) * leadM P m := by
  have e : P + n • Ecorner m = L * (X + n • Ecorner m) * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU, hP]
  have hX' : ∀ a : Fin m, (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a.castSucc (Fin.last m) = 0 ∧
      (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) a.castSucc = 0 := fun a => by
    simp [Ecorner, (hX a).1, (hX a).2, Fin.castSucc_ne_last]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_lo' hL, det_up' hU, one_mul, mul_one, det_of_corner _ hX',
    leadM_add_corner, hP, leadM_mul hL hU]
  simp [Ecorner, hs]

end Det

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem lead_eq_head (M : Loc.Model F E) {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (Y : M.Mat m)
    (hY : ∀ a b : Fin m, (Y.Z a b : E) = P a.castSucc b.castSucc) : leadM P m = (Y.Z.map M.R.subtype).det := by
  unfold leadM
  rw [dite_eq_left (Nat.le_succ m)]
  congr 1
  ext a b
  exact (hY a b).symm

end Model

theorem bridgeBA_of (hI : BridgeIso) : BridgeBA := by
  intro F _ _ _ E _ _ _ _ M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂
    be₁ be₂ al₁ al₂ hY hba hi₁ hi₂
  have hX₁ : ∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).1, (hX a).2.1⟩
  have hX₂ : ∀ a : Fin m, X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).2.2.1, (hX a).2.2.2⟩
  have hu₁ : IsUnit (P₁ + n • Ecorner m).det := by
    rw [det_shift hL₁ hU₁ hP₁ hX₁ h₁, lead_eq_head M P₁ Y₁ fun a b => (hY a b).1]
    exact hsn.mul Y₁.unit
  have hu₂ : IsUnit (P₂ + n • Ecorner m).det := by
    rw [det_shift hL₂ hU₂ hP₂ hX₂ h₂, lead_eq_head M P₂ Y₂ fun a b => (hY a b).2]
    exact hsn.mul Y₂.unit
  have hint : ∀ {P : Matrix (Fin (m + 1)) (Fin (m + 1)) E}, (∀ a b, P a b ∈ M.R) →
      ∀ a b, (P + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E) a b ∈ M.R := fun hP a b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, Ecorner, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact M.R.add_mem (hP a b) (by rw [mul_one]; exact hn)
    · rw [mul_zero, add_zero]; exact hP a b
  refine ⟨mkMat M _ (hint hi₁) hu₁, mkMat M _ (hint hi₂) hu₂, rfl, rfl, ?_⟩
  exact hI M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba
    hi₁ hi₂ _ _ rfl rfl

theorem partnerCount_of_iso {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D)
    (hI : IntGenP Zd) (hB : BridgeIso) : PartnerIsomorphismCount Zd :=
  partnerCount_of_integral Zd hT2 hI (bridgeBA_of hB)

end Formalism.L2.SG.Pf.PCount
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NGCut.VanishingOrbitalPoints

theorem stepNormOne_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepNormOne :=
  Formalism.L2.SG.NGCut.LeadingMinorIntegrality.stepNormOne_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'

theorem stepPoints_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepPoints :=
  Formalism.L2.SG.NGCut.PtPf.stepPoints_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'



end Formalism.L2.SG.NGCut.VanishingOrbitalPoints
end
end

