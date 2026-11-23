module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.NormCut Formalism.L2.SG.PackageTie2 Matrix

namespace Formalism.L2.SG.Pf.Act

section Row

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem isoG_one {u : D.what₂.Word} : isoG (1 : Gam X u) = 1 := by
  apply LinearEquiv.ext
  intro y
  apply inclCrd_inj
  rw [isoG_spec]
  show X.B.I.fmat 1 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem one_mem_gamL {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (q : {Λ // Λ ∈ what₂}) : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) ∈ X.B.I.Kset := by
  have e : colD (cs.h (cs.base q.1)) (iotaF X u 1 * cs.h (cs.base q.1)) =
      (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ * (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)) := by
    unfold colD; simp
  rw [e]
  exact Formalism.L2.SG.Pf.LatDictK.dict_K X _ _ {y | X.B.I.fmat (((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u))⁻¹ *ᵥ
    incl X.B.I (X.crd y) ∈ X.B.I.Lf} (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem cmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (c : GQ X u u' F0 F0' Λ Λ') :
    SatGramActR.cmap x β hN hx c = c := by
  subst hx1 hβ1
  by_cases hβ : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Saturated.AutF Λ' (lf D F0')
  · induction c using Quot.ind with
    | mk p =>
      rw [SatGramActR.cmap_pos _ _ _ _ hβ]
      congr 1
      apply Subtype.ext
      show (p.1.1 * (1 : X.B.I.GA)⁻¹, p.1.2 * (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)⁻¹) = p.1
      simp
  · exact SatGramActR.cmap_neg _ _ _ _ hβ c

theorem tmap_id {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    {x : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hN : SatGramActR.AutFConjN) (hx : RatLink X x β) (hx1 : x = 1) (hβ1 : β = 1)
    (t : GTerm X u u' F0 F0' what₂ rows') : SatGramActR.tmap x β hN hx t = t := by
  obtain ⟨Λ, hΛ, Λ', hΛ', c⟩ := t
  show (⟨Λ, hΛ, Λ', hΛ', SatGramActR.cmap x β hN hx c⟩ : GTerm X u u' F0 F0' what₂ rows') = ⟨Λ, hΛ, Λ', hΛ', c⟩
  rw [cmap_id hN hx hx1 hβ1]

variable {Y : Full X} {u u' : D.what₂.Word}

theorem act_one (q : {Λ // Λ ∈ Y.what₂ u'}) (t : Formalism.L2.SG.PackageTie2.TT Y u u') :
    KernelOfEmbedding.act Y q ⟨1, one_mem_gamL (Y.cs u') q⟩ t = t :=
  tmap_id _ _ rfl isoG_one t

theorem rowFree_of (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) : Formalism.L2.SG.Pf.FibreCounting.RowFree Y := by
  intro u u' s s' h hrow
  obtain ⟨γ, rfl⟩ := KernelOfEmbedding.fib_gam (hN u') h
  have hι := KernelOfEmbedding.iota_act hIR ⟨s.lam', s.mem'⟩ γ s rfl
  have hι2 : iotaOf Y.TR (Y.cs u) (Y.cs u') s =
      iotaOf Y.TR (Y.cs u) (Y.cs u') (KernelOfEmbedding.act Y ⟨s.lam', s.mem'⟩ γ s) := congrArg (fun r => r.2.2) hrow
  rw [hι] at hι2
  have hl : levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1) = 1 := by
    have h3 : iotaOf Y.TR (Y.cs u) (Y.cs u') s * (levi Y.TR (SatGramActL.kB (Y.cs u') s.lam' γ.1))⁻¹ =
        iotaOf Y.TR (Y.cs u) (Y.cs u') s * 1 := by rw [mul_one]; exact hι2.symm
    exact inv_eq_one.1 (mul_left_cancel h3)
  have hg : gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ γ =
      gamL_levi (Y.cs u') Y.TR ⟨s.lam', s.mem'⟩ ⟨1, one_mem_gamL (Y.cs u') ⟨s.lam', s.mem'⟩⟩ := by
    apply Subtype.ext
    show levi Y.TR (colD _ _) = levi Y.TR (colD _ _)
    have e1 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' γ.1 * (Y.cs u').h ((Y.cs u').base s.lam')) =
        SatGramActL.kB (Y.cs u') s.lam' γ.1 := (aK_eq _ _).symm
    have e2 : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' 1 * (Y.cs u').h ((Y.cs u').base s.lam')) = 1 := by
      unfold colD; simp
    rw [e1, e2, hl, levi_one]
  have h1 := (gamL_levi_bij (Y.cs u') Y.TR Y.hK (hN u') ⟨s.lam', s.mem'⟩).1 hg
  rw [h1, act_one]

theorem liftIotaFree (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : SatGramRep.IotaRepC) (u u' : D.what₂.Word) (s₁ s₂ : Formalism.L2.SG.PackageTie2.TT Y u u') (h : s₁.toTerm = s₂.toTerm)
    (hr : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂) : s₁ = s₂ :=
  rowFree_of hN hIR u u' s₁ s₂ h hr

end Row

end Formalism.L2.SG.Pf.Act
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAd
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hermitian_module_dual_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bwd j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).2 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  exact dual_beta_reference_congruence j a

theorem mem_module_of_congruences {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hbd : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) v))
    (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) : v ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  rw [show v = (v - repr0 X v) + repr0 X v by abel]
  refine add_mem (mL_Mo X.B.I hd) ?_
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine sum_mem fun a _ => ?_
    have : hA X.B.I (X.f0 a) v • X.e0 a = (⟨_, hA_int X.B.I (hF a) hv⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hbd l) (hB l))
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

theorem hA_bwd_K (δ : X.B.I.Gf) (k j : Fin D.R.k) : hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j) = 0 := by
  rw [X.bwd_w k, X.bwd_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA]
  have := X.ew_orth
  linear_combination (hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j)) * this

variable {X} (TR : TypedRed X)
include TR

theorem adTriv_inv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) :
    Formalism.L2.SG.Pf.AdTriv X δ⁻¹ := by
  have gδ := good_of_ncong X hK hN
  have h1 : levi TR δ = 1 := (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR gδ).2 hT
  refine (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR (good_inv X gδ)).1 ?_
  rw [levi_inv TR gδ, h1, inv_one]

theorem adTriv_bwd {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) (j : Fin D.R.k) :
    (X.B.I.fmat δ - 1) *ᵥ X.bwd j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hNi := ncong_inv X hK hN
  have hTi := adTriv_inv TR hK hN hT
  have hadj : ∀ y : VA X.B.I, hA X.B.I y ((X.B.I.fmat δ - 1) *ᵥ X.bwd j) =
      hA X.B.I ((X.B.I.fmat δ⁻¹ - 1) *ᵥ y) (X.bwd j) := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_adj, Matrix.sub_mulVec, Matrix.one_mulVec,
      hA_sub_left]
  refine mem_module_of_congruences X (K_sub_mv X.B.I hK (hBd j)) (fun a => ?_) ?_ (fun l => ?_) (fun l => ?_)
  · rw [hadj]
    exact hermitian_module_dual_beta_congruence X (Mo_mono X.B.I (Set.image_subset_range _ _) (hNi.1 a)) j
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X hNi.2 j
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_bwd_K, hA_bwd_bwd, sub_zero]
    exact Z_zero X.B.I X.B.g
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X (hTi l) j

theorem adFull_of_adTriv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ)
    {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w)) :
    (X.B.I.fmat δ - 1) *ᵥ w ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hw
  have hsm : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (m : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      m ∈ Mo X.B.I X.B.g (Set.range X.e0) → c • m ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c m hc hm => by
    have : c • m = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • m := rfl
    rw [this]; exact Submodule.smul_mem _ _ hm
  rw [show w = (w - repr0 X w) + repr0 X w by abel, Matrix.mulVec_add]
  refine add_mem (mL_Mo X.B.I ?_) ?_
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mem_mL_of_Kset X hK _ hd) hd
  unfold repr0
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, mulVec_fsum X, Matrix.mulVec_smul]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => hsm _ _ (hA_int X.B.I (hF a) hw)
      (Mo_mono X.B.I (Set.image_subset_range _ _) (hN.1 a))
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (K_sub_mv X.B.I hK (hF a)))
  · exact hsm _ _ (hA_int X.B.I hZ hw) hN.2
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hBd l) hw) (hT l)
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hB l) hw) (adTriv_bwd TR hK hN hT l)

end Formalism.L2.SG.Pf.BridgeAd
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKeyPf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
open Matrix

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

theorem isId_rat {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (t : GTerm X u u (X.Fu u) (X.Fu u) what₂ what₂) (ht : t.isId) :
    (∀ a : Fin D.R.rS, t.lin (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1})) ∧
      t.lin (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX) := by
  have hin := Formalism.L2.SG.FourParts.isInS_of_isIdT ht
  have hS : Formalism.L2.SG.FourParts.InSF (lf D (X.Fu u)) t.frame :=
    (Formalism.L2.SG.FourParts.isInS_mk (Λ := t.lam) (F := lf D (X.Fu u))
      (P := Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u)
      (PI.InSClassConstW.inSFun_all _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩).1 hin
  have hfr : t.frame.fl = mapFlag t.rep.1.2 t.rep.2.2.1 (lf D (X.Fu u)).fl := by
    show (mapLF t.rep.1.2 (lf D (X.Fu u))).fl = _
    simp only [mapLF, dite_eq_left t.rep.2.2.1]
  refine ⟨fun a => ?_, ?_⟩
  · have h := hS.1 a
    have e1 : t.frame.fl.e a = t.lin (X.eX a) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).e a) = t.rep.1.2 (X.eX a)
      rw [X.Fu_e u]
    have e2 : (lf D (X.Fu u)).fl.e a = X.eX a := by
      show (X.Fu u).e a = _
      rw [X.Fu_e u]
    have e3 : Xflag (lf D (X.Fu u)) a.val = Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h
  · have h := hS.2
    have e1 : t.frame.fl.z = t.lin (X.zu u) := by
      rw [hfr]
      show t.rep.1.2 ((X.Fu u).z) = t.rep.1.2 (X.zu u)
      rw [X.flagZVector u]
    have e2 : (lf D (X.Fu u)).fl.z = X.zu u := by
      show (X.Fu u).z = _
      rw [X.flagZVector u]
    have e3 : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range (X.Fu u).e) := rfl
    rw [e1, e2, e3, X.Fu_e u] at h
    exact h

theorem pt_srat {u : D.what₂.Word} {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}))
    (hz : n (X.zu u) - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX)) : x ∈ Srat X u := by
  have hmem := ratLink_mem X hx
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  have hE : ∀ a : Fin D.R.rS, ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a ∈
      Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
    intro a
    have := crd_span' X (he a)
    rw [Set.image_image] at this
    show _ *ᵥ X.crd (X.eX a) ∈ _
    rw [mcrd X h3]
    exact this
  have hZ : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.zR u ∈
      Submodule.span X.B.I.E (Set.range X.eR) := by
    have := crd_span' X hz
    rw [← Set.range_comp] at this
    show _ *ᵥ X.crd (X.zu u) ∈ _
    rw [mcrd X h3]
    exact this
  have transfer {R : Type} [CommRing R] (j : X.B.I.E →+* R)
      (ι : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → R))
      (hs : ∀ c x, ι (c • x) = j c • ι x)
      (G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) R)
      (hG : ∀ y, G *ᵥ ι y = ι (M *ᵥ y))
      (S : Set (Fin D.R.rS)) (y : Fin X.B.I.n → X.B.I.E)
      (hy : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ y ∈ Submodule.span X.B.I.E (X.eR '' S)) :
      (G - 1) *ᵥ ι y ∈ Submodule.span R ((fun b => ι (X.eR b)) '' S) := by
    have hspan : ∀ {z}, z ∈ Submodule.span X.B.I.E (X.eR '' S) →
        ι z ∈ Submodule.span R (ι '' (X.eR '' S)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [hs]; exact Submodule.smul_mem _ _ ha
    have hh := hspan hy
    rw [Set.image_image] at hh
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hG, ← map_sub]
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hh
  let rmap (v : InfinitePlace X.B.I.F) : (Fin X.B.I.n → X.B.I.E) →+ (Fin X.B.I.n → ℂ) :=
    { toFun := rv X.B.I v
      map_zero' := by
        unfold rv
        have : (fun i => X.B.I.φ v ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by funext i; simp
        rw [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        unfold rv
        rw [← Matrix.mulVec_add]
        congr 1
        funext i; simp }
  have rsmul (v : InfinitePlace X.B.I.F) (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
      rmap v (c • x) = X.B.I.φ v c • rmap v x := by
    change rv X.B.I v (c • x) = X.B.I.φ v c • rv X.B.I v x
    unfold rv
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i; simp
  let imap : (Fin X.B.I.n → X.B.I.E) →+ VA X.B.I :=
    { toFun := incl X.B.I
      map_zero' := by funext i; simp [incl]
      map_add' := by intro x y; funext i; simp [incl] }
  have ismul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
      imap (c • x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) c • imap x := by
    funext i
    simp [imap, incl]
  refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.subset_closure ⟨fun v => ?_, ?_⟩⟩
  · have hG : ∀ y, uMat (x.1 v) *ᵥ rmap v y =
        rmap v ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      change uMat (x.1 v) *ᵥ rv X.B.I v y = rv X.B.I v (M *ᵥ y)
      rw [h1 v]
      exact rv_mulVec X v _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact transfer (X.B.I.φ v) (rmap v) (rsmul v) _ hG _ _ (hE a)
    · have := transfer (X.B.I.φ v) (rmap v) (rsmul v) _ hG Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      unfold spanLt
      rw [← range_eq_image_lt]
      rwa [Set.image_univ] at this
  · have hG : ∀ y, X.B.I.fmat x.2 *ᵥ imap y =
        imap ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
      intro y
      change X.B.I.fmat x.2 *ᵥ incl X.B.I y = incl X.B.I (M *ᵥ y)
      rw [h2]
      exact incl_mulVec X _ y
    refine ⟨fun a => ?_, ?_⟩
    · exact transfer _ imap ismul _ hG _ _ (hE a)
    · have := transfer _ imap ismul _ hG Set.univ _
        (by rw [Set.image_univ]; exact hZ)
      rwa [Set.image_univ] at this

theorem lin_eq_of_fst {x y : X.B.I.GA} {m n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hy : RatLink X y n) (h : x.1 = y.1) : m = n := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  obtain ⟨N, -, k1, -, k3⟩ := hy
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have e3 : ∀ A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
      X.B.I.P v * ((X.B.I.P v)⁻¹ * A * X.B.I.P v) * (X.B.I.P v)⁻¹ = A := by
    intro A
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hP]
  have e : (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v =
      (X.B.I.P v)⁻¹ * (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v := by
    rw [← h1 v, ← k1 v, h]
  have e2 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) =
      (N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) := by
    rw [← e3 ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)),
      ← e3 ((N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)), e]
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    exact (X.B.I.φ v).injective (congrFun (congrFun e2 i) j)
  refine LinearEquiv.ext fun p => ?_
  rw [← toV_crd X (m p), ← toV_crd X (n p), h3, k3, hMN]

end Formalism.L2.SG.Pf.IdMeet

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.Pf.Level

theorem idMeetKeyC_holds : IdMeetKeyC := by
  intro D X Y u hNeat ρ ρ' t ht hM
  obtain ⟨-, -, hk⟩ := hM
  obtain ⟨he, hz⟩ := isId_rat X t ht
  have hs : t.pt ∈ Srat X u := pt_srat X t.rep.2.1 he hz
  have hg : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) ∈ X.K2 := hk
  obtain ⟨hs1, hs2⟩ := sratComp_holds X u t.pt hs
  obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ :=
    Formalism.L2.SG.Pf.ratLevi_holds X u t.pt (Subgroup.mem_inf.1 hs).1 hs1 hs2
  obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
  have hs2e : t.pt.2 = ν.2 * η.2 := by rw [hνη]; rfl
  obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ)⁻¹ ν.2 hν2
  have hLD := Formalism.L2.SG.Pf.Level.levelDec_of_psiDd (X := X) (u := u) (Formalism.L2.SG.Pf.psiDd_holds X)
  obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' := ⟨_, rfl⟩
  have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ)⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
      (h1 : X.B.I.Gf)) * X.xu u =
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u) := by
    rw [hs2e, hh1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
    group
  have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
  have hρρ : ρ = ρ' := by
    refine (Y.colReps u ((Y.cs u).h ρ')).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
    show (Y.cs u).h ρ' = iotaF X u ηg⁻¹ * (Y.cs u).h ρ * h1
    rw [map_inv, hh1]
    group
  subst hρρ
  have hmem : ((Y.cs u).h ρ)⁻¹ * iotaF X u ηg * (Y.cs u).h ρ ∈ Ku X u Y.hK := by
    rw [← hh1]; exact hh1K
  have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ) ηg hmem
  have hη1' : η = 1 := by
    have := congrArg Subtype.val hη1
    rw [hηg] at this
    exact this
  have hsν : t.pt = ν := by rw [hνη, hη1', mul_one]
  have hsN := nilradical_rational_lattice D X Y u ρ t.pt (Formalism.L2.SG.Closed.level_subgroup_properties X)
    (by rw [hsν]; exact hνG) (by rw [hsν]; exact hν1) (by rw [hsν]; exact hν2) hg
  obtain ⟨x, n, hx, hx1, hn⟩ := hsN
  refine ⟨rfl, ?_⟩
  have hl : t.lin = n := lin_eq_of_fst X t.rep.2.1 hx hx1
  rw [hl]
  exact hn

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaBridgeHalves
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaBridgeARC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) → RatTriv u X Λ β

def IotaBridgeRAC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      RatTriv u X Λ β → AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u))

end Formalism.L2.SG.Pf
end
end

