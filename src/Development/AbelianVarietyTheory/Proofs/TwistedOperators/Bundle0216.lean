module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KgFrame

open Formalism.L2.DIV Formalism.L2.Herm Formalism.UG
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem dvd_of_forall_mem (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical)
    (b : 𝓞 E) (hb : ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal) : (g : 𝓞 E) ∣ b := by
  have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  rw [← Ideal.mem_span_singleton]
  refine hr ?_
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro J ⟨hJ, hp⟩
  have hJ0 : J ≠ ⊥ := by
    intro e
    rw [e, le_bot_iff, Ideal.span_singleton_eq_bot] at hJ
    exact hg0 hJ
  exact hb ⟨J, hp, hJ0⟩ (hJ (Ideal.mem_span_singleton_self _))

theorem entries_iff_red (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical) (y : GL (Fin n) (intAf F E)) :
    (∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t) ↔
      ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → bc (resS F PP) y = 1 := by
  constructor
  · intro h PP hP
    have hgk : ((g : ℕ) : kP PP) = 0 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 hP
      rwa [map_natCast] at this
    apply Units.ext
    ext i j
    obtain ⟨t, ht⟩ := h i j
    have h1 := congrArg (resS F PP) ht
    rw [map_sub, map_nsmul, nsmul_eq_mul, hgk, zero_mul, sub_eq_zero] at h1
    show resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro h i j
    refine lc_div g (by omega) (dvd_of_forall_mem g hg hr) _ fun PP hP => ?_
    have h1 := congrArg (fun M : GL (Fin n) (kP PP) => (M : Matrix (Fin n) (Fin n) (kP PP)) i j) (h PP hP)
    change resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j at h1
    rw [map_sub, h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

theorem sub_one_iff_entries (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ)
    (g : ℕ) (y : GL (Fin n) (intAf F E)) :
    (∀ v ∈ hatL (F := F) Λ, ∃ z ∈ hatL (F := F) Λ,
      (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ v =
        (g : E ⊗[F] Formalism.L2.Herm.Af F) • z) ↔
    ∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t := by
  classical
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hB
  set Bi : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hBi
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype with hY
  have hXe : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = B * Y * Bi :=
    lc_frGL_coe β y
  have hBiB : Bi * B = 1 := Units.inv_mul β
  have hBBi : B * Bi = 1 := Units.mul_inv β
  have hX1 : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 = B * (Y - 1) * Bi := by
    rw [hXe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBBi]
  have hYe : ∀ i j, Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j =
      (((y : Matrix (Fin n) (Fin n) (intAf F E)) i j - (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j : intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) := by
    intro i j
    rw [← lc_one_coe]
    rfl
  constructor
  · intro h i j
    obtain ⟨z, hz, e⟩ := h _ (lc_frame_mem hβ (Pi.single j 1) (fun k => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]))
    have hc := (hβ z).1 hz
    refine ⟨⟨(Bi *ᵥ z) i, hc i⟩, ?_⟩
    apply Subtype.ext
    rw [← hYe]
    have e2 := congrArg (fun w => (Bi *ᵥ w) i) e
    beta_reduce at e2
    have hconj : Bi * (B * (Y - 1) * Bi) * B = Y - 1 := by
      calc Bi * (B * (Y - 1) * Bi) * B = (Bi * B) * (Y - 1) * (Bi * B) := by simp only [Matrix.mul_assoc]
        _ = Y - 1 := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [hX1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hB, hconj, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e2
    rw [Pi.smul_apply, smul_eq_mul] at e2
    rw [show (Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) = (Y - 1).col j i from rfl, e2]
    simp [nsmul_eq_mul]
  · intro h
    choose t ht using h
    set M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := fun i j => ((t i j : intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) with hM'
    have hYM : Y - 1 = (g : E ⊗[F] Formalism.L2.Herm.Af F) • M' := by
      ext i j
      rw [Matrix.sub_apply, hYe, ht i j]
      rw [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rfl
    refine fun v hv => ⟨B *ᵥ (M' *ᵥ (Bi *ᵥ v)), lc_frame_mem hβ _ fun i => ?_, ?_⟩
    · have hc := (hβ v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 (hc j)
    · rw [hX1, hYM, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Gen

theorem Lf_eq (D : D7) : (Formalism.L2.SG.InstExistsPf.instOf D).Lf =
      hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  have hΛ : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]; rfl
  show lamAf (F := ↥D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [hΛ]
  unfold lamAf hatL Formalism.UG.latS
  rw [Set.image_eq_range]
  rfl


set_option maxHeartbeats 2000000 in
theorem mem_Kg_iff_redFn : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset → 1 ≤ g →
    (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical →
    (x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔
      ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → Formalism.L2.DIV.redFn β PP x.1 = 1) := by
  intro D β x g hβ hx hg hr
  have hLf := Lf_eq D
  have hSt : x.1 ∈ St β := by
    rw [stabilizer_eq_stabilizer_lattice _ _ _ _ β hβ, ← hLf]
    exact hx
  obtain ⟨y, hy⟩ := hSt
  have hred : ∀ PP : Pl D.host.E, redFn β PP x.1 = bc (resS D.host.F PP) y := fun PP => by
    rw [← hy, redFn_frGL]

  have key := (sub_one_iff_entries _ β hβ g y).trans (entries_iff_red g hg hr y)
  have hfm : (Formalism.L2.SG.InstExistsPf.instOf D).fmat x = (frGL β y).val := by
    show x.1.val = _
    rw [← hy]
  have hv1 := fun v => SetLike.ext_iff.1 hLf v
  constructor
  · intro hk PP hP
    refine (hred PP).trans (key.1 (fun v hv => ?_) PP hP)
    obtain ⟨z, hz, e⟩ := hk.2 v ((hv1 v).2 hv)
    refine ⟨z, (hv1 z).1 hz, ?_⟩
    rw [← hfm]
    exact e
  · intro h
    refine ⟨hx, fun v hv => ?_⟩
    obtain ⟨z, hz, e⟩ := key.2 (fun PP hP => (hred PP).symm.trans (h PP hP)) v ((hv1 v).1 hv)
    refine ⟨z, (hv1 z).2 hz, ?_⟩
    rw [hfm]
    exact e

end GlobalTheory.KgFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Formalism.L2.SG.AdBridge


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem map_thetaV_eq_one (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E))
    (hM : M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) = 1) : M.map (thetaV I v) = 1 := by
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  let evI : Ainf I.F →ₐ[I.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding v).comp
        (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)
      commutes' := fun c => evV_algebraMap I v c }
  let φA : I.E →ₐ[I.F] ℂ := { I.φ v with commutes' := I.φ_over v }
  let θ' := Algebra.TensorProduct.lift evI φA (fun _ _ => Commute.all _ _)
  have key : ∀ z : AF I.F ⊗[I.F] I.E, thetaV I v z =
      θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [thetaV_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have e : M.map (thetaV I v) = (M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E))).map θ' := by
    ext i j; simp only [Matrix.map_apply]; exact key _
  rw [e, hM]
  exact Matrix.map_one _ (map_zero θ') (map_one θ')

theorem fst_eq_one_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) (hx : (hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F) (AlgHom.id I.F I.E)) = 1) :
    x.1 = 1 := by
  funext v
  apply Subtype.ext
  apply Units.ext
  have h1 := (hB x).1 v
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  show uMat (x.1 v) = 1
  rw [h1]
  unfold ofHAInf
  rw [hz]
  rw [map_thetaV_eq_one I v _ hx, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem iota_fst_eq_one {D : D7} (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) :
    (Formalism.IndefR.RationalEmbedding.iota D y).1 = 1 := by
  refine fst_eq_one_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) _ y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y) ?_
  have h := congrArg (fun g : GL (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    g.val) (MonoidHom.mem_ker.1 hy)
  exact h

theorem castGA_fst {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.1 = 1) : (castGA h x).1 = 1 := by
  subst h; exact hx

theorem real_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) : (iotaX X h y).1 = 1 :=
  castGA_fst h.symm _ (iota_fst_eq_one y hy)

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_intAf (U : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hU : ∀ i j, U i j ∈ Formalism.L2.Herm.intAf F E) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hw : ∀ i, w i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) : (U *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hU i j) (hw j)

theorem mem_hatL_iff_of_St {β M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hF : Formalism.L2.DIV.IsFrame β Λ) (hM : M ∈ Formalism.L2.DIV.St β) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hM
  have hint : ∀ v : GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ i j,
      (Formalism.L2.DIV.intGL F E n v).val i j ∈ Formalism.L2.Herm.intAf F E :=
    fun v i j => (v.val i j).2
  have e : (β⁻¹).val *ᵥ ((Formalism.L2.DIV.frGL β u).val *ᵥ x) =
      (Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x) := by
    have : Formalism.L2.DIV.frGL β u = β * Formalism.L2.DIV.intGL F E n u * β⁻¹ := rfl
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [hF, hF, e]
  constructor
  · intro hw i
    exact mulVec_mem_intAf _ (hint u) _ hw i
  · intro hw i
    have e2 : (β⁻¹).val *ᵥ x = (Formalism.L2.DIV.intGL F E n u⁻¹).val *ᵥ
          ((Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [e2]
    exact mulVec_mem_intAf _ (hint u⁻¹) _ hw i

end Frame

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem ofHAFin_eq (I : AutInst) (z : HAd I) :
    ofHAFin I z = ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
      (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply]
  induction (hmat I z i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem fmat_eq_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) : I.fmat x.2 =
      ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
        (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  rw [(hB x).2, hz, ofHAFin_eq]

theorem Lv_iff {D : D7} (z : Fin (D.sp.Y 0).rank → D.host.E) :
    z ∈ Formalism.L2.SG.InstExistsPf.Lv D ↔ z ∈ Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := by
  constructor
  · intro hz
    exact ⟨_, hz, (D.sp.Y 0).frame.equivFun.apply_symm_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    show (D.sp.Y 0).frame.equivFun.symm ((D.sp.Y 0).frame.equivFun w) ∈ (D.sp.Y 0).L0
    simpa using hw

theorem Lf_eq {D : D7} :
    @Eq (Submodule (Formalism.MainNotions.S.IntAf (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E)
      (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F]
        Formalism.MainNotions.S.Af (Formalism.L2.SG.InstExistsPf.instOf D).F))
      (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      (Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext w
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, (Lv_iff z).1 hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, (Lv_iff z).2 hz⟩, rfl⟩

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem conj_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β a M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hM : M ∈ Formalism.L2.DIV.St β) :
    a * M * a⁻¹ ∈ Formalism.L2.DIV.St (a * β) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨u, ?_⟩
  show a * β * Formalism.L2.DIV.intGL F E n u * (a * β)⁻¹ = a * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) * a⁻¹
  group

theorem iota_snd_mem_Kset {D : D7} (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (hF : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) (y : GA D (D.sp.Y 0))
    (hy : finE (D.sp.Y 0) y ∈ Formalism.L2.DIV.St β) :
    (Formalism.IndefR.RationalEmbedding.iota D y).2 ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset := by
  have hfm := fmat_eq_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) (Formalism.IndefR.RationalEmbedding.iota D y) y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y)
  intro x
  show x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
    ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D y).2) *ᵥ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
  rw [hfm, Lf_eq]
  exact mem_hatL_iff_of_St hF hy x

theorem castGA_snd_Kset {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.2 ∈ I.Kset) : (castGA h x).2 ∈ I'.Kset := by
  subst h; exact hx

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

theorem onto : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame γ
  obtain ⟨κ, hκf, hκp, hκr⟩ := GlobalTheory.LevelRowsObj.liftsExist hLev (cG.symm γ)
  set y : GA D (Yc D 0) := t * κ * t⁻¹ with hydef
  have hy : y ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hκf) ((GfC _).inv_mem ht)
  have h1 := real_one X h y hy
  have hy' : (iotaX X h).symm (1, (iotaX X h y).2) = y := by
    rw [← h1]; exact (iotaX X h).symm_apply_apply y
  refine ⟨(iotaX X h y).2, ?_, ?_⟩
  · have hS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
      rw [hydef, map_mul, map_mul, map_inv]
      exact conj_mem_St (Formalism.L2.DIV.parLev_St hκp)
    exact castGA_snd_Kset h.symm _ (iota_snd_mem_Kset _ hFrame y hS)
  · have hk : kap X h t (iotaX X h y).2 = κ := by
      unfold kap
      rw [hy']
      show (t⁻¹ * (t * κ * t⁻¹) * t : GA D (Yc D 0)) = κ
      group
    rw [hk, hκr, MulEquiv.apply_symm_apply]

end GlobalTheory.SeeMatchOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Wsub (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Submodule ℂ (X.B.H (X.pl.symm τ)) :=
  ((MP R).sm τ).map ((c τ).toLinearEquiv.toLinearMap)

theorem symm_mem_sm (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) (y : Wsub R X c τ) :
    (c τ).symm (y : X.B.H (X.pl.symm τ)) ∈ (MP R).sm τ := by
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 y.2
  have : (c τ).symm (y : X.B.H (X.pl.symm τ)) = w := by
    rw [← hwy]
    exact (c τ).symm_apply_apply w
  rw [this]
  exact hw

def vecOf (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) : (MP R).Vec :=
  fun τ => ⟨(c τ).symm (y τ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (y τ)⟩

def tensT {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (y : ∀ τ, X.B.H (X.pl.symm τ)) : X.B.Hs :=
  X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm y)


open Classical in
def evF (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : L2X X :=
  star (if hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
    then hm.toLp _ else 0)

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem tensT_inner {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a b : ∀ τ, X.B.H (X.pl.symm τ)) :
    ⟪tensT X a, tensT X b⟫_ℂ = ∏ τ, ⟪a τ, b τ⟫_ℂ := by
  unfold tensT
  rw [X.B.tens_spec.1]
  rw [← Equiv.prod_comp X.pl.symm]
  simp only [Equiv.piCongrLeft_apply_apply]

theorem tensT_dense {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    Dense (Submodule.span ℂ (Set.range (tensT X)) : Set X.B.Hs) := by
  have : Set.range (tensT X) = Set.range X.B.tens :=
    (Equiv.piCongrLeft X.B.H X.pl.symm).surjective.range_comp X.B.tens
  rw [this]
  exact X.B.tens_spec.2.2

theorem tensT_w {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    tensT X (fun τ => X.B.w (X.pl.symm τ)) = X.B.tens X.B.w := by
  unfold tensT
  congr 1
  have : (fun τ => X.B.w (X.pl.symm τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm X.B.w := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply]
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.RowEvalHH

namespace GlobalTheory.RowEvalHH

theorem Wsub_dense {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (τ : D.what₂.Tau) :
    Dense (Wsub R X c τ : Set (X.B.H (X.pl.symm τ))) := by
  unfold Wsub
  rw [Submodule.map_coe]
  exact (c τ).surjective.denseRange.dense_image (c τ).continuous (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense (MP R) τ)

end GlobalTheory.RowEvalHH
end
end

