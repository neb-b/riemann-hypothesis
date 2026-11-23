module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0037
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfB
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem dl_full {r : ℕ} (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  simp [Fin.castLE_rfl]

def Iso' {r : ℕ} (H : HermSp M V) (f' : Fin (r + 1) → V) : Prop :=
  ∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f' a) (f' b) = 0

theorem mem_perp_X {r : ℕ} (f' : Fin (r + 1) → V) {x : V} (hx : ∀ i : Fin r, H.h x (f' i.castSucc) = 0) :
    x ∈ H.perp (H.X f') := fun y hy => h_right_zero hx hy

theorem X_le_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : H.X f' ≤ H.perp (H.X f') := by
  unfold HermSp.X
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact mem_perp_X f' (fun i => hK _ _ (Or.inl (Fin.castSucc_lt_last a).ne))

theorem z_mem_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : f' (Fin.last r) ∈ H.perp (H.X f') := mem_perp_X f' (fun i => hK _ _ (Or.inr (Fin.castSucc_lt_last i).ne))

theorem om_mem_perp {r : ℕ} (f f' : Fin (r + 1) → V) : H.om f f' ∈ H.perp (H.X f') := by
  apply mem_perp_X
  intro i
  unfold HermSp.om
  rw [Formalism.L2.SG.CntLocal.h_sum_left]
  have e : ∀ a, H.h (M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a) • f a) (f' i.castSucc) =
      M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc) := by
    intro a
    rw [H.h_smul_left, H.h_herm (f' i.castSucc) (f a), map_mul]
    rfl
  simp only [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have h2 : ∑ a, (H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc =
      ((H.Zhat f f').adjugate * H.Zhat f f') (Fin.last r) i.castSucc := (Matrix.mul_apply ..).symm
  rw [h2, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne',
    smul_zero, map_zero]

theorem w_zero_le_perp_first {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f) := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_left (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem w_zero_le_perp_second {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f') := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_right (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem Xp_le_span {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Xp f ⊔ H.Xp f' ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply sup_le
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inl a, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inr a, rfl⟩

theorem X_le_span {r : ℕ} (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨Sum.inl a.castSucc, rfl⟩

theorem decomp_perp {r : ℕ} (t : Term V M r) (hN : GramInvE H (Sum.elim t.f t.f'))
    (hD : IsUnit (H.Zhat t.f t.f').det) (hK : Iso' H t.f') {x : V} (hx : x ∈ H.perp (H.X t.f')) :
    ∃ (w : V) (μ c : E) (xX : V), w ∈ H.W0 t.f t.f' ∧ xX ∈ H.X t.f' ∧
      x = w + μ • H.om t.f t.f' + xX + c • t.f' (Fin.last r) := by
  obtain ⟨c, hc⟩ := decompE hN x
  set w := x - ∑ k, c k • Sum.elim t.f t.f' k with hwdef
  have hwW : w ∈ H.W0 t.f t.f' := fun y hy => h_right_zero hc (Xp_le_span t.f t.f' hy)
  set y : V := ∑ a, c (Sum.inl a) • t.f a with hy
  set xX : V := ∑ i : Fin r, c (Sum.inr i.castSucc) • t.f' i.castSucc with hxX
  have hxXm : xX ∈ H.X t.f' :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsplit : ∑ k, c k • Sum.elim t.f t.f' k = y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_castSucc (fun b => c (Sum.inr b) • t.f' b)]
    abel
  have hx' : x = w + y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [hwdef, hsplit]; abel
  have hyo : ∀ b, b ≠ Fin.last r → H.h y (t.f' b) = 0 := by
    intro b hb
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hb
    have hyv : y = x - w - xX - c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by rw [hx']; abel
    have e1 : H.h x (t.f' i.castSucc) = 0 := hx _ (Submodule.subset_span ⟨i, rfl⟩)
    have e2 : H.h w (t.f' i.castSucc) = 0 := hc (Sum.inr i.castSucc)
    have e3 : H.h xX (t.f' i.castSucc) = 0 := X_le_perp hK hxXm _ (Submodule.subset_span ⟨i, rfl⟩)
    have e4 : H.h (t.f' (Fin.last r)) (t.f' i.castSucc) = 0 := hK _ _ (Or.inr (Fin.castSucc_ne_last i))
    rw [hyv, ← hL_apply]
    simp only [map_sub, map_smul, hL_apply, e1, e2, e3, e4, smul_zero, sub_zero]
  have hyom := y_eq_om t.f t.f' (fun a => c (Sum.inl a)) hyo
  have hu : IsUnit (M.L.cj (H.Zhat t.f t.f').det) := hD.map M.L.cj
  refine ⟨w, ((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r)), c (Sum.inr (Fin.last r)), xX, hwW, hxXm, ?_⟩
  have hy2 : y = (((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r))) • H.om t.f t.f' := by
    rw [mul_smul, ← hyom, smul_smul, hu.val_inv_mul, one_smul]
  rw [hx', ← hy2]

theorem psi_unique {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (ψ ψ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hN1 : GramInvE H (Sum.elim t₁.f t₁.f')) (hN2 : GramInvE H (Sum.elim t₂.f t₂.f'))
    (hD1 : IsUnit (H.Zhat t₁.f t₁.f').det) (hD2 : IsUnit (H.Zhat t₂.f t₂.f').det)
    (hK1 : Iso' H t₁.f') (hK2 : Iso' H t₂.f')
    (hI : H.Ident t₁ t₂ φ ψ) (hI' : H.Ident t₁ t₂ φ ψ')
    (hz : H.SendsTo ψ.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r)))
    (hz' : H.SendsTo ψ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r))) : ψ = ψ' := by

  have gW : ∀ (w : V) (hw : w ∈ H.W0 t₁.f t₁.f'),
      ψ (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) = ψ' (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) := by
    intro w hw
    obtain ⟨w₂, hw₂, hφ1, hψ1⟩ := hI.2.2.1 w hw
    obtain ⟨w₂', hw₂', hφ2, hψ2⟩ := hI'.2.2.1 w hw
    have e1 := hφ1 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ rfl rfl
    have e2 := hφ2 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    have e12 : H.mkW t₂.f ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ = H.mkW t₂.f ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ := by
      rw [← e1, ← e2]
    have hsub : w₂ - w₂' ∈ H.X t₂.f := by
      have h := (Submodule.Quotient.eq _).1 e12
      simpa using h
    have hz0 : w₂ - w₂' = 0 := by
      refine eqz hN2 (X_le_span _ _ hsub) fun k => ?_
      have hk : Sum.elim t₂.f t₂.f' k ∈ H.Xp t₂.f ⊔ H.Xp t₂.f' := by
        cases k with
        | inl a => exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
        | inr b => exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
      exact (H.W0 t₂.f t₂.f').sub_mem hw₂ hw₂' _ hk
    have hww : w₂ = w₂' := sub_eq_zero.1 hz0
    have f1 := hψ1 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂, w_zero_le_perp_second _ _ hw₂⟩ rfl rfl
    have f2 := hψ2 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂', w_zero_le_perp_second _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at f1 f2
    subst hww
    exact f1.trans f2.symm

  have gom : ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) = ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
    have e1 := hI.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have e2 := hI'.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have hu : IsUnit (M.L.cj (H.Dl t₂.f t₂.f' (r + 1))) := by rw [dl_full]; exact hD2.map M.L.cj
    have e3 : M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
        M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
      have a1 : ψ.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      have a2 : ψ'.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      rw [← a1, ← a2, e1, e2]
    have e4 := congrArg (fun q => ((hu.unit⁻¹ : Eˣ) : E) • q) e3
    simp only [smul_smul] at e4
    rwa [hu.val_inv_mul, one_smul, one_smul] at e4

  have gz : ψ (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) =
      ψ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) := by
    have e1 := hz ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    have e2 := hz' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    exact e1.trans e2.symm
  apply LinearEquiv.ext
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨w, μ, c, xX, hw, hxX, hdec⟩ := decomp_perp t₁ hN1 hD1 hK1 hx
  have hq : (⟨x, hx⟩ : H.perp (H.X t₁.f')) = ⟨w, w_zero_le_perp_second _ _ hw⟩ + μ • ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ +
      ⟨xX, X_le_perp hK1 hxX⟩ + c • ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ := Subtype.ext hdec
  have h0 : H.mkW t₁.f' ⟨xX, X_le_perp hK1 hxX⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxX
  show ψ (H.mkW t₁.f' ⟨x, hx⟩) = ψ' (H.mkW t₁.f' ⟨x, hx⟩)
  rw [hq, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, h0, add_zero]
  simp only [map_add (f := _), map_smul]
  rw [gW w hw, gom, gz]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GramMMUnitOfTerm
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem hR_add (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm z x]

theorem hR_smul (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem hR_zero (x : V) : H.h x 0 = 0 := by
  have h0 : H.h 0 x = 0 := by
    have h1 := H.h_smul_left 0 0 x
    rwa [zero_smul, zero_mul] at h1
  rw [H.h_herm 0 x, h0, map_zero]

theorem hR_sub (x y z : V) : H.h x (y - z) = H.h x y - H.h x z := by
  rw [sub_eq_add_neg, ← neg_one_smul E z, hR_add, hR_smul, map_neg, map_one]
  ring

theorem q_ne (g : SplitG M.L) : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem q_mem_O (g : SplitG M.L) : algebraMap F E (g.q : F) ∈ M.L.O := by
  rw [M.L.O_def]
  have h1 : algebraMap F E (g.q : F) = algebraMap 𝒪[F] E g.q := (IsScalarTower.algebraMap_apply 𝒪[F] F E g.q).symm
  rw [h1]
  exact isIntegral_algebraMap

theorem cj_q (g : SplitG M.L) : M.L.cj (algebraMap F E (g.q : F)) = algebraMap F E (g.q : F) :=
  M.L.cj.commutes _

theorem gramMM_unit_of_term (t : Term V M r) (hT : H.IsTerm t) : IsUnit (H.gram (H.MMfam t)).det := by
  have hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T := ⟨hT.2.1.2.1, hT.2.1.2.2.1⟩
  have hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' := ⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩
  have hD : IsUnit (H.Dl t.f t.f' (r + 1)) := hT.2.2.2.1
  have hG : IsUnit (H.Gdet t.f t.f' t.T t.T') := isUnit_Gdet H _ _ _ _ hT.2.2.2.2.1
  obtain ⟨s, hs, hdet⟩ := gram_det H t.f t.f' t.T t.T' hF hF' hD
  have hgu : IsUnit (H.gram (Sum.elim t.f t.f')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim t.f t.f')).det = H.Gdet t.f t.f' t.T t.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) (q_ne g))⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) = fun j => ∑ i, A i j • Sum.elim t.f t.f' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

theorem exists_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hG : IsUnit (H.gram v).det)
    (d : ι → E) : ∃ u ∈ Submodule.span E (Set.range v), ∀ i, H.h u (v i) = d i := by
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V), H.h (∑ j ∈ s, c j • v j) y = ∑ j ∈ s, c j * H.h (v j) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [H.h_zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, H.h_add_left, H.h_smul_left, ih]
  refine ⟨∑ j, ((H.gram v)⁻¹ *ᵥ d) j • v j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), fun i => ?_⟩
  rw [hsum]
  have h1 : (H.gram v *ᵥ ((H.gram v)⁻¹ *ᵥ d)) i = d i := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mem_MMsharp_of (t : Term V M r) {u : V} (hu : u ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hd : ∀ i, H.h u (H.MMfam t i) ∈ M.L.O) : u ∈ MMsharp H t := by
  have hcj : ∀ c ∈ M.L.O, M.L.cj c ∈ M.L.O := by
    intro c hc
    rw [M.L.O_def] at hc ⊢
    exact hc.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  refine ⟨hu, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hd i
  | zero =>
    rw [hR_zero]
    exact M.L.O.zero_mem
  | add a b _ _ ha hb =>
    rw [hR_add]
    exact M.L.O.add_mem ha hb
  | smul c x _ hx =>
    rw [Subring.smul_def, hR_smul]
    exact M.L.O.mul_mem (hcj c c.2) hx

theorem MMfam_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  simp only [Formalism.MainNotions.S.Loc.HermSp.MMfam, hs]

theorem f'_eq_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (a : Fin (r + 1)) :
    t.f' a = t.f a + algebraMap F E (g.q : F) • H.MMfam t (Sum.inr a) := by
  rw [MMfam_G H g hs t, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ (q_ne g), map_one, one_smul,
    add_sub_cancel]

theorem smul_mem_lat (g : SplitG M.L) (abelian₂ : Submodule M.L.O V) {x : V} (hx : x ∈ abelian₂) :
    algebraMap F E (g.q : F) • x ∈ abelian₂ := by
  have h1 := abelian₂.smul_mem (⟨algebraMap F E (g.q : F), q_mem_O g⟩ : M.L.O) hx
  exact h1

theorem iota_fst_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x : V} (hx : x ∈ t.abelian₂)
    (hxp : x ∈ H.perp (H.X t.f)) :
    ∃ x' ∈ t.abelian₂, x' ∈ H.perp (H.X t.f') ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x).1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x - c • ((u : V) + w), t.abelian₂.sub_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x (t.f j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hwy : H.h (w : V) (H.MMfam t (Sum.inr j.castSucc)) = 0 := hermitian_W0_span_zero H t w.2 hyM
    have hu1 : H.h u (t.f j.castSucc) = H.h x (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hu2 : H.h u (H.MMfam t (Sum.inr j.castSucc)) = 0 := hud (Sum.inr j.castSucc)
    rw [f'_eq_G H g hs t, h_sub_left, H.h_smul_left, hR_add, hR_add, hR_smul, hR_smul, H.h_add_left,
      H.h_add_left, hxf, hwf, hwy, hu1, hu2, cj_q]
    ring
  · rw [sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem iota_snd_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x' : V} (hx : x' ∈ t.abelian₂)
    (hxp : x' ∈ H.perp (H.X t.f')) :
    ∃ x ∈ t.abelian₂, x ∈ H.perp (H.X t.f) ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x' (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x').1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x' + c • ((u : V) + w), t.abelian₂.add_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x' (t.f' j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hu1 : H.h u (t.f j.castSucc) = H.h x' (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hxf2 : H.h x' (t.f j.castSucc) = - (c * H.h x' (H.MMfam t (Sum.inr j.castSucc))) := by
      have e := f'_eq_G H g hs t j.castSucc
      have : t.f j.castSucc = t.f' j.castSucc - c • H.MMfam t (Sum.inr j.castSucc) := by rw [e]; abel
      rw [this, hR_sub, hR_smul, hxf, cj_q]
      ring
    rw [H.h_add_left, H.h_smul_left, H.h_add_left, hxf2, hwf, hu1]
    ring
  · rw [add_sub_cancel_left]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem Lset_eq_snd (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f = Prod.snd '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hx'p, hd⟩ := iota_fst_of H hM g hs t hg hU hx x.2
    exact ⟨_, ⟨⟨x', hx'p⟩, x, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, -, hx, -, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem Lset_eq_fst (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f' = Prod.fst '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x', hx', rfl⟩
    obtain ⟨x, hx, hxp, hd⟩ := iota_snd_of H hM g hs t hg hU hx' x'.2
    exact ⟨_, ⟨x', ⟨x, hxp⟩, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, hx', -, -, rfl⟩, rfl⟩
    exact ⟨x', hx', rfl⟩

end RG1

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LiftPhaseAgreement
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LiftedPhaseAgreement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem liftAtSomeC_holds : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ := by
  intro R ρ s hs
  have hA := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    simp [Formalism.L2.SG.TermOp.Gt, Formalism.L2.SG.TermOp.GTerm.G, h]
  exact hA hG hs

theorem phaseTieC_holds (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.PhaseLiftCell.phaseAgreement_of_lift X Y u u' κ (liftAtSomeC_holds X Y u u' κ)
    (Formalism.L2.SG.Pf.FinitePhaseConjugation.finPhaseC_of (hNR := Formalism.L2.SG.Pf.normRepExists_of
      (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hP) (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u))
      (h1 := liftAtSomeC_holds X Y u u' κ))

end Formalism.L2.SG.Pf.LiftedPhaseAgreement
end
end

