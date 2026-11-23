module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HFrame
section
noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3

variable {A : Type} [CommRing A] {r k : ℕ}

def IsW (s : Idx r k) : Prop := ∃ i : Fin k, s = Sum.inr (Sum.inl (Sum.inl i))

abbrev wI (i : Fin k) : Idx r k := Sum.inr (Sum.inl (Sum.inl i))

theorem hEmb_col_frame (B : Matrix (Fin k) (Fin k) A) (s : Idx r k) (hs : ¬ IsW s) (t : Idx r k) :
    hEmb r B t s = (1 : Matrix (Idx r k) (Idx r k) A) t s := by
  rcases s with s | ((s | s) | s)
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]
  · exact absurd ⟨s, rfl⟩ hs
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]

theorem hEmb_row_frame (B : Matrix (Fin k) (Fin k) A) (s : Idx r k) (hs : ¬ IsW s) (t : Idx r k) :
    hEmb r B s t = (1 : Matrix (Idx r k) (Idx r k) A) s t := by
  rcases s with s | ((s | s) | s)
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]
  · exact absurd ⟨s, rfl⟩ hs
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]
  · rcases t with t | ((t | t) | t) <;> simp [hEmb, midEmb, Matrix.one_apply]

theorem hEmb_ww (B : Matrix (Fin k) (Fin k) A) (i j : Fin k) : hEmb r B (wI i) (wI j) = B i j := by
  simp [hEmb, midEmb]

theorem eq_hEmb_of (M N : Matrix (Idx r k) (Idx r k) A) (hNM : N * M = 1)
    (hc : ∀ s, ¬ IsW s → ∀ t, M t s = (1 : Matrix (Idx r k) (Idx r k) A) t s)
    (hr : ∀ s, ¬ IsW s → ∀ t, N s t = (1 : Matrix (Idx r k) (Idx r k) A) s t) :
    M = hEmb r (fun i j => M (wI i) (wI j)) := by
  ext t s
  by_cases hs : IsW s
  · obtain ⟨j, rfl⟩ := hs
    by_cases ht : IsW t
    · obtain ⟨i, rfl⟩ := ht
      exact (hEmb_ww (fun i j => M (wI i) (wI j)) i j).symm
    · refine Eq.trans ?_ (hEmb_row_frame _ t ht _).symm
      have h1 := congrFun (congrFun hNM t) (wI j)
      rw [Matrix.mul_apply] at h1
      have h2 : ∑ x, N t x * M x (wI j) = M t (wI j) := by
        rw [Finset.sum_eq_single t]
        · rw [hr t ht t, Matrix.one_apply_eq, one_mul]
        · intro b _ hb
          rw [hr t ht b, Matrix.one_apply_ne (Ne.symm hb), zero_mul]
        · intro h; exact absurd (Finset.mem_univ t) h
      exact h2.symm.trans h1
  · exact (hc s hs t).trans (hEmb_col_frame _ s hs t).symm

theorem mem_range_hEmbGL_iff (M : GL (Idx r k) A) :
    M ∈ (hEmbGL (A := A) r k).range ↔
      (∀ s, ¬ IsW s → ∀ t, (M : Matrix (Idx r k) (Idx r k) A) t s = (1 : Matrix (Idx r k) (Idx r k) A) t s) ∧
      (∀ s, ¬ IsW s → ∀ t, ((M⁻¹ : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) s t =
        (1 : Matrix (Idx r k) (Idx r k) A) s t) := by
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨fun s hs t => hEmb_col_frame _ s hs t, fun s hs t => ?_⟩
    rw [← map_inv, hEmbGL_val]
    exact hEmb_row_frame _ s hs t
  · rintro ⟨hc, hr⟩
    set Mm : Matrix (Idx r k) (Idx r k) A := (M : Matrix (Idx r k) (Idx r k) A)
    set Nm : Matrix (Idx r k) (Idx r k) A := ((M⁻¹ : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A)
    have hNM : Nm * Mm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hMN : Mm * Nm = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

    have hcN : ∀ s, ¬ IsW s → ∀ t, Nm t s = (1 : Matrix (Idx r k) (Idx r k) A) t s := by
      intro s hs t
      have h1 := congrFun (congrFun hNM t) s
      rw [Matrix.mul_apply] at h1
      have h2 : ∑ x, Nm t x * Mm x s = Nm t s := by
        rw [Finset.sum_eq_single s]
        · rw [hc s hs s, Matrix.one_apply_eq, mul_one]
        · intro b _ hb
          rw [hc s hs b, Matrix.one_apply_ne hb, mul_zero]
        · intro h; exact absurd (Finset.mem_univ s) h
      exact h2.symm.trans h1

    have hrM : ∀ s, ¬ IsW s → ∀ t, Mm s t = (1 : Matrix (Idx r k) (Idx r k) A) s t := by
      intro s hs t
      have e := eq_hEmb_of Mm Nm hNM hc hr
      exact (congrFun (congrFun e s) t).trans (hEmb_row_frame _ s hs t)
    have eM := eq_hEmb_of Mm Nm hNM hc hr
    have eN := eq_hEmb_of Nm Mm hMN hcN hrM
    let B : Matrix (Fin k) (Fin k) A := fun i j => Mm (wI i) (wI j)
    let B' : Matrix (Fin k) (Fin k) A := fun i j => Nm (wI i) (wI j)
    have hBB' : B * B' = 1 := by
      apply MassDataIdxStIm.hEmb_inj (r := r)
      rw [← MassDataIdxStIm.hEmb_mul, MassDataIdxStIm.hEmb_one]
      show hEmb r (fun i j => Mm (wI i) (wI j)) * hEmb r (fun i j => Nm (wI i) (wI j)) = 1
      rw [← eM, ← eN, hMN]
    have hB'B : B' * B = 1 := by
      apply MassDataIdxStIm.hEmb_inj (r := r)
      rw [← MassDataIdxStIm.hEmb_mul, MassDataIdxStIm.hEmb_one]
      show hEmb r (fun i j => Nm (wI i) (wI j)) * hEmb r (fun i j => Mm (wI i) (wI j)) = 1
      rw [← eM, ← eN, hNM]
    refine ⟨⟨B, B', hBB', hB'B⟩, Units.ext ?_⟩
    rw [hEmbGL_val]
    exact eM.symm

section Field

variable {K : Type} [Field K] {r k : ℕ}

theorem col_unit_iff (M : Matrix (Idx r k) (Idx r k) K) (s : Idx r k) :
    M *ᵥ Pi.single s 1 = Pi.single s 1 ↔ ∀ t, M t s = (1 : Matrix (Idx r k) (Idx r k) K) t s := by
  rw [funext_iff]
  refine forall_congr' fun t => ?_
  by_cases h : t = s
  · subst h
    simp [mulVec, dotProduct, Pi.single_apply]
  · simp [mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, h]

theorem row_unit_iff (M : Matrix (Idx r k) (Idx r k) K) (s : Idx r k) :
    Mᵀ *ᵥ Pi.single s 1 = Pi.single s 1 ↔ ∀ t, M s t = (1 : Matrix (Idx r k) (Idx r k) K) s t := by
  rw [funext_iff]
  refine forall_congr' fun t => ?_
  by_cases h : t = s
  · subst h
    simp [mulVec, dotProduct, Pi.single_apply]
  · simp [mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, h, Ne.symm h]

theorem frame_fix_iff (g1 Q : GL (Idx r k) K) (g2 J1 : Matrix (Idx r k) (Idx r k) K) (hJ : IsUnit J1.det)
    (hU : g2ᵀ * J1 * (g1 : Matrix (Idx r k) (Idx r k) K) = J1)
    (y1 y2 : Idx r k → Idx r k → K) (dl : Idx r k → Idx r k) (l : Idx r k → K)
    (hl : ∀ s, ¬ IsW s → l s ≠ 0) (hdl : ∀ s, ¬ IsW s → ¬ IsW (dl s))
    (hdls : ∀ s, ¬ IsW s → ∃ s', ¬ IsW s' ∧ dl s' = s)
    (hy1 : ∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 s = Pi.single s 1)
    (hy2 : ∀ s, ¬ IsW s → (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ (J1ᵀ *ᵥ y2 s) = l s • Pi.single (dl s) 1) :
    (∀ s, ¬ IsW s → (g1 : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 s = y1 s ∧ g2 *ᵥ y2 s = y2 s) ↔
      Q⁻¹ * g1 * Q ∈ (hEmbGL (A := K) r k).range := by
  set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1
  set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i
  set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm
  set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi
  have e1 : G1 * G1i = 1 := by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ' : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJt : IsUnit J1ᵀ.det := by rw [Matrix.det_transpose]; exact hJ
  have eJ : J1ᵀ⁻¹ * J1ᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have eJ' : J1ᵀ * J1ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJt
  have hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ := by
    have hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ := by
      have := congrArg Matrix.transpose hU
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have hit : G1iᵀ * G1ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ * (G1ᵀ * J1ᵀ * g2) * J1ᵀ⁻¹ := by
          rw [← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]
      _ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]
  set Mm : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hMm
  have hM : Mm = Qi * G1 * Qm := by simp [hMm, hQi, hG1, hQm, Units.val_mul]
  have hMi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm := by
    have : (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q := by group
    rw [this]
    simp [hQi, hG1i, hQm, Units.val_mul]
  have hQQ : ∀ v : Idx r k → K, Qm *ᵥ (Qi *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, eQ, Matrix.one_mulVec]
  have hQQ' : ∀ v : Idx r k → K, Qi *ᵥ (Qm *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, eQ', Matrix.one_mulVec]

  have c1 : ∀ s, ¬ IsW s → (G1 *ᵥ y1 s = y1 s ↔ ∀ t, Mm t s = (1 : Matrix (Idx r k) (Idx r k) K) t s) := by
    intro s hs
    have hyQ : y1 s = Qm *ᵥ Pi.single s 1 := by rw [← hy1 s hs, hQQ]
    rw [← col_unit_iff, hM, hyQ]
    simp only [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      rw [h, hQQ']
    · intro h
      rw [← hQQ (G1 *ᵥ (Qm *ᵥ Pi.single s 1)), h]
  have eQt : Qiᵀ * Qmᵀ = 1 := by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]
  have eQt' : Qmᵀ * Qiᵀ = 1 := by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]
  have hTT : ∀ v : Idx r k → K, Qmᵀ *ᵥ (Qiᵀ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, eQt', Matrix.one_mulVec]
  have hTT' : ∀ v : Idx r k → K, Qiᵀ *ᵥ (Qmᵀ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, eQt, Matrix.one_mulVec]

  have c2 : ∀ s, ¬ IsW s → (g2 *ᵥ y2 s = y2 s ↔
      ∀ t, (Qi * G1i * Qm) (dl s) t = (1 : Matrix (Idx r k) (Idx r k) K) (dl s) t) := by
    intro s hs
    rw [← row_unit_iff]
    have hls := hl s hs
    have step1 : g2 *ᵥ y2 s = y2 s ↔ G1iᵀ *ᵥ (J1ᵀ *ᵥ y2 s) = J1ᵀ *ᵥ y2 s := by
      rw [← hT]
      simp only [← Matrix.mulVec_mulVec]
      have hJJ : ∀ v : Idx r k → K, J1ᵀ⁻¹ *ᵥ (J1ᵀ *ᵥ v) = v := fun v => by
        rw [Matrix.mulVec_mulVec, eJ, Matrix.one_mulVec]
      rw [hJJ]
      constructor
      · intro h; rw [h]
      · intro h
        have := congrArg (fun v => J1ᵀ⁻¹ *ᵥ v) h
        simp only [hJJ] at this
        exact this
    rw [step1]
    set u : Idx r k → K := Pi.single (dl s) 1 with hu
    have hw : J1ᵀ *ᵥ y2 s = Qiᵀ *ᵥ (l s • u) := by rw [← hy2 s hs, hTT']
    have eqT : (Qi * G1i * Qm)ᵀ = Qmᵀ * G1iᵀ * Qiᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [eqT, hw]
    simp only [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have h2 : Qmᵀ *ᵥ (G1iᵀ *ᵥ (Qiᵀ *ᵥ (l s • u))) = l s • u := by rw [h, hTT]
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul] at h2
      exact smul_right_injective _ hls h2
    · intro h
      calc G1iᵀ *ᵥ (Qiᵀ *ᵥ (l s • u)) = Qiᵀ *ᵥ (Qmᵀ *ᵥ (G1iᵀ *ᵥ (Qiᵀ *ᵥ (l s • u)))) := by rw [hTT']
        _ = Qiᵀ *ᵥ (l s • u) := by
          simp only [Matrix.mulVec_smul, h]
  rw [mem_range_hEmbGL_iff, hMi]
  constructor
  · intro h
    refine ⟨fun s hs => (c1 s hs).1 (h s hs).1, fun s hs => ?_⟩
    obtain ⟨s', hs', rfl⟩ := hdls s hs
    exact (c2 s' hs').1 (h s' hs').2
  · rintro ⟨h1, h2⟩ s hs
    exact ⟨(c1 s hs).2 (h1 s hs), (c2 s hs).2 (h2 (dl s) (hdl s hs))⟩

end Field

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelComponentsSurjective
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem mem_stabT_of_comp (I : Formalism.MainNotions.S.AutInst) (h : HA (Af I.F) I.cm.sig I.J) {a : ℕ}
    (X0 : Fin a → Fin I.n → I.E)
    (hc : ∀ v, PI.MassDataKppVolLemmas.piV I v h ∈ stabT (Fv I.F v) I.cm.sig I.J X0) :
    h ∈ stabT (Af I.F) I.cm.sig I.J X0 := by
  rw [mem_stabT]
  intro b
  funext i
  rw [← sub_eq_zero]
  apply PI.MassDataKppVolLemmas.LocIdxLift_inj I
  intro v
  have hv := hc v
  rw [mem_stabT] at hv
  have e1 : ratV (F := I.F) (Fv I.F v) (X0 b) =
      (PI.MassDataKppVolLemmas.tV I v) ∘ ratV (F := I.F) (Af I.F) (X0 b) := by
    funext j
    simp [ratV, PI.MassDataKppVolLemmas.tV, tensMap_inclR]
  have h2 := congrFun (hv b) i
  rw [map_sub]
  show PI.MassDataKppVolLemmas.tV I v ((((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) *ᵥ ratV (F := I.F) (Af I.F) (X0 b)) i) -
    PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = 0
  rw [RingHom.map_mulVec, ← e1]
  have e2 : ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (PI.MassDataKppVolLemmas.tV I v) =
      ((HA.mat (Fv I.F v) I.cm.sig I.J (PI.MassDataKppVolLemmas.piV I v h) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) := rfl
  rw [e2]
  have e3 : PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = ratV (F := I.F) (Fv I.F v) (X0 b) i := by
    rw [e1]; rfl
  rw [e3, sub_eq_zero]
  exact h2

variable {D : D7}

theorem level_components_surjective : SurjH := by
  classical
  intro D X hb _hK u _hT _hL f
  have key : ∀ S : Finset (TypX X), ∃ z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
      z ∈ KHg X u ∧ ∀ p : TypX X, ((piH X u p.1 z : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        if p ∈ S then (((f p : KvH X u p.1) : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hzK, hz⟩ := ih
      set k : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J :=
        (((f q : KvH X u q.1) : Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) with hk
      have hkK : k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := (f q).2
      have hkH : k ∈ Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (f q : KvH X u q.1).1.2
      obtain ⟨h, hKf, hq1, hq2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I q.1 k hkK
      have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
        apply mem_stabT_of_comp X.B.I h
        intro v
        by_cases hv : v = q.1
        · subst hv; rw [hq1]; exact hkH
        · rw [hq2 v hv]; exact one_mem _
      refine ⟨⟨h, hH⟩ * z, ?_, fun p => ?_⟩
      · show (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
          Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
        exact mul_mem hKf hzK
      · rw [map_mul, Subgroup.coe_mul, hz p]
        show PI.MassDataKppVolLemmas.piV X.B.I p.1 h * _ = _
        by_cases hpq : p = q
        · subst hpq
          rw [if_neg hq, if_pos (Finset.mem_insert_self p S), mul_one, hq1]
        · have hp1 : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
          rw [hq2 p.1 hp1, one_mul]
          by_cases hpS : p ∈ S
          · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
          · rw [if_neg hpS, if_neg]
            intro hm
            rcases Finset.mem_insert.1 hm with e | e
            · exact hpq e
            · exact hpS e
  obtain ⟨z, hzK, hz⟩ := key Finset.univ
  refine ⟨z, hzK, fun p => Subtype.ext (Subtype.ext ?_)⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

end PIW.MassDataColumns
end
end

