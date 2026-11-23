module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem hJ_syn_syn {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ)
    (α' β' : Fin r → ℂ) (γ' : ℂ) (δ' : Fin k → ℂ) :
    hJ ε (syn e p z w T α β γ δ) (syn e p z w T α' β' γ' δ') =
      ∑ a, α' a * conj (β a) + ∑ a, β' a * conj (α a) + (-γ' / (T : ℂ)) * conj γ + ∑ j, δ' j * conj (δ j) := by
  rw [hJ_syn]
  have h1 : ∀ a, hJ ε (syn e p z w T α β γ δ) (e a) = conj (β a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_e F]
  have h2 : ∀ a, hJ ε (syn e p z w T α β γ δ) (p a) = conj (α a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_p F]
  have h3 : hJ ε (syn e p z w T α β γ δ) z = conj γ := by rw [UnitaryIsometries.hJ_conj, synthesized_vector_z_pairing F]
  have h4 : ∀ j, hJ ε (syn e p z w T α β γ δ) (w j) = conj (δ j) := fun j => by rw [UnitaryIsometries.hJ_conj, syn_w F]
  simp only [h1, h2, h3, h4]

def frL (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def frM (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (frL (ε := ε) e p z w y T)

theorem frM_apply (w y : Fin k → Fin n → ℂ) (v : Fin n → ℂ) :
    frM (ε := ε) e p z w y T *ᵥ v =
      syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  rw [frM, LinearMap.toMatrix'_mulVec]
  rfl

theorem frM_isIsom {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (Fy : Frm ε e p z y T)
    (hdim : n = 2 * r + 1 + k) : UnitaryIsometries.IsIsom ε (frM (ε := ε) e p z w y T) := by
  intro v v'
  rw [frM_apply, frM_apply, hJ_syn_syn Fy]
  conv_rhs => rw [recon Fw hdim v, recon Fw hdim v', hJ_syn_syn Fw]

theorem frM_fix {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {v : Fin n → ℂ}
    (hv : ∀ j, hJ ε (w j) v = 0) : frM (ε := ε) e p z w y T *ᵥ v = v := by
  rw [frM_apply]
  conv_rhs => rw [recon Fw hdim v]
  simp only [syn, hv, zero_smul, Finset.sum_const_zero]

theorem frM_w {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (j : Fin k) :
    frM (ε := ε) e p z w y T *ᵥ w j = y j := by
  rw [frM_apply]
  simp only [syn, Fw.pw, Fw.ew, Fw.zw, Fw.ww, zero_smul, Finset.sum_const_zero, zero_add, neg_zero, zero_div,
    ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem span_perp {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (a : ℕ) :
    ∀ x ∈ spanLt e a, ∀ j, hJ ε x (w j) = 0 := by
  intro x hx j
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact F.ew b j
  | zero => exact UnitaryIsometries.hJ_zero_left ε _
  | add x y _ _ hx hy => rw [UnitaryIsometries.hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [UnitaryIsometries.hJ_smul_left, hx, mul_zero]

theorem spanLt_le (a : ℕ) (h : a ≤ r) : spanLt e a ≤ spanLt e r := by
  unfold spanLt
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, b.2, rfl⟩

theorem mem_NH {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {s : UJ ε}
    (hs : s ∈ UnitaryIsometries.RI.SG ε e z) : ∃ m ∈ NG ε e z, ∃ h ∈ HG ε e p z, s = m * h := by
  set M := Formalism.MainNotions.S.uMat s with hM
  have hsi : s⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hs
  have hiso := UnitaryIsometries.isIsom_uMat ε s
  have hback : ∀ v : Fin n → ℂ, M *ᵥ (Formalism.MainNotions.S.uMat s⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hM, uMat_mul_inv, one_mulVec]
  have hMe : ∀ a j, hJ ε (e a) (M *ᵥ w j) = 0 := by
    intro a j
    rw [← hback (e a), hiso]
    have hx := hsi.1 a
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ e a = e a + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ e a := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.ew, span_perp Fw a.1 _ hx j, add_zero]
  have hMz : ∀ j, hJ ε z (M *ᵥ w j) = 0 := by
    intro j
    rw [← hback z, hiso]
    have hx := hsi.2
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ z = z + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.zw, span_perp Fw r _ hx j, add_zero]
  set y : Fin k → Fin n → ℂ := fun j => M *ᵥ w j - ∑ a, hJ ε (p a) (M *ᵥ w j) • e a with hy
  have hpe : ∀ a b, hJ ε (p a) (e b) = if b = a then 1 else 0 := fun a b => hJ_swapδ Fw.ep b a
  have hwe : ∀ j b, hJ ε (M *ᵥ w j) (e b) = 0 := fun j b => hJ_swap0 (hMe b j)
  have Fy : Frm ε e p z y T := by
    refine ⟨Fw.ee, Fw.ep, Fw.pp, Fw.ez, Fw.pz, Fw.zz, fun a j => ?_, fun a j => ?_, fun j => ?_, fun i j => ?_,
      Fw.T_ne⟩
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, Fw.ee, mul_zero, Finset.sum_const_zero, sub_zero, hMe]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hpe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · have hze : ∀ b, hJ ε z (e b) = 0 := fun b => hJ_swap0 (Fw.ez b)
      simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hze, mul_zero, Finset.sum_const_zero, sub_zero, hMz]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hwe, Fw.ee, hMe,
        mul_zero, Finset.sum_const_zero, sub_zero]
      rw [hM]
      exact (hiso _ _).trans (Fw.ww i j)
  have hI := frM_isIsom Fw Fy hdim
  set hU := UnitaryIsometries.toUJ ε hI with hUdef
  have hUm : Formalism.MainNotions.S.uMat hU = frM (ε := ε) e p z w y T := UnitaryIsometries.uMat_toUJ ε hI
  have hUe : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ e a = e a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.ew a j)
  have hUp : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ p a = p a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.pw a j)
  have hUz : Formalism.MainNotions.S.uMat hU *ᵥ z = z := by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.zw j)
  have hUH : hU ∈ HG ε e p z := ⟨hUe, hUp, hUz⟩
  have hUw : ∀ j, Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ y j = w j := fun j => by
    rw [← frM_w (y := y) Fw j, ← hUm, mulVec_mulVec, uMat_inv_mul, one_mulVec]
  refine ⟨s * hU⁻¹, ?_, hU, hUH, by group⟩
  have hmv : ∀ v, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ v = M *ᵥ (Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ v) - v := fun v => by
    rw [uMat_mul, Matrix.sub_mulVec, one_mulVec, ← mulVec_mulVec]
  have hme : ∀ a, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ e a = (M - 1) *ᵥ e a := fun a => by
    rw [hmv, inv_fix ε (hUe a), Matrix.sub_mulVec, one_mulVec]
  have hmz : (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ z = (M - 1) *ᵥ z := by
    rw [hmv, inv_fix ε hUz, Matrix.sub_mulVec, one_mulVec]
  have hmy : ∀ j, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ y j ∈ spanLt e r := fun j => by
    rw [hmv, hUw, hy, sub_sub_cancel]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)
  refine ⟨⟨fun a => ?_, ?_⟩, fun v hv => ?_⟩
  · rw [hme]; exact hs.1 a
  · rw [hmz]; exact hs.2
  · rw [recon Fy hdim v]
    simp only [syn, mulVec_add, mulVec_sum, mulVec_smul, hv, zero_smul, Finset.sum_const_zero, add_zero]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmy j))
    · rw [hme]; exact spanLt_le a.1 (le_of_lt a.2) (hs.1 a)
    · rw [hmz]; exact hs.2

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.GramEqOfHyp
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool)

def frm3 (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin r ⊕ (Fin r ⊕ Unit) → Fin n → ℂ :=
  Sum.elim e (Sum.elim f (fun _ => z))

structure Hyp (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z = -T

theorem Hyp.fe {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a b : Fin r) :
    hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  rw [hJ_conj, h.ef]; by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

theorem Hyp.ze {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (e a) = 0 := by rw [hJ_conj, h.ez, map_zero]

theorem Hyp.zf {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (f a) = 0 := by rw [hJ_conj, h.fz, map_zero]

theorem gram_eq_of_hyp {e f e' f' : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T : ℂ}
    (h : Hyp ε e f z T) (h' : Hyp ε e' f' z' T) (i j : Fin r ⊕ (Fin r ⊕ Unit)) :
    hJ ε (frm3 e f z i) (frm3 e f z j) = hJ ε (frm3 e' f' z' i) (frm3 e' f' z' j) := by
  rcases i with a | a | _ <;> rcases j with b | b | _ <;>
    simp only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz,
      h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]

theorem gram_nd_of_hyp {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (hT : T ≠ 0) (h : Hyp ε e f z T) :
    (Matrix.of fun i j => hJ ε (frm3 e f z i) (frm3 e f z j)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0 := fun i => by
    have := congrFun hw i
    simpa [mulVec, dotProduct] using this
  funext i
  rcases i with a | a | u
  · have := row (Sum.inr (Sum.inl a))
    simpa [Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz] using this
  · have := row (Sum.inl a)
    simpa [Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez] using this
  · have := row (Sum.inr (Sum.inr u))
    simp [Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this
    rcases this with h1 | h1
    · exact absurd h1 hT
    · simpa using h1

theorem coord_inj {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ (N : Fin (r + 1) → Fin n) (P : Fin (r + k) → Fin n), Function.Injective N ∧ Function.Injective P ∧
      (∀ y, ε (N y) = false) ∧ (∀ x, ε (P x) = true) := by
  set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN
  set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP
  have hcard : sP.card + sN.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => ε i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hP : sP.card = r + k := by omega
  let eN := sN.equivFinOfCardEq hsig
  let eP := sP.equivFinOfCardEq hP
  refine ⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp eN.symm.injective
  · exact Subtype.val_injective.comp eP.symm.injective
  · exact (Finset.mem_filter.1 (eN.symm y).2).2
  · exact (Finset.mem_filter.1 (eP.symm x).2).2

theorem complement {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1)
    {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T) (h : Hyp ε e f z (T : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      (∀ c a, hJ ε (e c) (w a) = 0) ∧ (∀ c a, hJ ε (f c) (w a) = 0) ∧ (∀ a, hJ ε z (w a) = 0) := by
  obtain ⟨N, P, hN, hP, hNs, hPs⟩ := coord_inj ε hdim hsig
  have hNP : ∀ y x, N y ≠ P x := fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this
  set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq
  have hsqc : conj sq = sq := Complex.conj_ofReal _
  have hsq2 : sq * sq = 1 / 2 := by
    rw [hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let p : Fin r → Fin n := fun c => P (Fin.castAdd k c)
  let q : Fin r → Fin n := fun c => N (Fin.castSucc c)
  let qz : Fin n := N (Fin.last r)
  let wi : Fin k → Fin n := fun j => P (Fin.natAdd r j)
  let e0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) + dl (q c))
  let f0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) - dl (q c))
  let z0 : Fin n → ℂ := ((Real.sqrt T : ℝ) : ℂ) • dl qz
  let w0 : Fin k → Fin n → ℂ := fun j => dl (wi j)
  have hp : Function.Injective p := hP.comp (Fin.castAdd_injective r k)
  have hq : Function.Injective q := hN.comp (Fin.castSucc_injective r)
  have hqz : ∀ c, q c ≠ qz := fun c h => Fin.castSucc_ne_last c (hN h)
  have hwi : Function.Injective wi := hP.comp (Fin.natAdd_injective k r)
  have hpw : ∀ c j, p c ≠ wi j := fun c j h => by
    have h1 := congrArg Fin.val (hP h)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  have hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := hJ_dl ε
  have pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [p, hPs]
    · rw [if_neg (hp.ne hab), if_neg hab]
  have qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [q, hNs]
    · rw [if_neg (hq.ne hab), if_neg hab]
  have pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _).symm]
  have qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _)]
  have h0 : Hyp ε e0 f0 z0 (T : ℂ) := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
    · simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · simp only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs
      · linear_combination 2 * hsq2
      · ring
    · simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
      have hq0 : ε qz = false := hNs _
      simp only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true,
        if_false]
      linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h)
    (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)
  have hiso := isIsom_uMat ε g
  have he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c := fun c => hg (Sum.inl c)
  have hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c := fun c => hg (Sum.inr (Sum.inl c))
  have hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z := hg (Sum.inr (Sum.inr ()))
  have ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0 := fun a b => by
    simp only [w0]; rw [hd]; by_cases hab : a = b
    · subst hab; simp [wi, hPs]
    · rw [if_neg (hwi.ne hab), if_neg hab]
  have pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]
  have qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  have zw : ∀ j, hJ ε (dl qz) (w0 j) = 0 := fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  refine ⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩
  · rw [← he, hiso]; simp only [e0, hJ_smul_left, hJ_add_left, pw, qw]; ring
  · rw [← hf, hiso]; simp only [f0, hJ_smul_left, hJ_sub_left, pw, qw]; ring
  · rw [← hz, hiso]; simp only [z0, hJ_smul_left, zw]; ring

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem lieE_G : Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL := by
  have h : Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = ((uH k r : Submodule ℝ (Mat k r)) : Set (Mat k r)) := BH.lieG k r
  unfold Formalism.MainNotions.S.lieE
  rw [h]
  change Submodule.span ℝ (⇑(RL (k := k) (r := r)) '' ↑(uH k r)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem lieG' : LieG := fun k r => lieE_G

theorem mulVec_bvec (X : Mat k r) (j i : Fin (2 * r + k + 1)) : (X *ᵥ bvec j) i = X i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]

theorem mid_or (j : Fin (2 * r + k + 1)) (h : ¬ Mid k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) := by
  simp only [Mid, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨2 * r + k - j, by omega⟩, Fin.ext ?_⟩
    have hj := j.isLt
    show (j : ℕ) = 2 * r + k - (2 * r + k - j)
    omega

private theorem mul_hpk_apply_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  rw [Matrix.mul_apply]
  simp_rw [Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row]
  rw [Finset.sum_eq_single (tau k r j)]
  · rw [tau_tau, if_pos rfl, sgn_tau]
  · intro m _ hm
    rw [if_neg (fun h => hm (by rw [h, tau_tau])), mul_zero]
  · simp

private theorem adjH_apply_lemma_2 (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Xᴴ * Hpk k r) i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  rw [mul_hpk_apply_lemma, Formalism.QuantumDeterminants.WeylGroupFacts.hpk_mul_apply, Matrix.conjTranspose_apply]

theorem lieWb_set : Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r : Set (Mat k r)) := by
  rw [BH.lieWb k r]
  ext X
  change _ ↔ (adjH X + X = 0 ∧ ∀ i j, ¬(Mid k r i ∧ Mid k r j) → X i j = 0)
  rw [adjH_def]
  constructor
  · rintro ⟨hX, hc⟩
    have hcol : ∀ i j, ¬ Mid k r j → X i j = 0 := by
      intro i j hj
      rcases mid_or j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [← mulVec_bvec X (eI k r a) i, (hc a).1]; rfl
      · rw [← mulVec_bvec X (esI k r a) i, (hc a).2]; rfl
    refine ⟨hX, fun i j hij => ?_⟩
    rcases not_and_or.1 hij with hi | hj
    · have h := congrFun (congrFun hX i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      rw [adjH_apply_lemma_2] at h
      have htau : ¬ Mid k r (tau k r i) := by
        have := tau_out i (by simp only [Mid, not_and_or, not_le] at hi; exact hi)
        simp only [Mid, not_and_or, not_le]; exact this
      rw [hcol _ _ htau, star_zero, mul_zero, zero_mul, zero_add] at h
      exact h
    · exact hcol i j hj
  · rintro ⟨hX, hz⟩
    refine ⟨hX, fun a => ⟨?_, ?_⟩⟩
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h1 : r ≤ (a : ℕ) := h.2.1
      have := a.isLt
      omega
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h2 : 2 * r + k - (a : ℕ) ≤ r + k := h.2.2
      have := a.isLt
      omega

theorem lieWb' : LieWb := by
  intro k r
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have h : Z ∈ Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) := by rw [lieWb_set]; exact hZ
    simpa using h 1
  · unfold Formalism.MainNotions.S.lieE
    rw [lieWb_set]
    have : (fun X => (WithLp.equiv 2 _).symm (Formalism.MainNotions.S.realifyFun X)) '' (uWb k r : Set (Mat k r)) =
        (RL : Mat k r → _) '' (uWb k r : Set (Mat k r)) := rfl
    rw [this, Submodule.span_image, Submodule.span_eq]

def prodEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_prodS {R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) [FiniteDimensional R p] [FiniteDimensional R q] :
    Module.finrank R ↥(p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

private theorem eq_zero_of_RL_lemma_3 (M : Mat k r) (h : ‖RL (k := k) (r := r) M‖ ^ 2 = 0) : M = 0 := by
  rw [RL_sq] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖M i j‖))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖M i j‖)).1 h1 j (Finset.mem_univ _)
  simpa using h2

theorem lm_inj {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (h : Lm k r v = 0) : v = 0 := by
  have hn := lm_norm hv
  rw [h, map_zero, norm_zero] at hn
  have h1 := sq_nonneg ‖RL (k := k) (r := r) v.1‖
  have h2 : 0 ≤ ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have h3 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.1‖
  have h4 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.2‖
  have e1 : ‖RL (k := k) (r := r) v.1‖ ^ 2 = 0 := by nlinarith
  have e2 : ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
  have e3 : ‖RL (k := k) (r := r) v.2.2.1‖ ^ 2 = 0 := by nlinarith
  have e4 : ‖RL (k := k) (r := r) v.2.2.2‖ ^ 2 = 0 := by nlinarith
  have hx : v.2.1 = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v.2.1 a‖)).1 e2 a (Finset.mem_univ _)
    simpa using this
  exact Prod.ext (eq_zero_of_RL_lemma_3 _ e1)
    (Prod.ext hx (Prod.ext (eq_zero_of_RL_lemma_3 _ e3) (eq_zero_of_RL_lemma_3 _ e4)))

def lmEquiv (k r : ℕ) : ↥(Vs k r) ≃ₗ[ℝ] ↥(uH k r) :=
  LinearEquiv.ofBijective ((Lm k r).toLinearMap.restrict fun v hv => lm_mem hv)
    ⟨fun a b hab => by
      have h : Lm k r (a.1 - b.1) = 0 := by
        have := congrArg Subtype.val hab
        simp only [LinearMap.restrict_apply] at this
        rw [map_sub]; exact sub_eq_zero.2 this
      exact Subtype.ext (sub_eq_zero.1 (lm_inj ((Vs k r).sub_mem a.2 b.2) h)),
     fun y => by
      obtain ⟨v, hv, hvy⟩ := lm_surj y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

theorem dimG : Formalism.L2.SG.Pf.BH.DimG := by
  intro k r
  have eG : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (UH (Hpk k r))) = Module.finrank ℝ ↥(uH k r) := by
    rw [lieE_G]; exact ((Submodule.equivMapOfInjective _ RL_injective (uH k r)).finrank_eq).symm
  have eN : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Nset k r)) = Module.finrank ℝ ↥(lieNS k r) := by
    rw [lieE_N]; exact ((Submodule.equivMapOfInjective _ RL_injective (lieNS k r)).finrank_eq).symm
  have eW : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) = Module.finrank ℝ ↥(uWb k r) := by
    rw [(lieWb' k r).2]; exact ((Submodule.equivMapOfInjective _ RL_injective (uWb k r)).finrank_eq).symm
  rw [eG, eN, eW, ← (lmEquiv k r).finrank_eq]
  unfold Vs
  rw [finrank_prodS, finrank_prodS, finrank_prodS, finrank_top, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Formalism.L2.SG.Pf.BH.Sw
end
end

