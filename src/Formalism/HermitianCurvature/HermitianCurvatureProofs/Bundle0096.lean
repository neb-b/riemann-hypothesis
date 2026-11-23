module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatExtMulVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterProductMatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConnectionRaisingConstantEq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart
section
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

section lev

variable {k : ℕ}

theorem castV_mulVec' {a b : ℕ} (h : a = b) (M : B.Mat k a) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h (M *ᵥ v) = D.castM h M *ᵥ D.castV h v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]

theorem zL_lift {o ρ r : ℕ} (h : o + ρ = r) (v : Fin (2 * ρ + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (D.castV h (liftVec k o ρ v)) = v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]
  funext i
  have := Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_levPos_gen (k := k) o ρ v i
  simpa [Formalism.FourierDecayAlt.P.Dx2.Tower.zL, levPos] using this

theorem zL_smul {o ρ r : ℕ} (h : o + ρ = r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (c • v) = c • Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v := by
  funext i; simp [Formalism.FourierDecayAlt.P.Dx2.Tower.zL]

theorem hermitian_form_anisotropic_part {m : ℕ} (v w : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) (hw : inWb k m w) :
    herm (Hpk k m) v w = herm (Hb k) (wbPart k m v) (wbPart k m w) := by
  have := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m w)
  rwa [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hw] at this

theorem herm_zL {o ρ r : ℕ} (h : o + ρ = r) (v w : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k ρ) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h w) = herm (Hpk k r) v w := by
  rw [hermitian_form_anisotropic_part _ _ (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h v hv) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h w hw),
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, hermitian_form_anisotropic_part v w hv hw]

theorem inWb_last {r : ℕ} (v : Fin (2 * (r - r) + k + 1) → ℂ) : inWb k (r - r) v := by
  intro i hi; exfalso; have := i.isLt; omega

theorem inWb_liftLast {r : ℕ} (h : r + (r - r) = r) (v : Fin (2 * (r - r) + k + 1) → ℂ) :
    inWb k r (D.castV h (liftVec k r (r - r) v)) := by
  intro i hi
  simp only [D.castV]
  apply Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_out_gen
  simp only [Fin.val_cast]
  omega

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nuR (p : KB.Pl P Wp Wq) : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) (by omega) p.ν'

def m0R (p : KB.Pl P Wp Wq) : B.Mat P.k (P.r - P.r) :=
  fun i j => p.m₀ ⟨i.val + P.r, by have := i.isLt; omega⟩ ⟨j.val + P.r, by have := j.isLt; omega⟩

theorem base_point_block_eq (p : KB.Pl P Wp Wq) :
    D.castM (by omega : P.r + (P.r - P.r) = P.r) (ιLev P.k P.r (P.r - P.r) (m0R p)) = p.m₀ := by
  obtain ⟨-, -, -, ⟨hmU, hmfix⟩, -⟩ := p.hF
  have hme : ∀ a : Fin P.r, p.m₀ *ᵥ ee P.k P.r a = ee P.k P.r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin P.r, p.m₀ *ᵥ es P.k P.r a = es P.k P.r a := fun a => (hmfix a a.isLt).2
  have hcol : ∀ (i j : Fin (2 * P.r + P.k + 1)), (j.val < P.r ∨ P.r + P.k < j.val) →
      p.m₀ i j = if i = j then 1 else 0 := by
    intro i j hj
    rcases hj with hj | hj
    · have e : bvec j = ee P.k P.r ⟨j.val, hj⟩ := by simp [ee, eI]
      have := congrFun (hme ⟨j.val, hj⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
    · have hj2 := j.isLt
      have e : bvec j = es P.k P.r ⟨2 * P.r + P.k - j.val, by omega⟩ := by
        simp only [es, esI]; congr 1; ext; simp; omega
      have := congrFun (hms ⟨2 * P.r + P.k - j.val, by omega⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
  have hrow : ∀ (i j : Fin (2 * P.r + P.k + 1)), (i.val < P.r ∨ P.r + P.k < i.val) →
      (P.r ≤ j.val ∧ j.val ≤ P.r + P.k) → p.m₀ i j = 0 := by
    intro i j hi hj
    have hmj : (p.m₀ *ᵥ bvec j) i = p.m₀ i j := by
      simp [mulVec, dotProduct, bvec, Pi.single_apply]
    rcases hi with hi | hi
    · have h1 := herm_es (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨i.val, hi⟩
      rw [← hms ⟨i.val, hi⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_es] at h1
      have hi' : eI P.k P.r ⟨i.val, hi⟩ = i := by ext; simp [eI]
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
    · have hi2 := i.isLt
      have h1 := herm_ee (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨2 * P.r + P.k - i.val, by omega⟩
      rw [← hme ⟨2 * P.r + P.k - i.val, by omega⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_ee] at h1
      have hi' : esI P.k P.r ⟨2 * P.r + P.k - i.val, by omega⟩ = i := by ext; simp [esI]; omega
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
  ext i j
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold ιLev
  by_cases hi : P.r ≤ i.val ∧ i.val ≤ P.r + P.k <;> by_cases hj : P.r ≤ j.val ∧ j.val ≤ P.r + P.k
  · rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    simp only [m0R]
    congr 1 <;> ext <;> simp <;> omega
  · rw [dite_eq_left (by simp; omega), dite_eq_right (by simp; omega), hcol i j (by omega)]
    rw [if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [dite_eq_right (by simp; omega)]
    rw [hrow i j (by omega) hj, if_neg]
    · intro h; apply hi; have := congrArg Fin.val h; simp at this; omega
  · rw [dite_eq_right (by simp; omega), hcol i j (by omega)]
    congr 1
    apply propext; constructor
    · intro h; ext; have := congrArg Fin.val h; simpa using this
    · intro h; subst h; rfl

theorem levFrame_nuR (p : KB.Pl P Wp Wq) : LevFrame p (nuR p) (m0R p) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := p.hF
  have h : P.r + (P.r - P.r) = P.r := by omega
  have hZ : (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z := by
    show (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z
    rw [← p.T.z_lev P.r le_rfl, zL_lift]
  have hZ' : (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z' := by
    show (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z'
    rw [← p.T.z'_lev P.r le_rfl, zL_lift]
  have hz := p.T.base.z_mem
  have hz' := p.T.base.z'_mem
  have hblk := base_point_block_eq p

  set Lf : (Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) → (Fin (2 * P.r + P.k + 1) → ℂ) :=
    fun v => D.castV h (liftVec P.k P.r (P.r - P.r) v) with hLf
  have hLm : ∀ v, Lf (m0R p *ᵥ v) = p.m₀ *ᵥ Lf v := by
    intro v
    simp only [hLf]
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mulVec_lift, castV_mulVec', hblk]
  have hLh : ∀ v w, herm (Hpk P.k (P.r - P.r)) v w = herm (Hpk P.k P.r) (Lf v) (Lf w) := by
    intro v w
    rw [← herm_zL h (Lf v) (Lf w) (inWb_liftLast h v) (inWb_liftLast h w), zL_lift, zL_lift]
  refine ⟨Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h p.ν' hν, hblk, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact inWb_last _
  · rw [hZ', nuR, herm_zL h _ _ hν hz', hνz]
  · rw [nuR, herm_zL h _ _ hν hν, hνν]
  · apply B2x4.mem_UH_of_herm
    intro x y
    rw [hLh, hLh x y, hLm, hLm, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]
  · intro a _; exact absurd a.isLt (by omega)
  · have e1 : m0R p *ᵥ (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.m₀ *ᵥ p.T.base.z') := by
      have := congrArg (Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h) (hLm (p.T.bs P.r).z')
      rw [zL_lift] at this
      rw [this, hZ']
      simp only [hLf]
      rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h _ hz']
    rw [e1, hmz, zL_smul, ← hZ, hZ', hZ, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz,
      Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz']

end place

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem levFrameExists_statement : PBI.LevFrameExists := by
  intro Wp Wq _ _ _ _ _ _ P p
  exact ⟨PBI.nuR p, PBI.m0R p, PBI.levFrame_nuR p⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMOfCont
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def MeasM (A : X → Matrix (Fin n) (Fin n) ℂ) : Prop := Measurable fun x => (Matrix.of.symm (A x) : Fin n → Fin n → ℂ)

theorem measM_iff {A : X → Matrix (Fin n) (Fin n) ℂ} : MeasM A ↔ ∀ i j, Measurable fun x => A x i j := by
  simp only [MeasM, measurable_pi_iff]
  exact Iff.rfl

theorem measM_const (C : Matrix (Fin n) (Fin n) ℂ) : MeasM (fun _ : X => C) := measurable_const

theorem measM_of_cont {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : Y → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous fun y => (Matrix.of.symm (f y) : Fin n → Fin n → ℂ))
    {g : X → Y} (hg : Measurable g) : MeasM (fun x => f (g x)) := hf.measurable.comp hg

theorem measM_mul {A B : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) (hB : MeasM B) : MeasM (fun x => A x * B x) := by
  rw [measM_iff] at hA hB ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hA i l).mul (hB l j)

theorem measM_star {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)ᴴ) := by
  rw [measM_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (hA j i)

theorem cont_det : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of M).det :=
  Continuous.matrix_det continuous_id

theorem cont_adj : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of M).adjugate : Fin n → Fin n → ℂ) :=
  Continuous.matrix_adjugate continuous_id

theorem measM_inv {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)⁻¹) := by
  have hd : Measurable fun x => (A x).det := cont_det.measurable.comp hA
  have hadj : MeasM (fun x => (A x).adjugate) := cont_adj.measurable.comp hA
  rw [measM_iff] at hadj ⊢
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.inv.mul (hadj i j)

variable {k r : ℕ}

theorem measM_nEich (z : Fin (2 * r + k + 1) → ℂ) {ξ : X → Fin r → ℂ} (hξ : Measurable ξ) :
    MeasM (fun x => C2.nEich k r z (ξ x)) := by
  have hxi : Continuous fun ξ : Fin r → ℂ => C2.xiV k r ξ := by
    refine continuous_pi fun i => ?_
    by_cases h : i.val < r
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_const
  have hc : Continuous fun ξ : Fin r → ℂ => (C2.nEich k r z ξ : Matrix _ _ ℂ) := by
    unfold C2.nEich
    have h1 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ z)) :=
      hxi.matrix_vecMulVec continuous_const
    have h2 : Continuous fun ξ : Fin r → ℂ => vecMulVec z (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    have h3 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      hxi.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    fun_prop
  exact measM_of_cont (f := fun ξ => C2.nEich k r z ξ) hc hξ

theorem measM_submatrix_castSucc {A : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : MeasM A) :
    MeasM (fun x => (A x).submatrix Fin.castSucc Fin.castSucc) := by
  rw [measM_iff] at hA ⊢
  intro i j
  exact hA _ _

theorem measM_mX {A : X → Matrix (Fin r) (Fin r) ℂ} (hA : MeasM A) : MeasM (fun x => C2.mX k r (A x)) := by
  have hinv : MeasM fun x => ((A x)ᴴ)⁻¹ := measM_inv (measM_star hA)
  rw [measM_iff] at hA hinv ⊢
  intro i j
  simp only [C2.mX]
  split_ifs
  all_goals first | exact measurable_const | exact hA _ _ | exact hinv _ _

theorem measM_tau (z : Fin (2 * r + k + 1) → ℂ) {v : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : MeasM v) :
    MeasM (fun x => C2.tauM k r z (v x)) := by
  show MeasM fun x => C2.nEich k r z (fun a => v x a.castSucc (Fin.last r)) *
    C2.mX k r ((v x).submatrix Fin.castSucc Fin.castSucc)
  refine measM_mul (measM_nEich z ?_) (measM_mX (measM_submatrix_castSucc hv))
  exact Measurable.of_eval fun a => (measM_iff.1 hv) _ _

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingSndEmptyBlock
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def tauB (a : Fin 1 → Fin j → ℂ) : Fin j → Fin 1 → ℂ := fun i _ => star (a 0 i)

theorem bC_eq (x : U.RC k j (1 + ρ)) : bC x = tauB (aC x) := by
  funext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  simp [bC, tauB]

theorem tauB_mp : MeasurePreserving (tauB (j := j)) volume volume := by
  have u1 := measurePreserving_funUnique (volume : Measure (Fin j → ℂ)) (Fin 1)
  have u2 : MeasurePreserving (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i))
      volume volume :=
    measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure (Fin 1 → ℂ)))
      (f := fun _ => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm)
      (fun _ => (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1)).symm)
  have h := u2.comp (vconj_mp.comp u1)
  have e : (tauB (j := j)) =
      (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i)) ∘
        (fun v : Fin j → ℂ => star v) ∘ ⇑(MeasurableEquiv.funUnique (Fin 1) (Fin j → ℂ)) := by
    funext a i l
    rfl
  rw [e]; exact h

theorem PsiR_mp : MeasurePreserving (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  have h := ((MeasurePreserving.id (volume : Measure (U.RC k (j + 1) ρ))).prod tauB_mp).comp PsiL_mp
  have e : (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) =
      Prod.map id tauB ∘ (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) := by
    funext z; simp [bC_eq]
  rw [e]; exact h

theorem measurePreserving_snd_empty_block (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (fun η : U.XiH j 0 σ => η.2) volume volume := by
  have h0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h1 : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin j → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h2 : IsProbabilityMeasure (volume : Measure (Fin j → Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi]
    infer_instance
  have h3 : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  exact MeasureTheory.measurePreserving_snd

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def TQ (σ : Equiv.Perm (Fin j)) (p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ) : U.Xi k j 1 ρ σ :=
  ((XC p.2.1.1 p.1.1, XC p.2.1.2 p.1.2), ((aC p.2.1.1, bC p.2.1.2), p.2.2.2))

theorem TQ_mp (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (TQ (k := k) (ρ := ρ) σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ))
      (U.muXi k j 1 ρ σ) := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  set μX := (volume : Measure (U.RC k j (1 + ρ)))
  set μY := (volume : Measure (U.RC k 1 ρ))
  set μH := (volume : Measure (U.XiH j 0 σ))
  set μXC := (volume : Measure (U.RC k (j + 1) ρ))
  set μA := (volume : Measure (Fin 1 → Fin j → ℂ))
  set μB := (volume : Measure (Fin j → Fin 1 → ℂ))
  set μHr := (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ)))
  have s1 := Measure.measurePreserving_swap (μ := μY.prod μY) (ν := (μX.prod μX).prod μH)
  have s2 := measurePreserving_prodAssoc (μX.prod μX) μH (μY.prod μY)
  have s3 := (MeasurePreserving.id (μX.prod μX)).prod (Measure.measurePreserving_swap (μ := μH) (ν := μY.prod μY))
  have s4 := (measurePreserving_prodAssoc (μX.prod μX) (μY.prod μY) μH).symm
  have s5 := (middle_four_swap_measure_preserving μX μX μY μY).prod (MeasurePreserving.id μH)
  have c1 := ((PsiL_mp (k := k) (j := j) (ρ := ρ)).prod (PsiR_mp (k := k) (j := j) (ρ := ρ))).prod (measurePreserving_snd_empty_block σ)
  have t1 := (middle_four_swap_measure_preserving μXC μA μXC μB).prod (MeasurePreserving.id μHr)
  have t2 := measurePreserving_prodAssoc (μXC.prod μXC) (μA.prod μB) μHr
  have h := t2.comp (t1.comp (c1.comp (s5.comp (s4.comp (s3.comp (s2.comp s1))))))
  exact h

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

theorem pointStep : PointStep := by
  intro k j ρ σ d hd c hc zA zA' hzA hzA' E _ _ _ F γ hint
  set Gi : U.Xi k j 1 ρ σ → E := fun ξ => U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ) with hGi
  have hT := TQ_mp (k := k) (ρ := ρ) σ
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  haveI : SigmaFinite ((volume : Measure (U.RC k j (1 + ρ))).prod (volume : Measure (U.RC k j (1 + ρ)))) :=
    inferInstance
  haveI : SFinite (U.muXi k j 0 (1 + ρ) σ) := by
    unfold U.muXi U.muRC U.muXiH; infer_instance
  haveI : SFinite ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
    unfold U.muRC; infer_instance
  have hpt : ∀ p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ, Gi (TQ σ p) =
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := by
    rintro ⟨⟨y, y'⟩, ⟨⟨x, x'⟩, η⟩⟩
    have hgx : D.castM (hs' k j ρ) (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d ((x, x'), η) (fun a => a.elim0)
        ((U.Rn k 1 ρ y)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ y')) =
        U.gaXi (p := j) (s := 1) k ρ σ d ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) (fun _ _ => c) γ :=
      GX σ d hd c hc x x' η y y' γ
    simp only [hGi, TQ]
    rw [PS σ zA zA' hzA hzA' x x' η y y', ← hgx, mul_smul]
    rfl
  have hint' : Integrable (Gi ∘ TQ σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ)) :=
    (hT.integrable_comp hint.aestronglyMeasurable).mpr hint
  show ∫ ξ, Gi ξ ∂(U.muXi k j 1 ρ σ) = _
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)]
  have e2 : (fun p => Gi (TQ σ p)) = fun p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ =>
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := funext hpt
  have hint2 := hint'
  rw [show Gi ∘ TQ σ = fun p => Gi (TQ σ p) from rfl, e2] at hint2
  rw [e2, integral_prod _ hint2]
  congr 1
  funext yy
  dsimp only
  rw [integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
section
namespace Formalism.FourierDecayAlt.P

theorem normalFormFromModule_statement : Formalism.FourierDecayAlt.Q.NormalFormFromModule :=
  normal_form_from_module theorem_S_ring actual_pre_level actual_hypotheses_of_parts
    level_coordinates_commute types_complete

theorem normal_form_actual : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  JacquetIntegral.normalFormActual_of_fromModule normalFormFromModule_statement

theorem level_start_actual : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  JacquetIntegral.levelStartActual_of_fromModule normalFormFromModule_statement

end Formalism.FourierDecayAlt.P
end

