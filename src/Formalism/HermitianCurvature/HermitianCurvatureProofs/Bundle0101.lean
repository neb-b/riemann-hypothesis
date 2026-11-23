module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0079

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCoefContSupp
section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

section coef

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cptCoef_cont_supp (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) :
    ContinuousOn F (B.GV k r) ∧ ∃ R : ℝ, ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R :=
  ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1, hF.2.1⟩

end coef

section point

theorem cast_perm_val {m n : ℕ} (e : m = n) (σ : Equiv.Perm (Fin m)) (x : Fin n) :
    ((e ▸ σ) x).val = (σ (Fin.cast e.symm x)).val := by
  subst e; rfl

theorem ptSize_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) : D.ptSize (h ++ [(1, ζ)]) = n + 1 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append, hh.2]

theorem perm_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    U.hMat (hh.2 ▸ D.ptPerm h) (hh.2 ▸ D.ptDiag h) = D.ptMatN h n ∧ (∀ a, (hh.2 ▸ D.ptDiag h) a ≠ 0) ∧
    D.ptMatN (h ++ [(1, ζ)]) (n + 1) =
      C2.monoP (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])) (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) ∧
    (∀ a, (ptSize_app h n hh ζ ▸ D.ptDiag (h ++ [(1, ζ)])) a ≠ 0) ∧
    (∀ a : Fin n, (ptSize_app h n hh ζ ▸ D.ptPerm (h ++ [(1, ζ)])).symm a.castSucc =
      ((hh.2 ▸ D.ptPerm h) a).castSucc) := by
  have hq : D.IsLocPt (h ++ [(1, ζ)]) (n + 1) := Formalism.FourierDecayAlt.P.PBI.isLocPt_app h n hh ζ hζ
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' h n hh.2 hh.1
  obtain ⟨h3, h4⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (h ++ [(1, ζ)]) (n + 1) (ptSize_app h n hh ζ) hq.1
  refine ⟨?_, h2, h3, h4, ?_⟩
  · rw [h1]
    refine (Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ ?_).symm
    intro a
    apply Fin.ext
    have e : Fin.cast hh.2.symm ((hh.2 ▸ D.ptPerm h) a) = D.ptPerm h (Fin.cast hh.2.symm a) :=
      Fin.ext (by rw [Fin.val_cast, cast_perm_val])
    rw [cast_perm_val, e, Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol, Fin.val_cast]
  · intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    have hs := hh.2
    have hb := ((hh.2 ▸ D.ptPerm h) a).isLt
    rw [cast_perm_val, Formalism.FourierDecayAlt.P.Dx1.ptPerm_val, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append 1 ζ h _ (by
      simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    rw [if_pos (by simp only [Fin.val_cast, Fin.val_castSucc]; omega)]
    simp only [Fin.val_cast, Fin.val_castSucc]
    rw [cast_perm_val]
    have e1 := Formalism.FourierDecayAlt.P.Dx1.ptPerm_val h (D.ptPerm h (Fin.cast hh.2.symm a))
    rw [Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol] at e1
    rw [← e1, Fin.val_cast]

end point

section frame

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem baseFrame_last (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    D.IsBaseFrame (p.T.bs P.r) ν'r m₀r := by
  have h : P.r + (P.r - P.r) = P.r := by omega
  have e1 : ν'r = Formalism.FourierDecayAlt.P.PBI.nuR p := by
    rw [Formalism.FourierDecayAlt.P.PBI.nuR, ← hν, Formalism.FourierDecayAlt.P.PBI.zL_lift]
  have e2 : m₀r = Formalism.FourierDecayAlt.P.PBI.m0R p := by
    ext i j
    rw [Formalism.FourierDecayAlt.P.PBI.m0R, ← hm]
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    congr 1 <;> ext <;> simp
  rw [e1, e2]
  exact (Formalism.FourierDecayAlt.P.PBI.levFrame_nuR p).2.2

end frame

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTA
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem sum_lt_castLE {j : ℕ} (hj : j ≤ n) (f : Fin n → ℂ) :
    ∑ i : Fin n, (if i.val < j then f i else 0) = ∑ b : Fin j, f (Fin.castLE hj b) := by
  rw [← Finset.sum_filter]
  have e : (Finset.univ.filter fun i : Fin n => i.val < j) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩; simp
  rw [e, Finset.sum_map]
  rfl

def gram (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Zᴴ * Z

def blkJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => A (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)

def colJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Fin j → ℂ := fun a => A (Fin.castLE j.isLt.le a) j

def Wm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  if h : i.val < j.val then -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) ⟨i.val, h⟩) else if i = j then 1 else 0

theorem Wm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [Wm, Matrix.of_apply]
    rw [dif_neg (by have : j.val < i.val := h; omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h)]
  · simp [Wm]

theorem mul_col_split (A V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ C2.UTset n) (l j : Fin n) :
    (A * V) l j = ∑ b : Fin j, A l (Fin.castLE j.isLt.le b) * V (Fin.castLE j.isLt.le b) j + A l j := by
  rw [Matrix.mul_apply, ← sum_lt_castLE j.isLt.le (fun i => A l i * V i j)]
  have hsplit : ∀ i : Fin n, A l i * V i j = (if i.val < j.val then A l i * V i j else 0) +
      (if i = j then A l j else 0) := by
    intro i
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [if_pos h, if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), add_zero]
    · have e : i = j := Fin.ext h
      subst e
      rw [if_neg (lt_irrefl _), if_pos rfl, hV.2, mul_one, zero_add]
    · rw [if_neg (by omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), hV.1 i j h, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem blk_gram_eq (Z : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blkJ (gram Z) j = (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b))ᴴ *
      Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b) := by
  ext a b
  simp [blkJ, gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem blk_det_ne {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (j : Fin n) : (blkJ (gram Z) j).det ≠ 0 := by
  rw [blk_gram_eq]
  refine (Matrix.PosDef.det_pos (Matrix.PosDef.conjTranspose_mul_self _ ?_)).ne'
  intro x y hxy
  set ex : (Fin j → ℂ) → Fin n → ℂ := fun x l => if h : l.val < j.val then x ⟨l.val, h⟩ else 0 with hex
  have hm : ∀ x : Fin j → ℂ, (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b)) *ᵥ x = Z *ᵥ ex x := by
    intro x
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    set f : Fin n → ℂ := fun l => Z a l * ex x l with hf
    calc ∑ b : Fin j, Z a (Fin.castLE j.isLt.le b) * x b = ∑ b : Fin j, f (Fin.castLE j.isLt.le b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hf, hex, Fin.val_castLE, dif_pos b.isLt]
      _ = ∑ l : Fin n, (if l.val < j.val then f l else 0) := (sum_lt_castLE _ f).symm
      _ = ∑ l : Fin n, f l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases h : l.val < j.val
          · rw [if_pos h]
          · rw [if_neg h]; simp only [hf, hex, dif_neg h, mul_zero]
  rw [hm, hm] at hxy
  have hinj : Function.Injective (Z *ᵥ ·) := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr hZ))
  have := hinj hxy
  funext a
  have h2 := congrFun this (Fin.castLE j.isLt.le a)
  simp only [hex, Fin.val_castLE, dif_pos a.isLt] at h2
  exact h2

theorem Wm_spec {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (l j : Fin n) (hlj : l.val < j.val) :
    (gram Z * Wm Z) l j = 0 := by
  rw [mul_col_split _ _ (Wm_ut Z)]
  have hBc : blkJ (gram Z) j *ᵥ ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) = colJ (gram Z) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)), Matrix.one_mulVec]
  have hrow := congrFun hBc ⟨l.val, hlj⟩
  simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply] at hrow
  have hl : Fin.castLE j.isLt.le ⟨l.val, hlj⟩ = l := Fin.ext rfl
  rw [hl] at hrow
  have hW : ∀ b : Fin j, Wm Z (Fin.castLE j.isLt.le b) j =
      -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) b) := by
    intro b
    simp only [Wm, Matrix.of_apply, Fin.val_castLE, dif_pos b.isLt, Fin.eta]
  simp only [hW, mul_neg, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin j, gram Z l (Fin.castLE j.isLt.le x) * ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) x =
      gram Z l j from hrow]
  ring

theorem Wm_unique {Z V : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hV : V ∈ C2.UTset n)
    (hlow : ∀ l j : Fin n, l.val < j.val → (gram Z * V) l j = 0) : V = Wm Z := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hu : IsUnit (blkJ (gram Z) j).det := isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)
    set x : Fin j → ℂ := fun b => V (Fin.castLE j.isLt.le b) j with hx
    have hB : blkJ (gram Z) j *ᵥ x = -colJ (gram Z) j := by
      ext a
      have h0 := hlow (Fin.castLE j.isLt.le a) j (by simp [a.isLt])
      rw [mul_col_split _ _ hV] at h0
      simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply, hx, Pi.neg_apply]
      linear_combination h0
    have hx' : x = -((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) := by
      have e : x = (blkJ (gram Z) j)⁻¹ *ᵥ (blkJ (gram Z) j *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      rw [e, hB, Matrix.mulVec_neg]
    have h1 := congrFun hx' ⟨i.val, h⟩
    simp only [hx, Pi.neg_apply] at h1
    rw [show Fin.castLE j.isLt.le ⟨i.val, h⟩ = i from Fin.ext rfl] at h1
    rw [h1]
    simp only [Wm, Matrix.of_apply, dif_pos h]
  · have e : i = j := Fin.ext h
    subst e
    rw [hV.2, (Wm_ut Z).2]
  · rw [hV.1 i j h, (Wm_ut Z).1 i j h]

theorem gram_mul (Z u : Matrix (Fin n) (Fin n) ℂ) : gram (Z * u) = uᴴ * gram Z * u := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem Wm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Wm (Z * u) = u⁻¹ * Wm Z := by
  have hZu : (Z * u).det ≠ 0 := by rw [Matrix.det_mul, C2x2.ut_det hu, mul_one]; exact hZ
  refine (Wm_unique hZu (C2x2.ut_mul (C2x2.ut_inv hu) (Wm_ut Z)) ?_).symm
  intro l j hlj
  rw [gram_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ l.val
  · rw [Wm_spec hZ i j (by omega), mul_zero]
  · rw [Matrix.conjTranspose_apply, hu.1 i l (by show l.val < i.val; omega), star_zero, zero_mul]

def Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Wm Z).adjugate

theorem Sm_eq_inv (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z = (Wm Z)⁻¹ := by
  rw [Sm, Matrix.inv_def, C2x2.ut_det (Wm_ut Z), Ring.inverse_one, one_smul]

theorem Sm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z ∈ C2.UTset n := by
  rw [Sm_eq_inv]; exact C2x2.ut_inv (Wm_ut Z)

theorem Sm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Sm (Z * u) = Sm Z * u := by
  rw [Sm_eq_inv, Sm_eq_inv, Wm_mul hZ hu, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (C2x2.ut_unit hu)]

theorem Wm_mul_Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z * Sm Z = 1 := by
  rw [Sm_eq_inv]; exact Matrix.mul_nonsing_inv _ (C2x2.ut_unit (Wm_ut Z))

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCGenToQQ
section
noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

end hs

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def Intw (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (A' : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ, trR P Bs e (A.1 Φ) = MA.actA P A' (trR P Bs e Φ)

theorem rawR_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((Φ + Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ + rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_add, Pi.add_apply, hsv_add, inner_add_right, mul_add]

theorem rawR_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((c • Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      c • rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_smul, Pi.smul_apply, hsv_smul, inner_smul_right, smul_eq_mul]
  ring

theorem toSm_smul' {u : MA.Qp P.r P.TT → ℂ} (c : ℂ) (hu : u ∈ MA.smSub P.r P.TT) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P hu, Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P (Subalgebra.smul_mem _ hu c)]
  rfl

end intw

section clos

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem trR_add (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (Φ + Ψ) = trR P Bs e Φ + trR P Bs e Ψ := by
  funext ρ
  simp only [trR, Pi.add_apply]
  rw [rawR_add, toSm_add P (hsm Φ ρ) (hsm Ψ ρ)]

theorem trR_smul (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (c • Φ) = c • trR P Bs e Φ := by
  funext ρ
  simp only [trR, Pi.smul_apply]
  rw [rawR_smul, toSm_smul' c (hsm Φ ρ)]

theorem actA_smulM (c : ℂ) (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • x) f = c • MA.actA P x f := by
  funext π
  show ∑ π', ((c • x) π π').1 (f π') = c • ∑ π', (x π π').1 (f π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Fintype.sum_eq_single π (fun b hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl), Matrix.one_apply_eq]
  rfl

theorem actA_alg (c : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) c) f = c • f := by
  rw [Algebra.algebraMap_eq_smul_one, actA_smulM, actA_one]

variable (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_add {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A + B) (A' + B') := by
  intro Φ
  show trR P Bs e (A.1 Φ + B.1 Φ) = _
  rw [trR_add hsm, hA, hB, actA_add]

theorem intw_mul {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A * B) (A' * B') := by
  intro Φ
  show trR P Bs e (A.1 (B.1 Φ)) = _
  rw [hA, hB, actA_mul]

theorem intw_alg (c : ℂ) : Intw P Bs e (algebraMap ℂ _ c) (algebraMap ℂ (MA.A P (MA.DQ P)) c) := by
  intro Φ
  show trR P Bs e (c • Φ) = _
  rw [trR_smul hsm, actA_alg]

theorem intw_neg {A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') : Intw P Bs e (-A) (-A') := by
  have h := intw_mul hsm (intw_alg hsm (-1)) hA
  intro Φ
  have e1 : (-A) = algebraMap ℂ _ (-1) * A := by simp
  have e2 : (-A') = algebraMap ℂ (MA.A P (MA.DQ P)) (-1) * A' := by simp
  rw [e1, e2]
  exact h Φ

theorem intw_sub {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A - B) (A' - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact intw_add hsm hA (intw_neg hsm hB)

theorem intw_sum {ι : Type} (s : Finset ι) {A : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {A' : ι → MA.A P (MA.DQ P)} (h : ∀ i ∈ s, Intw P Bs e (A i) (A' i)) :
    Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  first | exact UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum .. | (apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' h | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp

end clos

theorem generator_to_quadratic_form : GenToQQ := by
  intro hRS hGT Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec X
  obtain ⟨d, hL, hstar, hrel, hQQ⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X
  obtain ⟨e, he, hg⟩ := hGT Wp Wq P Bs hPl hk hsec X d hL hstar hrel hQQ
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => hRS Wp Wq P Bs hPl hk e he Φ ρ
  refine ⟨e, he, fun Φ Y a b => ?_⟩

  have hζ : Intw P Bs e d.L.ζ (MA.zA P (MA.DQ P)) := fun Φ => (hg Φ).1
  have hζi : Intw P Bs e d.L.ζi (MA.ziA P (MA.DQ P)) := fun Φ => (hg Φ).2.1
  have hζb : Intw P Bs e d.L.ζb (MA.zbA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.1
  have hζbi : Intw P Bs e d.L.ζbi (MA.zbiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.1
  have hGG : Intw P Bs e d.L.GG (MA.ggA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.1
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.1
  have hnab : Intw P Bs e d.L.nab (MA.nabA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.1
  have hnabs : Intw P Bs e d.L.nabs (MA.nabsA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.2.1
  have hκ : ∀ f, Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f) := fun f Φ => (hg Φ).2.2.2.2.2.2.2.2.1 f
  have hSS : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.1 l hl
  have hSSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l)) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.2 l hl

  have hx : Intw P Bs e (d.x Y) (MA.xA P (MA.DQ P) Y) := hκ _
  have hl0 : Intw P Bs e (d.L.l0 Y) (MA.l0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nab - algebraMap ℂ _ (Y + 1/2) * (d.L.ζb * d.L.GGi))
      (-MA.nabA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnab) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζb hGGi))
  have hm0 : Intw P Bs e (d.L.m0 Y) (MA.m0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nabs - algebraMap ℂ _ (Y - 1/2) * (d.L.ζ * d.L.GGi))
      (-MA.nabsA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnabs) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζ hGGi))
  have hS21 : Intw P Bs e (d.weightedSumBis Y) (MA.weightedSumBis P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hSS l hl) (hκ _)
  have hS12 : Intw P Bs e (d.S12 Y) (MA.S12 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hκ _) (hSSs l hl)
  have hS4 : Intw P Bs e (d.S4 Y) (MA.S4 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_sum hsm _ fun j hj =>
      intw_mul hsm (intw_mul hsm (hSSs l hl) (hSS j (Finset.mem_of_mem_erase hj))) (hκ _)

  have hent : ∀ a b : Fin 2, Intw P Bs e (d.QQ Y a b) (MA.QQr P (MA.DQ P) Y a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show Intw P Bs e (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
          d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) (MA.t11 P (MA.DQ P) Y)
      exact intw_add hsm (intw_add hsm (intw_add hsm (intw_add hsm (intw_mul hsm hGGi (hκ _))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hl0))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hm0) hGGi) hS21))
        (intw_mul hsm hS12 hl0)) (intw_mul hsm hGGi hS4)
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) (MA.t12 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hS12
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) (MA.t21 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hl0) hS21
    · show Intw P Bs e (d.L.GG * d.x Y) (MA.t22 P (MA.DQ P) Y)
      exact intw_mul hsm hGG hx
  have ht : X.t Y a b = (X.QQ Y a b).1 := rfl
  rw [ht, hQQ Y]
  exact hent a b Φ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvPolyCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def sumU (P : M.Par) : ℂ := ∑ i ∈ Finset.Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ))

def GTCCurvScal : Prop :=
  ∀ (P : M.Par), 2 ≤ P.k → ∀ ρ : M.Ty P,
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i) ∧
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i) ∧
    (∀ ex : Finset ℕ, (∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) →
      ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i)

def GTCCurvPolyOfScal : Prop := GTCCurvScal → GTCCurvPoly

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

