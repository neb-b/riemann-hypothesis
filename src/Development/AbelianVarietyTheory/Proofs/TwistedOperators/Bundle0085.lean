module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0080
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardBlockUpperTriangularSubgroupOfTopBlock
section
noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [Field κ] {r t : ℕ}

abbrev blkForm (g : GL (Fin (r + t)) κ) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) κ :=
  (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).submatrix finSumFinEquiv finSumFinEquiv

theorem blkForm_toBlocks₂₁ {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₁ = 0 := by
  ext i j
  simp only [toBlocks₂₁, blkForm, submatrix_apply, of_apply, Matrix.zero_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  apply hg
  have hj : (Fin.castAdd t j).val < r := j.2
  have hi : ¬ (Fin.natAdd r i).val < r := by simp
  simp only [blk2, hj, hi, if_true, if_false]
  exact Nat.zero_lt_one

theorem blkForm_eq {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    blkForm g = fromBlocks (blkForm g).toBlocks₁₁ (blkForm g).toBlocks₁₂ 0 (blkForm g).toBlocks₂₂ := by
  rw [← blkForm_toBlocks₂₁ hg, fromBlocks_toBlocks]

theorem det_blkForm_toBlocks22_ne_zero_of_mem_blockTri {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₂.det ≠ 0 := by
  have h1 : (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h2 : (blkForm g).det = (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det := det_submatrix_equiv_self _ _
  rw [blkForm_eq hg, det_fromBlocks_zero₂₁] at h2
  intro h; rw [h, mul_zero] at h2; exact h1 h2.symm

def blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) : GL (Fin (r + t)) κ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) (by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (A.isUnit.map Matrix.detMonoidHom).ne_zero (D.isUnit.map Matrix.detMonoidHom).ne_zero)

theorem blkForm_blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkForm (blkMk A D B) = fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ) := by
  ext i j
  simp [blkForm, blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem blkMk_mem (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkMk A D B ∈ blockTri (blk2 r) := by
  intro i j hij
  have key : r ≤ i.val ∧ j.val < r := by unfold blk2 at hij; split_ifs at hij <;> omega
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, by ext; simp; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = Fin.castAdd t j' := ⟨⟨j.val, key.2⟩, by ext; simp⟩
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem topBlock_upperTriangularBlockGL (hr : r ≤ r + t) (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    upperLeftBlock hr (blkMk A D B) = A := by
  ext i j
  rw [upper_block_val_submatrix hr (blkMk_mem A D B)]
  have : Fin.castLE hr = Fin.castAdd t := rfl
  rw [this]
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem upperLeftBlock_eq_blkForm_toBlocks11 (hr : r ≤ r + t) {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = (blkForm g).toBlocks₁₁ := by
  rw [upper_block_val_submatrix hr hg]
  ext i j
  rfl

def parSubEquiv (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) :
    parSub hr H ≃ H × GL (Fin t) κ × Matrix (Fin r) (Fin t) κ where
  toFun g := (⟨upperLeftBlock hr g, g.2.2⟩,
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1), (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂)
  invFun x := ⟨blkMk x.1 x.2.1 x.2.2, blkMk_mem _ _ _, by rw [topBlock_upperTriangularBlockGL]; exact x.1.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    have h1 := blkForm_blkMk (r := r) (t := t) (κ := κ) (upperLeftBlock hr g)
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1)) (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂
    have h2 := blkForm_eq g.2.1
    rw [upperLeftBlock_eq_blkForm_toBlocks11 hr g.2.1] at h1
    have h3 : blkForm (blkMk (upperLeftBlock hr g) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1))
        (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂) = blkForm (g : GL (Fin (r + t)) κ) := by
      exact h1.trans h2.symm
    ext i j
    have := congrFun (congrFun h3 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    simpa [blkForm] using this
  right_inv x := by
    obtain ⟨A, D, B⟩ := x
    refine Prod.ext (Subtype.ext (topBlock_upperTriangularBlockGL hr _ _ _)) (Prod.ext ?_ ?_)
    · apply Units.ext
      show (blkForm (blkMk A.1 D B)).toBlocks₂₂ = _
      rw [blkForm_blkMk]; rfl
    · show (blkForm (blkMk A.1 D B)).toBlocks₁₂ = _
      rw [blkForm_blkMk]; rfl

theorem card_parSub_eq (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) [Finite κ] :
    Nat.card (parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  rw [Nat.card_congr (parSubEquiv hr H), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin t → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin t),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_parSub : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ) (hr : r ≤ n), n = r + t →
    ∀ H : Subgroup (GL (Fin r) κ),
      Nat.card (GlobalTheory.ParIndex.parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  intro κ _ _ n r t hr hn H
  subst hn
  exact card_parSub_eq hr H

end GlobalTheory.ParIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ : ∀ (p q : ℕ) (Y : Mat p q), (∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) → LinearMap.det (sP Y) = polJ Y := by
  first | exact @GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | exact GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | (intros; apply GlobalTheory.PolarU.det_sinhc_eq_polarJacobian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquivStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card → ∃ e : Option (Fin n) ≃ Fin (n + 1), GlobalTheory.SepReal.Signs e ε ε' := by
  first | exact @GlobalTheory.SepReal.exists_signs_equiv | exact GlobalTheory.SepReal.exists_signs_equiv | (intros; apply GlobalTheory.SepReal.exists_signs_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPositiveBlockColumnEqStatement
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_positiveBlock_column_eq : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  first | exact @GlobalTheory.Twist.Boost.exists_unitary_col | exact GlobalTheory.Twist.Boost.exists_unitary_col | (intros; apply GlobalTheory.Twist.Boost.exists_unitary_col <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolume
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

open scoped ContDiff

namespace GlobalTheory.SepReal

theorem expS_mem_UJset {m : ℕ} {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.MainNotions.S.UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, neg_mul]
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  have hc : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hJu, hJinv]
  have hcomm : Commute (-(t • X)) (t • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-(t • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp (t • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem orbit_sub_le {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π) {X : Mat m}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) {v : H} (hv : SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v) :
    ‖π (NormedSpace.exp X) v - v‖ ≤ ‖dR π X v‖ := by
  set f : ℝ → H := fun s => π (NormedSpace.exp (s • X)) v with hf
  have hcd : ContDiff ℝ ∞ f := by
    have h1 := hv 1 (fun _ => X) (fun _ => hX)
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    have h3 := h1.comp h2
    convert h3 using 1
    funext s
    simp [f, List.ofFn_succ]
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt f (π (NormedSpace.exp (t • X)) (dR π X v)) t := by
    intro t
    set Lt := π (NormedSpace.exp (t • X)) with hLt
    have h0 : HasDerivAt f (dR π X v) 0 := (hdiff 0).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (Lt.restrictScalars ℝ) (f u)) ((Lt.restrictScalars ℝ) (dR π X v)) (t - t) := by
      rw [sub_self]; exact (Lt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := h1.comp_sub_const t t
    have hfun : f = fun s : ℝ => (Lt.restrictScalars ℝ) (f (s - t)) := by
      funext s
      have he : NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
        congr 2; ring
      simp only [f, he, hπ.1.2 _ (expS_mem_UJset hX t) _ (expS_mem_UJset hX (s - t))]
      rfl
    rw [hfun]
    exact h2
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => π (NormedSpace.exp (t • X)) (dR π X v)) (C := ‖dR π X v‖)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hπ.2.1 _ (expS_mem_UJset hX t) _))
  simpa [f, hπ.1.1] using hb

end GlobalTheory.SepReal

namespace GlobalTheory.SepReal

theorem exists_lowUnit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)} (hds : IsDS ε lam π) : ∃ v, IsLowUnit ε lam π v := by
  obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    simp [norm_smul, this]
  · exact (le_sSup hS : S ≤ lowKSub ε lam π) (S.smul_mem _ hvS)

theorem one_le_eightMB {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 3 ≤ m) (hlam : IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ 8 * (m : ℝ) * B := by
  have i0 : 0 < m := by omega
  have i1 : 1 < m := by omega
  have hlt : lam ⟨1, i1⟩ < lam ⟨0, i0⟩ := hlam.1 (show (⟨0, i0⟩ : Fin m) < ⟨1, i1⟩ from by simp [Fin.lt_def])
  obtain ⟨k0, hk0⟩ := hlam.2 ⟨0, i0⟩
  obtain ⟨k1, hk1⟩ := hlam.2 ⟨1, i1⟩
  have hk : (k1 : ℝ) < k0 := by linarith
  have hk' : k1 < k0 := by exact_mod_cast hk
  have hk'' : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hk'
  have h0 := hB ⟨0, i0⟩
  have h1 := hB ⟨1, i1⟩
  rw [abs_le] at h0 h1
  have hB2 : 1 / 2 ≤ B := by linarith
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem degUpper_of (hlog : LogNear) (hlie : LieBound) (_hvol : VolBall) : DegUpper := by
  unfold DegUpper ForDS
  intro m ε lam B hm hlam hgap hB H _ _ π hds d hd
  obtain ⟨v₀, hv₀⟩ := exists_lowUnit hds
  obtain ⟨hsm, hbd⟩ := hlie m ε lam B hm hlam hgap hB H π hds v₀ hv₀
  have hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π := hds.2.2.1
  have hB1 := one_le_eightMB hm hlam hB
  set c : ℝ := (8 * (m : ℝ) * B) ^ 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by linarith
  set δ : ℝ := 1 / (4 * c) with hδ
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hv1 : ‖v₀‖ = 1 := hv₀.1

  have key : ∀ g ∈ nbh ε δ, (1 / 4 : ℝ) ≤ ‖coefOn π v₀ v₀ g‖ ^ 2 := by
    intro g hg
    have hgU : umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
    obtain ⟨X, hX, hXn, hXe⟩ := hlog m ε δ hδ4 (umat g) hgU hg
    have h1 := hbd [X] (by simpa using hX) (by simp)
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1
    have h2 : ‖dR π X v₀‖ ≤ 1 / 2 := by
      calc ‖dR π X v₀‖ ≤ c * hsn X := h1
        _ ≤ c * (2 * δ) := by gcongr
        _ = 1 / 2 := by rw [hδ]; field_simp; ring
    have h3 : ‖π (umat g) v₀ - v₀‖ ≤ 1 / 2 := by
      rw [← hXe]; exact (orbit_sub_le hπ hX hsm).trans h2
    have h4 : coefOn π v₀ v₀ g = 1 + ⟪v₀, π (umat g) v₀ - v₀⟫_ℂ := by
      simp only [coefOn, inner_sub_right, inner_self_eq_norm_sq_to_K, hv1]
      push_cast; ring
    have h5 : ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ 1 / 2 := by
      calc ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ ‖v₀‖ * ‖π (umat g) v₀ - v₀‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 := by rw [hv1, one_mul]; exact h3
    have h6 : 1 / 2 ≤ ‖coefOn π v₀ v₀ g‖ := by
      rw [h4]
      have := norm_sub_norm_le (1 : ℂ) (-⟪v₀, π (umat g) v₀ - v₀⟫_ℂ)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    nlinarith

  obtain ⟨hdpos, hI⟩ := hd
  obtain ⟨hint, hval⟩ := hI v₀ v₀ v₀ v₀
  have hpt : ∀ g : UJ ε, coefOn π v₀ v₀ g * star (coefOn π v₀ v₀ g) = ((‖coefOn π v₀ v₀ g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint' : Integrable (fun g => ‖coefOn π v₀ v₀ g‖ ^ 2) (muG ε) := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  have hval' : ∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε = 1 / d := by
    have h := hval
    simp only [hpt, inner_self_eq_norm_sq_to_K, hv1] at h
    rw [integral_complex_ofReal] at h
    have h' : ((∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hlint : ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ) ≤ ENNReal.ofReal (1 / d) := by
    calc ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ)
        ≤ ENNReal.ofReal (1 / 4) * muG ε {g | ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2)} := by
          gcongr
          intro g hg
          exact ENNReal.ofReal_le_ofReal (key g hg)
      _ ≤ ∫⁻ g, ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2) ∂muG ε :=
          mul_meas_ge_le_lintegral₀ hint'.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
      _ = ENNReal.ofReal (1 / d) := by
          rw [← hval', ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun g => by positivity)]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)] at ht
  have : (muG ε (nbh ε δ)).toReal ≤ 4 * (1 / d) := by linarith
  rwa [mul_one_div] at this

end GlobalTheory.SepReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
section
open Matrix Formalism.REAL Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

variable {n : ℕ}

def actM {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, Z a b • E a b

def thE (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  -((sgn ε p.1 p.2 : ℝ) : ℂ) • Matrix.single p.2 p.1 (1 : ℂ)

def thM (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : Fin n × Fin n, Z p.1 p.2 • thE ε p

def arr1 {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (j : W →ₗᵢ[ℂ] V) (G : Fin n × Fin n → W) : Arr V n 1 :=
  arrTo V n 1 fun α => j (G (α 0))

def Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  fun z => fderiv ℂ f z (z * Z)

def Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool) (l : List (Fin n × Fin n))
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  l.foldr (fun p g => Rz (thE ε p) g) f

def formOf {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : W →ₗ[ℂ] W) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ).compl₂ T

def funJet {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  formOf (Rw ε l f 1 : W →L[ℂ] W).toLinearMap

theorem funJet_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) (y x : W) :
    funJet ε f l y x = ⟪y, Rw ε l f 1 x⟫_ℂ := rfl

def modJet {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n)) :
    W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).compl₂ (ew E l ∘ₗ j.toLinearMap)) ∘ₛₗ j.toLinearMap

theorem modJet_apply {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n))
    (y x : W) : modJet E j l y x = ⟪j y, ew E l (j x)⟫_ℂ := rfl

section Rel

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]

def JetRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
    B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
      (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0)) ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y x x' : W, j x' = E a b (j x) →
    B (l ++ [(a, b)]) y x = B l y x') ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y y' x : W, j y' = E b a (j y) →
    B ((a, b) :: l) y x = B l y' x) ∧
  ∀ (l : List (Fin n × Fin n)) (G : Fin n × Fin n → W), arr1 j G ∈ Vminus ε E Λ u →
    ∀ y : W, ∑ p, B (l ++ [p]) y (G p) = 0

theorem JetRel.sub {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V}
    {j : W →ₗᵢ[ℂ] V} {B B' : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (h : JetRel ε E Λ u j B)
    (h' : JetRel ε E Λ u j B') : JetRel ε E Λ u j (fun l => B l - B' l) := by
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b hab y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have h1 := h.1 l₁ l₂ a b c d
    have h2 := h'.1 l₁ l₂ a b c d
    rw [sub_sub_sub_comm, h1, h2]
    split_ifs <;> (ext y x; simp only [LinearMap.sub_apply, LinearMap.zero_apply]; ring)
  · simp only [LinearMap.sub_apply, h.2.1 l a b hab y x x' hx, h'.2.1 l a b hab y x x' hx]
  · simp only [LinearMap.sub_apply, h.2.2.1 l a b hab y y' x hy, h'.2.2.1 l a b hab y y' x hy]
  · simp only [LinearMap.sub_apply, Finset.sum_sub_distrib, h.2.2.2 l G hG y, h'.2.2.2 l G hG y, sub_self]

def FunEquiv (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    (∀ x x' : W, j x' = E a b (j x) → fderiv ℂ f z (z * thE ε (a, b)) x = f z x') ∧
    ∀ y y' x : W, j y' = E b a (j y) → ⟪y, fderiv ℂ f z (thE ε (a, b) * z) x⟫_ℂ = ⟪y', f z x⟫_ℂ

def FunSchmid (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    ∑ p, fderiv ℂ f z (z * thE ε p) (G p) = 0

def TauTie (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ Y, inK ε Y → ∀ v v' : W, j v' = actM E (Y.map star) (j v) →
    HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v) v' 0

def LowData (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) :
    Prop :=
  GlRel E ∧ IsUnitary ε E ∧ KHighest ε E Λ u ∧ FiniteDimensional ℂ (kSpan ε E u) ∧
    LinearMap.range j.toLinearMap = kSpan ε E u

def DerTie {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) : Prop :=
  ∀ X, inG ε X → ∀ v : V,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (ι v)) (ι (actM E X v)) 0

end Rel

end GlobalTheory.SphJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZeroStatement
section
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  first | exact @GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | exact GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | (intros; apply GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariantStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJacobian_blockDiag_conj_invariant : ∀ (p q : ℕ) (k k' Y : Mat p q), k * k' = 1 → IsKC k → IsKC k' → polJ (k * Y * k') = polJ Y := by
  first | exact @GlobalTheory.PolarU.Conj.polJ_conj | exact GlobalTheory.PolarU.Conj.polJ_conj | (intros; apply GlobalTheory.PolarU.Conj.polJ_conj <;> assumption)
end

