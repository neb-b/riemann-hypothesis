module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PositiveMatrixBlocks
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace PositiveMatrixBlocks

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem posM_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_posM_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem posM_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := posM_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, posM_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blk (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_posM_apply, posM_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

end PositiveMatrixBlocks

theorem positive_matrix_block_product : MirabolicColumnBlock := by
  intro R _ a m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    refine ⟨fun t => γ.val t.1.1 t.1.2, blkU (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2)) * γ, ?_, ?_⟩
    · intro i k hik
      show ((1 + posM Subtype.val (-(fun t : UnipotentBlockColumnIndex a m m => γ.val t.1.1 t.1.2))) * γ.val) i k = _
      rw [add_mul, one_mul, PositiveMatrixBlocks.posM_mul_row m _ γ.val (fun j k hj => hγ j k (Or.inl hj.ge)),
        Matrix.add_apply, PositiveMatrixBlocks.posM_col]
      split_ifs with hc
      · rcases hik with hi | _
        · omega
        · rw [Matrix.one_apply_ne (fun e => by rw [e] at hc; omega)]
          simp
      · rw [add_zero]
        exact hγ i k (by omega)
    · show γ = blkU _ * (blkU _ * γ)
      rw [← mul_assoc]
      unfold blkU
      rw [← posU_add, add_neg_cancel, posU_zero, one_mul]
  · intro γ hγ
    apply Units.ext
    ext i k
    exact hγ i k (Or.inl (Nat.zero_le _))
  · intro i k _
    rfl
  · intro i k _
    rfl
  · intro γ γ' hγ hγ' i k hik
    show (γ.val * γ'.val) i k = _
    rw [Matrix.mul_apply]
    rcases hik with hi | hk
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, (1 : Matrix (Fin a) (Fin a) R) i j * γ'.val j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ i j (Or.inl hi)]
        _ = ((1 : Matrix (Fin a) (Fin a) R) * γ'.val) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.one_mul]; exact hγ' i k (Or.inl hi)
    · calc ∑ j, γ.val i j * γ'.val j k = ∑ j, γ.val i j * (1 : Matrix (Fin a) (Fin a) R) j k :=
            Finset.sum_congr rfl fun j _ => by rw [hγ' j k (Or.inr hk)]
        _ = (γ.val * (1 : Matrix (Fin a) (Fin a) R)) i k := Matrix.mul_apply.symm
        _ = _ := by rw [Matrix.mul_one]; exact hγ i k (Or.inr hk)
  · intro k y hkm i l hil
    show (1 + posM Subtype.val y) i l = _
    rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
    intro t _
    rw [Matrix.single_apply, if_neg]
    rintro ⟨e1, e2⟩
    have := t.2
    rw [← e1, ← e2] at hil
    omega
  · intro k γ hkm hγ i l hil
    exact hγ i l (by omega)
  · intro h hB y
    refine ⟨fun t => ∑ s, h.val t.1.1 s.1.1 * y s, ?_, fun t => rfl⟩
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      PositiveMatrixBlocks.posM_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), PositiveMatrixBlocks.mul_posM_blk m y h hB]

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.RowS
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

abbrev V (ι : Type) (a m : ℕ) : Type := UnipotentBlockColumnIndex a (m + 1) (m + 1) → ι → ℂ

def mm (hm : m + 1 < a) : Fin a := ⟨m, by omega⟩

def ix (hm : m + 1 < a) (j : Fin a) (hj : (j : ℕ) < m + 1) : UnipotentBlockColumnIndex a (m + 1) (m + 1) :=
  ⟨(j, ⟨m + 1, hm⟩), hj, le_rfl, le_rfl⟩

def t0 (hm : m + 1 < a) : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ix hm (mm hm) (Nat.lt_succ_self m)

def O (ι : Type) (hm : m + 1 < a) : Set (V ι a m) := {x | ∀ i, x (t0 hm) i ≠ 0}

def rowS (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then x (ix hm j h) else 0

def rowT (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then
    (if (j : ℕ) = m then (x (t0 hm))⁻¹ else -(x (ix hm j h) * (x (t0 hm))⁻¹)) else 0

def sM (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowS hm x))

def sI (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowT hm x))

def e (ι : Type) (hm : m + 1 < a) : V ι a m := Pi.single (t0 hm) 1

def xi (hm : m + 1 < a) (h : GL (Fin a) (ι → ℂ)) : V ι a m := fun t => h.val (mm hm) t.1.1

end PositivityTheory.jumpWindows.CornerBlockIndex

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsIntertwiner
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace SmoothVectorsIntertwiner

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def rmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (Matrix.of M * B)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def lmulₗ (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun M := Matrix.of.symm (B * Matrix.of M)
  map_add' x y := by
    funext i j k
    simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i j k
    simp [Matrix.mul_apply, Finset.mul_sum]

def rmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (rmulₗ B)

def lmulL (B : Matrix (Fin a) (Fin a) (ι → ℂ)) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap (lmulₗ B)

theorem rmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    rmulL B M = Matrix.of.symm (Matrix.of M * B) := rfl

theorem lmulL_apply (B : Matrix (Fin a) (Fin a) (ι → ℂ)) (M : LieI ι a) :
    lmulL B M = Matrix.of.symm (B * Matrix.of M) := rfl

theorem isOpen_U : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have hc : Continuous fun M : LieI ι a => (Matrix.of M).det :=
    Continuous.matrix_det continuous_id
  have e : {M : LieI ι a | IsUnit (Matrix.of M)} =
      (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {x | IsUnit x} := by
    ext M
    simp [Matrix.isUnit_iff_isUnit_det]
  rw [e]
  exact Units.isOpen.preimage hc

omit [Fintype ι] in
theorem one_mem_U : oneI ι a ∈ {M : LieI ι a | IsUnit (Matrix.of M)} := by
  change IsUnit (Matrix.of (Matrix.of.symm 1))
  rw [Equiv.apply_symm_apply]
  exact isUnit_one

theorem orb_rmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (g : GL (Fin a) (ι → ℂ)) (v : X)
    (M : LieI ι a) : orb ρ (ρ g v) M = orb ρ v (rmulL g.val M) := by
  rw [rmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * g.val))) ↔ IsUnit (Matrix.of M) := by
    rw [Equiv.apply_symm_apply]
    exact Units.isUnit_mul_units _ g
  by_cases hM : IsUnit (Matrix.of M)
  · rw [dif_pos hM, dif_pos (hiff.mpr hM), ← ContinuousLinearMap.mul_apply, ← map_mul]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hM, dite_eq_right (mt hiff.mp hM)]

theorem orb_lmul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (M : LieI ι a)
    (hM : IsUnit (Matrix.of M)) (N : LieI ι a) :
    orb ρ v (lmulL (Matrix.of M) N) = ρ hM.unit (orb ρ v N) := by
  rw [lmulL_apply]
  unfold orb
  have hiff : IsUnit (Matrix.of (Matrix.of.symm (Matrix.of M * Matrix.of N))) ↔
      IsUnit (Matrix.of N) := by
    rw [Equiv.apply_symm_apply, ← hM.unit_spec]
    exact Units.isUnit_units_mul _ _
  by_cases hN : IsUnit (Matrix.of N)
  · rw [dif_pos hN, dif_pos (hiff.mpr hN), ← ContinuousLinearMap.mul_apply, ← map_mul ρ]
    congr 2
    ext1
    simp only [IsUnit.unit_spec, Units.val_mul, Equiv.apply_symm_apply]
  · rw [dite_eq_right hN, dite_eq_right (mt hiff.mp hN), map_zero]

omit [Fintype ι] in
theorem orbit_map_intertwiner_comm (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) :
    orb ρ (T v) = fun M => T (orb ρ v M) := by
  funext M
  unfold orb
  split_ifs with h
  · exact (hT _ _).symm
  · exact (map_zero T).symm

theorem smooth_vector_intertwiner_apply (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (T : X →L[ℂ] X)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (v : X) (hv : SmV ρ v) : SmV ρ (T v) := by
  unfold SmV at *
  rw [orbit_map_intertwiner_comm ρ T hT v]
  exact (T.restrictScalars ℝ).contDiff.comp_contDiffOn hv

end SmoothVectorsIntertwiner

open SmoothVectorsIntertwiner in
theorem smooth_vectors_stable_intertwiner : S2 := by
  intro ι _ a X _ _ _ ρ _
  have hU : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := isOpen_U
  have orb_zero : orb ρ (0 : X) = fun _ => 0 := by
    funext M
    unfold orb
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SmV
    rw [orb_zero]
    exact contDiffOn_const
  · intro v w hv hw
    have e : orb ρ (v + w) = fun M => orb ρ v M + orb ρ w M := by
      funext M
      unfold orb
      split_ifs <;> simp
    unfold SmV at *
    rw [e]
    exact hv.add hw
  · intro c v hv
    have h := smooth_vector_intertwiner_apply ρ (c • ContinuousLinearMap.id ℂ X) (fun g x => by simp) v hv
    simpa using h
  · intro g v hv
    unfold SmV at *
    rw [show orb ρ (ρ g v) = fun M => orb ρ v (rmulL g.val M) from
      funext fun M => orb_rmul ρ g v M]
    refine hv.comp (rmulL g.val).contDiff.contDiffOn ?_
    intro M hM
    simp only [Set.mem_setOf_eq, rmulL_apply, Equiv.apply_symm_apply] at hM ⊢
    exact (Units.isUnit_mul_units _ g).mpr hM
  · exact fun T hT v hv => smooth_vector_intertwiner_apply ρ T hT v hv
  · intro v hv
    have hd : ∀ N ∈ {M : LieI ι a | IsUnit (Matrix.of M)}, DifferentiableAt ℝ (orb ρ v) N :=
      fun N hN => (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hN)
    refine ⟨fderiv ℝ (orb ρ v) (oneI ι a), (hd _ one_mem_U).hasFDerivAt, fun Z => ?_⟩
    have key : ∀ N (hN : IsUnit (Matrix.of N)),
        ρ hN.unit (fderiv ℝ (orb ρ v) (oneI ι a) Z) =
          fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N) := by
      intro N hN
      have hL : lmulL (Matrix.of N) (oneI ι a) = N := by
        rw [lmulL_apply, oneI, Equiv.apply_symm_apply, mul_one, Equiv.symm_apply_apply]
      have h0 : HasFDerivAt (orb ρ v) (fderiv ℝ (orb ρ v) N) (lmulL (Matrix.of N) (oneI ι a)) := by
        rw [hL]
        exact (hd N hN).hasFDerivAt
      have h1 : HasFDerivAt (fun M => orb ρ v (lmulL (Matrix.of N) M))
          ((fderiv ℝ (orb ρ v) N).comp (lmulL (Matrix.of N))) (oneI ι a) :=
        h0.comp (oneI ι a) (lmulL (Matrix.of N)).hasFDerivAt
      have h2 : HasFDerivAt (fun M => ρ hN.unit (orb ρ v M))
          (((ρ hN.unit).restrictScalars ℝ).comp (fderiv ℝ (orb ρ v) (oneI ι a))) (oneI ι a) :=
        ((ρ hN.unit).restrictScalars ℝ).hasFDerivAt.comp (oneI ι a) (hd _ one_mem_U).hasFDerivAt
      have e : (fun M => orb ρ v (lmulL (Matrix.of N) M)) = fun M => ρ hN.unit (orb ρ v M) :=
        funext fun M => orb_lmul ρ v N hN M
      rw [e] at h1
      have h3 := congrArg (fun D => D Z) (h2.unique h1)
      simpa [lmulL_apply, rmulL_apply] using h3
    unfold SmV
    have hc : ContDiffOn ℝ ∞ (fun N => fderiv ℝ (orb ρ v) N (rmulL (Matrix.of Z) N))
        {M : LieI ι a | IsUnit (Matrix.of M)} :=
      (hv.fderiv_of_isOpen hU (by simp)).clm_apply (rmulL (Matrix.of Z)).contDiff.contDiffOn
    refine hc.congr fun N hN => ?_
    have hw : ∀ w : X, orb ρ w N = ρ (show IsUnit (Matrix.of N) from hN).unit w := by
      intro w
      unfold orb
      exact dif_pos hN
    rw [hw]
    exact key N hN

end PositivityTheory.jumpWindows

end
end

