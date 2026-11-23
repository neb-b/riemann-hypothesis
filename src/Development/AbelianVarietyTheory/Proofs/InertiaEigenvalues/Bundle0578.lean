module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EOsurjOneX
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteField
section
open Matrix Formalism.IndefR.Datum
open Classical

namespace GlobalTheory

theorem addChar_inv_isPrimitive_of_isPrimitive {k : Type} [Field k] {R : Type} [CommRing R] (ψ : AddChar k R)
    (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  intro a ha h
  apply hψ (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply, neg_mul] using this

theorem sum_addChar_trace_rectMatrix_mul {k : Type} [Field k] [Fintype k] {R : Type} [CommRing R] [IsDomain R]
    (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r t : ℕ} (m : Matrix (Fin t) (Fin r) k) :
    ∑ b : Matrix (Fin r) (Fin t) k, ψ (trace (b * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r * t) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, mul_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

variable {k : Type} [Field k] {r t : ℕ}

def squareAndRectColumnsEquivWideMatrix : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k ≃ Matrix (Fin r) (Fin (r + t)) k where
  toFun p := fun i j => Fin.addCases (p.1 i) (p.2 i) j
  invFun y := (y.submatrix id (Fin.castAdd t), y.submatrix id (Fin.natAdd r))
  left_inv p := by
    ext i j
    · exact Fin.addCases_left (motive := fun _ => k) j
    · exact Fin.addCases_right (motive := fun _ => k) j
  right_inv y := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

theorem topLeftBlock_neg_eq_submatrix_castAdd (y : Matrix (Fin r) (Fin (r + t)) k) :
    topL r (-y) = -(y.submatrix id (Fin.castAdd t)) := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨i.2, by omega⟩]; rfl

theorem topLeftBlock_eq_submatrix_castAdd (u : Matrix (Fin (r + t)) (Fin r) k) :
    topL r u = u.submatrix (Fin.castAdd t) id := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨by omega, j.2⟩]; rfl

theorem lowZero_iff_submatrix_natAdd_eq_zero (u : Matrix (Fin (r + t)) (Fin r) k) :
    LowZero r u ↔ u.submatrix (Fin.natAdd r) id = 0 := by
  constructor
  · intro h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2
  · intro h i j hi _
    obtain ⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simpa using congr_fun (congr_fun h i') j

theorem trace_mul_split_castAdd_natAdd (y : Matrix (Fin r) (Fin (r + t)) k) (u : Matrix (Fin (r + t)) (Fin r) k) :
    trace (y * u) = trace (y.submatrix id (Fin.castAdd t) * u.submatrix (Fin.castAdd t) id) +
      trace (y.submatrix id (Fin.natAdd r) * u.submatrix (Fin.natAdd r) id) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]

theorem sum_GL_character_neg_det_addChar_trace (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (w : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-a).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (a * w))
      = ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
          ψ⁻¹ (trace (w * (x : Matrix (Fin r) (Fin r) k))) := by
  symm
  refine Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k))
    (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_
  · intro a ha
    rw [dite_eq_right, zero_mul]
    intro h
    exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩
  · intro x
    have hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det := by
      rw [neg_neg]; exact (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rw [dite_eq_left hx]
    have hu : hx.unit = Matrix.GeneralLinearGroup.det x := Units.ext (by simp)
    rw [hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]

end GlobalTheory

namespace GlobalTheory

theorem fourier_flatDatum_finite : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  intro k _ _ ψ ξ r n hψ hξ
  rcases lt_or_ge n r with hnr | hrn
  · refine ⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩
    have h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0 := fun y =>
      Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])
    have h2 : (topL r u).det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])
    rw [one_mul, dite_eq_right (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [dite_eq_right (by rw [h1 y]; exact not_isUnit_zero), zero_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  obtain ⟨hnorm, hGint, hGinv, -⟩ := _root_.GlobalTheory.complexMatrixGaussSum_norm_integral_galois k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2) := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    rw [← hnorm] at this
    norm_num at this
  refine ⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩
  · refine IsIntegral.mul (IsIntegral.pow ?_ _) hGint
    rw [hq]
    exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))
  · have : q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹ := by
      rw [pow_add, mul_inv]
      field_simp
    rw [this]
    exact hGinv

  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dite_eq_left hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLeSquarefree
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section
namespace GlobalTheory.GLq.UpperWeight

def cnt {g : ℕ} (L : List (Pc g)) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card

theorem sum_get_fst {g : ℕ} (L : List (Pc g)) : ∑ j : Fin L.length, (L.get j).1 = degL L := by
  induction L with
  | nil => simp [degL]
  | cons a L ih =>
    show ∑ j : Fin (L.length + 1), ((a :: L).get j).1 = _
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at ih ⊢
    rw [ih]; simp [degL]

theorem comb_bound {g : ℕ} (L : List (Pc g)) (hg : 1 ≤ g) (hpos : ∀ p ∈ L, 0 < p.1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ (1 + 1 / (g : ℝ)) ^ (degL L) * (g : ℝ) ^ k := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  set w : Finset (Fin L.length) → ℕ := fun I => ∑ j ∈ I, (L.get j).1 with hw
  set x : ℝ := 1 / (g : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity

  have h1 : (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))
        ≤ ∑ i ∈ Finset.range k, (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : (0 : ℝ) ≤ (g : ℝ) ^ (k - i - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (cnt L i))
    linarith

  have h2 : ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i)
      = ∑ I : Finset (Fin L.length), if w I ≤ k then (g : ℝ) ^ (k - w I) else 0 := by
    have : ∀ i, (cnt L i : ℝ) = ∑ I : Finset (Fin L.length), if w I = i then (1 : ℝ) else 0 := by
      intro i
      simp only [cnt, Finset.sum_boole, hw]
    simp_rw [this, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_iff]

  have h3 : ∀ I : Finset (Fin L.length), (if w I ≤ k then (g : ℝ) ^ (k - w I) else 0) ≤ (g : ℝ) ^ k * x ^ w I := by
    intro I
    split_ifs with h
    · rw [pow_sub₀ _ hg0.ne' h, hx, one_div_pow, one_div]
    · positivity

  have h4 : ∑ I : Finset (Fin L.length), x ^ w I = ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hw, Finset.prod_pow_eq_pow_sum]
  have h5 : ∏ j : Fin L.length, (1 + x ^ (L.get j).1) ≤ (1 + x) ^ degL L := by
    rw [← sum_get_fst, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    have hj : 0 < (L.get j).1 := hpos _ (List.get_mem L j)
    have := pow_add_pow_le (zero_le_one' ℝ) hx0 hj.ne'
    simpa using this
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ∑ I : Finset (Fin L.length), (g : ℝ) ^ k * x ^ w I := Finset.sum_le_sum fun I _ => h3 I
    _ = (g : ℝ) ^ k * ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by rw [← Finset.mul_sum, h4]
    _ ≤ (g : ℝ) ^ k * (1 + x) ^ degL L := by gcongr
    _ = _ := by rw [mul_comm]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem wtC_eJ_le : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 →
    Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  intro g _ L hg hG ψ hψ N k s hN hk f hm hd hc hsq
  obtain ⟨Q, hQ, -, hdeg, hset⟩ := (_root_.GlobalTheory.GLq.Label.label_main g L hg hG N).2.2 f hm hd hc hsq
  set τ := hcL (Q.map Prod.snd) N with hτ
  have hser : eSerC L N f = zOf τ := by
    unfold eSerC; rw [hset, finsum_mem_singleton]
  have hirr : IsIrr τ := by
    have : τ ∈ {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f} := by rw [hset]; rfl
    exact this.1
  have hcl := isClass_of_isIrr hirr
  obtain ⟨d, hdpos, hd1⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g N) (eU g N ψ) τ).2.1 hirr
  have hL : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 ∧ wh ψ p.2 = 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hQ q hq).1.2.1, _root_.GlobalTheory.GLq.wh_cusp_eq_one g ψ hψ _ _ (hQ q hq).1.2.1 (hQ q hq).2⟩
  have hlb := fun i (hi : i ≤ N) => _root_.GlobalTheory.GLq.Leibniz.main g ψ hψ (Q.map Prod.snd) N i hdeg hi hL
  have hwhU : tr (eU g N ψ) τ = 1 := (hlb 0 (Nat.zero_le _)).2
  have hkN : k < N := by omega
  set TR : ℝ := (∑ i ∈ Finset.range k, (cnt (Q.map Prod.snd) i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1)))
    + cnt (Q.map Prod.snd) k with hTR
  have hJ : tr (eJ g N k s ψ) τ = (TR : ℂ) := by
    rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN τ hcl, _root_.GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der g ψ hψ N k hk hkN τ hcl, (hlb k hkN.le).1, hTR]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hlb i (by simp at hi; omega)).1]
    rfl
  obtain ⟨-, hU1, hJ', -⟩ := _root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ' hN
  have hb := comb_bound (Q.map Prod.snd) (by omega) (fun p hp => (hL p hp).1.1) k
  rw [hdeg] at hb
  unfold wtC
  rw [hser, (_root_.GlobalTheory.GLq.trIdem _ (eJ g N k s ψ) τ).2.2, (_root_.GlobalTheory.GLq.trIdem _ (eU g N ψ) τ).2.2, hwhU, hJ, hJ1, hU1, hd1]
  set M := N * (N - 1) / 2
  set a : ℝ := (d : ℝ) / (Fintype.card (Gn g N) : ℝ) with ha
  set m : ℝ := ((g : ℝ) ^ M)⁻¹ with hm'
  have e1 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * (TR : ℂ) = ((a * TR : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e2 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * 1 = ((a : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e3 : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = (((g : ℝ) ^ k * m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  have e4 : ((g : ℂ) ^ M)⁻¹ = ((m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hm0 : 0 < m := by rw [hm']; positivity
  have ha0 : 0 < a := by
    rw [ha]; apply div_pos (by exact_mod_cast hdpos); exact_mod_cast Fintype.card_pos
  have hT : TR / (g : ℝ) ^ k ≤ (1 + 1 / (g : ℝ)) ^ N := by rw [div_le_iff₀ hgk]; exact hb
  calc a * TR / ((g : ℝ) ^ k * m) = (a / m) * (TR / (g : ℝ) ^ k) := by rw [div_mul_div_comm, mul_comm ((g : ℝ) ^ k) m]
    _ ≤ (a / m) * (1 + 1 / (g : ℝ)) ^ N := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 + 1 / (g : ℝ)) ^ N * (a / m) := by ring

end GlobalTheory.GLq.UpperWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLattice
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Pass.LocDual.OneX

theorem span_stable (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (γ : GE D.nd) :
    ∀ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)),
      actK i r Xs x γ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) := by
  let f : (Fin a → Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] (Fin a → Fin D.R.nV → KK D.nd i) :=
    LinearMap.pi fun b => Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ) ∘ₗ LinearMap.proj b
  have hf : ∀ v, f v = actK i r Xs x γ v := fun v => rfl
  intro v hv
  rw [← hf]
  have h : Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) ≤
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))).comap f := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [SetLike.mem_coe, Submodule.mem_comap, hf]
    exact Submodule.subset_span (hst γ y hy)
  exact h hv

end GlobalTheory.Pass.LocDual.OneX


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.Pass.LocDual.OneX.main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  intro D hF i r hr Xs w hw n hP k M hSub F hFs
  obtain ⟨a, x, E, Y, hYfg, hst, hE, hc⟩ := GlobalTheory.Pass.LocDual.OneX.cutCoc_finset_common D i w hw r Xs M F hFs
  have hC := GlobalTheory.BlockSum.exists_stable_compl_actK D i r Xs hr x (Submodule.span (KK D.nd i) (Y : Set _))
    (fun γ => GlobalTheory.Pass.LocDual.OneX.span_stable D i r Xs x Y hst γ)
  refine ⟨GlobalTheory.Pass.LocDual.OneX.XG i w hw r Xs hr x Y hst,
    GlobalTheory.Pass.LocDual.OneX.isSummandTw_XG D i w hw r Xs hr x Y hst hC, ?_⟩
  obtain ⟨LY, hLY⟩ := GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice D i w hw r Xs hr x Y hst hYfg
  have hy := GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT D hF i r hr Xs w hw n hP x Y hst E hE LY hLY
  apply Submodule.span_le.2
  intro c hcF
  obtain ⟨φ, hφ, rfl⟩ := hc c hcF
  obtain ⟨φ', hG, hpush⟩ := GlobalTheory.Pass.LocDual.OneX.PushEq.main D i w hw r Xs hr x Y hst E hE M LY hLY φ hφ
  unfold BlochKatoDuality.spanPush
  exact Submodule.subset_span (R := Br.OLL D.nbr i w hw) (M := Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) ⟨LY, φ', hG, ⟨_, hy.1⟩, hy, (hpush ⟨_, hy.1⟩ rfl).symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CocycleInt

theorem TWincl_comp_toB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] {T : LocLat (Gl l) ℚ_[l] K O} (z : TW (OA l O) T) :
    TWincl (toOB l O) T (TWincl (toOCr l O) T z) = TWincl (toB l O) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r x => rfl

theorem TWincl_smul' {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

end GlobalTheory.BKGal.CocycleInt


open GlobalTheory.BKGal.CocycleInt in
theorem GlobalTheory.BKGal.potential_cocycle_mem_lpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R hηH hl y hyY c hc b hb g hg hex
  obtain ⟨ε, hε⟩ := (_root_.GlobalTheory.MuOfEps.main l).1
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hval, rfl⟩ := hb
  have hl2 : l ≠ 2 := by omega
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB l a e O K t ϖ hl2 ι η H D T R σ c (by rw [hconn]; exact hc) g hg
  obtain ⟨w₁, hw₁⟩ := _root_.GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower R.jB R.cmp ε hε z
  obtain ⟨z₀, hz₀⟩ := _root_.GlobalTheory.BKExp.muPow_smul_crisVal_integral l a e O K t ϖ ι η H D T R y hyY hy m₀ b₀ hm₀ hval ε hε
  obtain ⟨z₁, hz₁⟩ := _root_.GlobalTheory.BKGal.muPow_smul_actB_sub_mem l O K T g ε hε (H + 2 * η) b₀ z₀ hz₀
  obtain ⟨n, x, hx⟩ := hex
  set jσ := R.jB (toBcris t ϖ D.toPhiMod σ)
  refine _root_.GlobalTheory.BKGal.Count.count l O K T hl2 ε hε (H + 2 * η) n c (by omega) _ x
    (toOCr l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) • w₁ - (l : O) ^ c • TWincl (toOCr l O) T z₁) hx ?_
  have hsplit : actB (sQ l) T g (jσ - b₀) - (jσ - b₀) = (actB (sQ l) T g jσ - jσ) - (actB (sQ l) T g b₀ - b₀) := by
    rw [map_sub]; abel
  have hmu : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η) : OA l O) =
      ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ η) := by
    rw [show H + 2 * η = (H + η) + η by ring, pow_add]
  rw [hsplit, map_sub, TWincl_smul', map_smul, TWincl_comp_toB, ← hz₁, smul_sub, hz, ← hw₁]
  rw [smul_sub, hmu, map_mul, mul_smul, hw₁, smul_comm ((l : O) ^ c) (toB l O _ * toB l O _ : OB l O)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSupStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_inf_modulus_eq_sup : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁] [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) → ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} → 𝔟 ≤ Ideal.span {(q : 𝓞 K)} → GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → GlobalTheory.FieldSize.IsRay H₁ 𝔞 → GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  first | exact @GlobalTheory.RayCompositum.fieldRange_sup_eq_top | exact GlobalTheory.RayCompositum.fieldRange_sup_eq_top | (intros; apply GlobalTheory.RayCompositum.fieldRange_sup_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_eq_filtration_sum_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, f ∈ Lat C h T i ζ ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k : ℤ, f k ∈ Di (HW l) h T i ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (f k) ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
  first | exact @GlobalTheory.NL.LatFil.lat_eq_fil | exact GlobalTheory.NL.LatFil.lat_eq_fil | (intros; apply GlobalTheory.NL.LatFil.lat_eq_fil <;> assumption)
end

