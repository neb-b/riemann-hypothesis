module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagImageGrass
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Matrix

namespace FlagImageGrass

section Cone

variable {K : Type} {ι : K → Type}

theorem mConeMap_apply [Fintype K] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (F : MRing ι) :
    mConeMap y F = eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F := by
  rw [mConeMap, aeval_def, RingHom.ext_int (algebraMap ℤ (MvPolynomial K Ω)) (Int.castRingHom _)]

theorem cone_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : (Σ k, ι k) → A)
    (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F =
      map φ (eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [eval₂_add, map_add (f := _), hp, hq]
  | mul_X p q hp => simp only [eval₂_mul, map_mul, hp, eval₂_X, map_C, map_X]

theorem cone_map_eq_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : (Σ k, ι k) → A)
    (F : MvPolynomial (Σ k, ι k) ℤ) (h : eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F = 0) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F = 0 := by
  rw [cone_map, h, map_zero]

theorem cone_map_eq_zero_iff {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (y : (Σ k, ι k) → A) (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F = 0 := by
  rw [cone_map]
  exact ⟨fun h => map_injective φ hφ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem cone_smul_eq_zero_iff {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0)
    (y : (Σ k, ι k) → Ω) (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (c p.1 * y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F = 0 := by
  let D : (K → Ω) → MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := fun c => aeval fun k => C (c k) * X k
  have hD : eval₂ (Int.castRingHom _) (fun p => C (c p.1 * y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F =
      D c (eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F) := by
    induction F using MvPolynomial.induction_on with
    | C a => simp only [eval₂_C, Int.coe_castRingHom, map_intCast]
    | add p q hp hq => simp only [eval₂_add, map_add (f := _), hp, hq]
    | mul_X p q hp =>
      rw [eval₂_mul, eval₂_mul, map_mul, hp]
      simp only [eval₂_X, aeval_X, D, map_mul, aeval_C, algebraMap_eq, C_mul]
      ring
  have hinv : ∀ G, D (fun k => (c k)⁻¹) (D c G) = G := by
    intro G
    have : (D fun k => (c k)⁻¹).comp (D c) = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [D, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
    exact congrArg (fun φ => φ G) this
  rw [hD]
  exact ⟨fun h => by rw [← hinv (eval₂ _ _ F), h, map_zero], fun h => by rw [h, map_zero]⟩

end Cone

section Rows

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hN : j + (N - j) = N)

def genTop (τ : Ψ) : Matrix (Fin j) (Fin (j + (N - j))) (MvPolynomial (Ψ × Fin N × Fin N) ℚ) :=
  Matrix.of fun a b => X (τ, Fin.castLE (by omega) a, Fin.cast hN b)

theorem yFl_grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    yFl Ψ N (grFlV Ψ N j hj hjN p) =
      algebraMap _ (ΩFl Ψ N) (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det := by
  have hs : j - 1 + 1 = j := by omega
  unfold yFl
  congr 1
  rw [← Matrix.det_submatrix_equiv_self (finCongr hs)]
  congr 1

def genZ (t : Fin (Fintype.card Ψ)) :
    Matrix (Fin j) (Fin (N - j)) (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ) :=
  Matrix.of fun a b => X (t, a, b)

def toOnePipe : MvPolynomial (Ψ × Fin N × Fin N) ℚ →ₐ[ℚ]
    MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ :=
  aeval fun x => if h : (x.2.1 : ℕ) < j then
    onePipe (genZ Ψ N j (Fintype.equivFin Ψ x.1)) ⟨x.2.1, h⟩ (Fin.cast hN.symm x.2.2) else 0

theorem toOnePipe_genTop (τ : Ψ) :
    (genTop Ψ N j hN τ).map (toOnePipe Ψ N j hN) = onePipe (genZ Ψ N j (Fintype.equivFin Ψ τ)) := by
  ext a b
  simp [toOnePipe, genTop]

theorem toOnePipe_minor (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    toOnePipe Ψ N j hN (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det =
      GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have : (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).map (toOnePipe Ψ N j hN) =
      colsOf ((genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)).map (toOnePipe Ψ N j hN)) p.2 := rfl
  rw [this, toOnePipe_genTop, Equiv.apply_symm_apply]
  rfl

def genTopF (τ : Ψ) : Matrix (Fin j) (Fin (j + (N - j))) (ΩFl Ψ N) :=
  (genTop Ψ N j hN τ).map (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N))

def genLead (τ : Ψ) : Matrix (Fin j) (Fin j) (ΩFl Ψ N) :=
  (genTopF Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))

theorem genLead_det_ne_zero (τ : Ψ) : (genLead Ψ N j hN τ).det ≠ 0 := by
  have hA : genLead Ψ N j hN τ = (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)).mapMatrix
      ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))) := by
    ext a c
    rfl
  rw [hA, ← RingHom.map_det]
  intro h0
  have h1 : ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))).det = 0 :=
    IsFractionRing.injective (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (by rw [h0, map_zero])
  have h2 := congrArg (MvPolynomial.eval fun x : Ψ × Fin N × Fin N => if (x.2.1 : ℕ) = x.2.2 then (1 : ℚ) else 0) h1
  rw [RingHom.map_det, map_zero] at h2
  have h3 : (MvPolynomial.eval fun x : Ψ × Fin N × Fin N => if (x.2.1 : ℕ) = x.2.2 then (1 : ℚ) else 0).mapMatrix
      ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))) = 1 := by
    ext a c
    simp [genTop, Matrix.one_apply, Fin.ext_iff]
  rw [h3, det_one] at h2
  exact one_ne_zero h2

def toFlag : MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ →ₐ[ℚ] ΩFl Ψ N :=
  aeval fun x => ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm x.1))⁻¹ *
    genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm x.1)) x.2.1 (Fin.natAdd j x.2.2)

theorem toFlag_onePipe (t : Fin (Fintype.card Ψ)) :
    (onePipe (genZ Ψ N j t)).map (toFlag Ψ N j hN) =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ * genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm t) := by
  have hAA := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genLead_det_ne_zero Ψ N j hN ((Fintype.equivFin Ψ).symm t)))
  ext a b
  refine Fin.addCases (fun c => ?_) (fun c => ?_) b
  · have : ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ * genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm t))
        a (Fin.castAdd (N - j) c) = ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ *
          genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t)) a c := rfl
    rw [this, hAA]
    simp [onePipe, Matrix.one_apply]
  · simp [onePipe, toFlag, genZ]

theorem toFlag_minor (hj : 1 ≤ j) (hjN : j ≤ N - 1) (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    toFlag Ψ N j hN (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p) =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)).det⁻¹ * yFl Ψ N (grFlV Ψ N j hj hjN p) := by
  rw [yFl_grFlV Ψ N j hN hj hjN p]
  have e1 : GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p =
      (colsOf (onePipe (genZ Ψ N j p.1)) p.2).det := rfl
  rw [e1, AlgHom.map_det, AlgHom.mapMatrix_apply]
  have e2 : (colsOf (onePipe (genZ Ψ N j p.1)) p.2).map (toFlag Ψ N j hN) =
      colsOf ((onePipe (genZ Ψ N j p.1)).map (toFlag Ψ N j hN)) p.2 := rfl
  rw [e2, toFlag_onePipe]
  have e3 : colsOf ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1))⁻¹ *
      genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2 =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1))⁻¹ *
        colsOf (genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2 := rfl
  rw [e3, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', RingHom.map_det, RingHom.mapMatrix_apply]
  rfl

end Rows

theorem image_eq (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = mCoordIdeal (yFl Ψ N ∘ grFlV Ψ N j hj hjN) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := fun a b h =>
    (Fintype.equivFin Ψ).symm.injective (congrArg Prod.fst h)
  ext F
  simp only [PFl, imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, GroundTheory.Heights₂.Heights.Targets.ImageCoord.mConeMap_rename (grFlKappa Ψ N j hj hjN)
      (grFlV Ψ N j hj hjN) (fun _ => rfl) (yFl Ψ N) F]
  exact ⟨fun h => rename_injective _ hκ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem proof : FlagImageGrass.Statement := by
  intro Ψ _ _ N j hj hjN
  have hN : j + (N - j) = N := by omega
  rw [image_eq]
  ext F
  simp only [GroundTheory.Heights₂.Heights.grassIdeal, mCoordIdeal, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, mConeMap_apply, Function.comp_apply]

  have ha : ∀ F : MvPolynomial (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) ℤ,
      eval₂ (Int.castRingHom _) (fun p => C (yFl Ψ N (grFlV Ψ N j hj hjN p)) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (ΩFl Ψ N)) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (MvPolynomial (Ψ × Fin N × Fin N) ℚ)) F = 0 := by
    intro F
    simp only [yFl_grFlV Ψ N j hN hj hjN]
    exact cone_map_eq_zero_iff (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N))
      (IsFractionRing.injective _ _)
      (fun p : (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) =>
        (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det) F

  have hb : ∀ F : MvPolynomial (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) ℤ,
      eval₂ (Int.castRingHom _) (fun p => C (GroundTheory.Heights₂.Heights.grassCoord (Fintype.card Ψ) j (N - j) p) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (GroundTheory.Heights₂.Heights.GrassField (Fintype.card Ψ) j (N - j))) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ))
          (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ)) F = 0 :=
    fun F => cone_map_eq_zero_iff
      (algebraMap (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ)
        (GroundTheory.Heights₂.Heights.GrassField (Fintype.card Ψ) j (N - j)))
      (IsFractionRing.injective _ _) (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j)) F
  rw [ha, hb]
  constructor
  · intro h
    have h' := cone_map_eq_zero (toOnePipe Ψ N j hN).toRingHom _ F h
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toOnePipe_minor] using h'
  · intro h
    have h' := cone_map_eq_zero (toFlag Ψ N j hN).toRingHom _ F h
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toFlag_minor Ψ N j hN hj hjN] at h'
    rw [← ha]
    exact (cone_smul_eq_zero_iff (fun t => (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t)).det⁻¹)
      (fun _ => inv_ne_zero (genLead_det_ne_zero Ψ N j hN _)) _ F).mp h'

end FlagImageGrass

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FsInvPow

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_h_eq (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (fsHerm ι a).h z = (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h z := by
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h : (fsHerm ι a).h = (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) a).h :=
    funext (fsHerm_h_eq a)
  unfold IsSmoothHerm
  rw [h]
  exact Inter.isSmoothHerm_ofMetrics_fs a

theorem isSmoothHerm_fsMulti : IsSmoothHerm (GroundTheory.Heights₂.Heights.fsMulti ι) := by
  unfold GroundTheory.Heights₂.Heights.fsMulti
  exact Inter.isSmoothHerm_ofMetrics_fs _

abbrev invTensor (ι : K → Type) [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  (fsHerm ι (fun _ => -1)).tensor (GroundTheory.Heights₂.Heights.fsMulti ι)

theorem isSmoothHerm_invTensor : IsSmoothHerm (invTensor ι) := by
  show ContDiffOn ℝ _ (fun z => (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z) _
  exact (isSmoothHerm_fsHerm _).mul isSmoothHerm_fsMulti

theorem invTensor_a (k : K) : (invTensor ι).a k = ((0 : K → ℕ) k : ℤ) := by
  show (-1 : ℤ) + 1 = _
  simp

theorem invTensor_h {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (invTensor ι).h z = 1 := by
  show (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z = 1
  rw [fsHerm_h_eq]
  unfold GroundTheory.Heights₂.Heights.fsMulti
  rw [Inter.ofMetrics_fs_h, Inter.ofMetrics_fs_h, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hS : Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩)).ne'
  show Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (-1 : ℤ) * Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (1 : ℤ) = 1
  rw [zpow_neg_one, zpow_one]
  exact inv_mul_cancel₀ hS


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_eq_zero {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem snoc_invTensor (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    II K ι P (n + 1) (Fin.snoc L (invTensor ι)) = 0 := by
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
    classical
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hne : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [(hII K ι).2.2 P n L (invTensor ι) 1 0 hP hL isSmoothHerm_invTensor invTensor_a h1 hne]
  unfold recR
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    unfold divSupp
    rw [Ideal.span_singleton_one, sup_top_eq, Ideal.minimalPrimes_top]
    simp
  have hint : arInt P 1 (invTensor ι) L = 0 := by
    unfold arInt
    refine ptsIntegral_eq_zero P _ _ fun z hz => ?_
    simp [logNorm, invTensor_h hz.1]
  simp [hsupp, hint]

theorem intersection_update_fsHerm_neg_one (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (M : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P (n + 1)) (hM : ∀ i, IsSmoothHerm (M i))
    (j : Fin (n + 1)) :
    II K ι P (n + 1) (Function.update M j (fsHerm ι fun _ => -1)) =
      -II K ι P (n + 1) (Function.update M j (GroundTheory.Heights₂.Heights.fsMulti ι)) := by
  let σ := Equiv.swap j (Fin.last n)
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => M (σ (Fin.castSucc i))
  have hL : ∀ i, IsSmoothHerm (L i) := fun i => hM _
  have key : ∀ C, Function.update M j C ∘ σ = Fin.snoc L C := by
    intro C
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp only [Function.comp_apply, Fin.snoc_castSucc, L]
      rw [Function.update_of_ne]
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact (Fin.castSucc_lt_last i).ne h
  have hsm : ∀ C, IsSmoothHerm C → ∀ i, IsSmoothHerm (Function.update M j C i) := by
    intro C hC i
    by_cases h : i = j
    · subst h
      simpa using hC
    · rw [Function.update_of_ne h]
      exact hM i
  have hsym : ∀ C, IsSmoothHerm C →
      II K ι P (n + 1) (Function.update M j C) = II K ι P (n + 1) (Fin.snoc L C) := by
    intro C hC
    rw [← key C]
    exact ((hII K ι).1 P (n + 1) _ σ hP (hsm C hC)).symm
  rw [hsym _ (isSmoothHerm_fsHerm _), hsym _ isSmoothHerm_fsMulti]
  have hadd := (hII K ι).2.1 P n L (fsHerm ι fun _ => -1) (GroundTheory.Heights₂.Heights.fsMulti ι) hP hL
    (isSmoothHerm_fsHerm _) isSmoothHerm_fsMulti
  rw [snoc_invTensor II hII P n L hP hL] at hadd
  linarith

theorem proof : FsInvPow.Statement := by
  intro II K _ ι _ P d hII hP
  cases d with
  | zero =>
    rw [pow_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    let M : ℕ → Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k i =>
      if (i : ℕ) < k then GroundTheory.Heights₂.Heights.fsMulti ι else fsHerm ι fun _ => -1
    have hM : ∀ k i, IsSmoothHerm (M k i) := by
      intro k i
      dsimp only [M]
      split_ifs
      · exact isSmoothHerm_fsMulti
      · exact isSmoothHerm_fsHerm _
    have step : ∀ k, (hk : k < n + 1) →
        II K ι P (n + 1) (M k) = -II K ι P (n + 1) (M (k + 1)) := by
      intro k hk
      have h1 : Function.update (M k) ⟨k, hk⟩ (fsHerm ι fun _ => -1) = M k := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
      have h2 : Function.update (M k) ⟨k, hk⟩ (GroundTheory.Heights₂.Heights.fsMulti ι) = M (k + 1) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
          have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          dsimp only [M]
          by_cases hi : (i : ℕ) < k
          · rw [if_pos hi, if_pos (by omega)]
          · rw [if_neg hi, if_neg (by omega)]
      rw [← h1, ← h2]
      exact intersection_update_fsHerm_neg_one II hII P n (M k) hP (hM k) ⟨k, hk⟩
    have hpow : ∀ k, k ≤ n + 1 → II K ι P (n + 1) (M 0) = (-1) ^ k * II K ι P (n + 1) (M k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [ih (by omega), step k (by omega), pow_succ]
        ring
    have h0 : M 0 = fun _ => fsHerm ι fun _ => -1 := by
      funext i
      simp [M]
    have hd : M (n + 1) = fun _ => GroundTheory.Heights₂.Heights.fsMulti ι := by
      funext i
      simp [M, i.isLt]
    rw [← h0, ← hd]
    exact hpow (n + 1) le_rfl

end FsInvPow

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

