module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRealMatrixForLatticeAndDualWithDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Gl2AdelicDoubleCosetDecompositionTotallyReal
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Reps

variable {F : Type} [Field F] [NumberField F]

theorem aff_mul_aff {R : Type} [CommRing R] (a b : Rˣ) : aff a 0 * aff b 0 = aff (a * b) (0 : R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (η : Fˣ) : toFin (aff η 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom η) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem det_aff' {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

theorem exists_sl_aff (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ Matrix.GeneralLinearGroup.det σ = 1 ∧
      g = toFin σ * (aff y 0 * u) := by
  set y := Matrix.GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff', hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem TP_mul {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v)
  rw [reAt_eq, reAt_eq] at this; rw [reAt_eq, map_mul]; exact this

theorem TP_inv {x : F} (hx : TP x) : TP x⁻¹ := fun v => by
  have := inv_pos.2 (hx v)
  rw [reAt_eq] at this; rw [reAt_eq, map_inv₀]; exact this

end GlobalTheory.HilbertThetaSeries.Reps

open GlobalTheory.HilbertThetaSeries.Reps in
theorem GlobalTheory.HilbertThetaSeries.finite_reps : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  intro F _ _ _ p hp δ hδ
  classical
  obtain ⟨Y0, hY0⟩ := (GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F).1
  choose ξf hξf using (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).2 δ hδ
  set ι := Units.map (algebraMap F (Af F)).toMonoidHom with hι
  refine ⟨Y0.image (fun y => ι (ξf y) * y), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact (hξf y).2
  · intro g
    obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl_aff (KLev F 2 1) (isOpen_KLev le_rfl) g
    obtain ⟨y0, hy0, ξ, u0, hξ, hu0, hy⟩ := hY0 y
    have hK := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 u0 0 hu0 (fun w => by simp)
    refine ⟨aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹, ?_, ι (ξf y0) * y0, Finset.mem_image_of_mem _ hy0, aff u0 0 * u, mul_mem hK.1 hu, ?_⟩
    · have hd : (aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹ : GL (Fin 2) F).val.det = ((ξ⁻¹ * ξf y0 : Fˣ) : F) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hσ, det_aff', inv_one, mul_one]
      rw [hd, Units.val_mul]
      exact TP_mul (by simpa using TP_inv hξ) (hξf y0).1
    · rw [e, map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, toFin_aff, ← mul_assoc, aff_mul_aff, aff_mul_aff, hy]
      congr 2
      simp only [map_mul, map_inv, hι]
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) ξ = a
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) (ξf y0) = b
      rw [mul_comm a⁻¹ b, mul_assoc b, ← mul_assoc a⁻¹, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul, ← mul_assoc]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_reps | exact GlobalTheory.HilbertThetaSeries.finite_reps | (intros; apply GlobalTheory.HilbertThetaSeries.finite_reps <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.QAff

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_eq (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := (rfl)

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have hv : ∀ v : InfinitePlace F, ((reAt v x : ℝ) : ℂ) = v.embedding x := fun v =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [Complex.ofReal_sum, Complex.ofReal_ratCast]
  simp_rw [hv]
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ)]
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun σ : F →ₐ[ℚ] ℂ => σ x) (fun _ => rfl)]
  symm
  refine Fintype.sum_equiv ((Equiv.subtypeUnivEquiv
    (fun φ : F →+* ℂ => IsTotallyReal.complexEmbedding_isReal φ)).symm.trans
    (InfinitePlace.mkReal.trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)))) _ _ ?_
  intro φ
  simp [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)]

theorem reAt_mul (v : InfinitePlace F) (x y : F) : reAt v (x * y) = reAt v x * reAt v y := by
  rw [← rhom_eq, ← rhom_eq, ← rhom_eq, map_mul, Pi.mul_apply]

theorem e00 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = reAt v (ε : F) :=
  rhom_eq v _

theorem e01 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = reAt v b :=
  rhom_eq v _

theorem e10 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  simp [cmp, toInf, aff]

theorem e11 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  simp [cmp, toInf, aff]

theorem denom_aff (ε : Fˣ) (b : F) (v : InfinitePlace F) (w : ℂ) :
    UpperHalfPlane.denom (cmp v (toInf (aff ε b))) w = 1 := by
  rw [UpperHalfPlane.denom, e10, e11]; simp

theorem act_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (aff ε b)) z v : UpperHalfPlane) : ℂ) = (reAt v (ε : F) : ℂ) * (z v : ℂ) + (reAt v b : ℂ) := by
  have hd : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff ε b))) : ℝˣ) : ℝ) := by
    simpa [Matrix.det_fin_two, e00, e01, e10, e11] using hε v
  simp only [act]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, denom_aff, div_one, UpperHalfPlane.num]
  simp [e00, e01]

theorem ez_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (η : F) :
    ez η (act (toInf (aff ε b)) z) = ez (η * ε) z * et (η * b) := by
  simp only [ez, et, act_aff ε b hε]
  rw [← Complex.exp_add, ← Complex.ofReal_ratCast, ← sum_reAt]
  congr 1
  simp only [reAt_mul]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

theorem weightSlash_hilbertAffine_apply (k : ℕ) (f : Hn F → ℂ) (ε : Fˣ) (b : F) (z : Hn F) :
    sl0 k (toInf (aff ε b)) f z = f (act (toInf (aff ε b)) z) := by
  simp only [sl0, denom_aff, Finset.prod_const_one, inv_one, one_pow, one_mul]

omit [IsTotallyReal F] in
theorem exists_den (x : F) : ∃ E : ℕ, 0 < E ∧ IsIntegral ℤ ((E : F) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] at hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases le_total 0 y with h | h
  · have e : ((y.natAbs : ℕ) : F) = (y : F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    rw [e]
    exact hint
  · have e : ((y.natAbs : ℕ) : F) = -(y : F) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h, Int.cast_neg]
    rw [e, neg_mul]
    exact hint.neg

theorem hasQ_aff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F),
    TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  intro F _ _ _ k f a ε b hε hf
  obtain ⟨⟨D, hD, hDa⟩, hsum⟩ := hf
  obtain ⟨E, hE, hEint⟩ := exists_den (ε : F)
  have hε0 : (ε : F) ≠ 0 := ε.ne_zero
  refine ⟨⟨D * E, by positivity, ?_⟩, ?_⟩
  · intro ξ hξ
    have ha : a (ξ / ε) ≠ 0 := fun h0 => hξ (by simp [h0])
    obtain ⟨h1, h2⟩ := hDa _ ha
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · left
        rwa [div_eq_zero_iff, or_iff_left hε0] at h1
      · right
        intro v
        have hp := mul_pos (h1 v) (hε v)
        rwa [← reAt_mul, div_mul_cancel₀ _ hε0] at hp
    · have hm := h2.mul hEint
      have e : ((D * E : ℕ) : F) * ξ = ((D : F) * (ξ / ε)) * ((E : F) * ε) := by
        push_cast
        field_simp
      rw [e]
      exact hm
  · intro z
    have hs := hsum (act (toInf (aff ε b)) z)
    simp only [ez_aff ε b hε z] at hs
    rw [weightSlash_hilbertAffine_apply]
    have hc := (Equiv.hasSum_iff (Units.mulRight ε⁻¹)).mpr hs
    convert hc using 1
    funext ξ
    simp only [Function.comp_apply, Units.mulRight_apply, Units.val_inv_eq_inv_val]
    rw [← div_eq_mul_inv, div_mul_cancel₀ _ hε0]
    ring

end GlobalTheory.HilbertThetaSeries.QAff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_affineTranslate_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F), TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | exact GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | (intros; apply GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesCosetInversionFormula
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.WCos
open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

noncomputable def sg (v : InfinitePlace F) : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).comp rhom

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x :=
  ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).1 v x).symm

theorem cmp_wm (c : Fˣ) (v : InfinitePlace F) (i j : Fin 2) :
    ((HilbertThetaSeries.cmp v (toInf (wm c)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = sg v (((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem sg_ne (c : Fˣ) (v : InfinitePlace F) : sg v (c : F) ≠ 0 := (map_ne_zero _).2 c.ne_zero

theorem denom_wm (c : Fˣ) (v : InfinitePlace F) (z : ℂ) :
    denom (HilbertThetaSeries.cmp v (toInf (wm c))) z = (sg v (c : F) : ℂ) * z := by
  unfold denom
  rw [cmp_wm, cmp_wm]
  simp [wm]

theorem act_wm (c : Fˣ) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (wm c)) z v : ℍ) : ℂ) = -((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))⁻¹ := by
  have hc : (sg v (c : F) : ℂ) ≠ 0 := by exact_mod_cast sg_ne c v
  have hz : ((z v : ℍ) : ℂ) ≠ 0 := (z v).ne_zero
  unfold HilbertThetaSeries.act
  rw [coe_smul_of_det_pos, denom_wm]
  · unfold num
    rw [cmp_wm, cmp_wm]
    simp [wm]
    field_simp
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, cmp_wm, cmp_wm, cmp_wm, cmp_wm]
    simp [wm]

theorem ez_QF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (b : F) (x : κ → F) (w : Hn F) :
    ez (b * QF G x) w = Complex.exp (Real.pi * Complex.I * ∑ j : InfinitePlace F × κ,
      ((sg j.1 b : ℂ) * (w j.1 : ℂ)) * ((e x j : ℝ) : ℂ) ^ 2) := by
  unfold ez QF
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [reAt_eq, map_mul, map_div₀, map_ofNat, ← reAt_eq v (BF G x x), ← he]
  dsimp only
  rw [← Finset.mul_sum]
  push_cast
  simp only [sq]
  ring

theorem et_BF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (x y : κ → F) :
    et (BF G x y) = Complex.exp (2 * Real.pi * Complex.I * ∑ j : InfinitePlace F × κ, ((e x j * e y j : ℝ) : ℂ)) := by
  unfold et
  congr 2
  rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (BF G x y)).2, ← Complex.ofReal_sum,
    Fintype.sum_prod_type]
  simp only [he]

theorem const_eq (k t : ℕ) (a : F) (c : Fˣ) (z : Hn F) (d : ℝ)
    (hd : d = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F) :
    (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ))⁻¹ ^ k * ((d : ℂ)⁻¹ * (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))) ^ k)
      = wC k t a (c : F) := by
  have hP : (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => mul_ne_zero (by exact_mod_cast sg_ne c v) (z v).ne_zero
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
  have hN : (∏ v, (sg v (c : F) : ℂ)) = ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (c : F)).1, Complex.ofReal_prod]
    simp only [reAt_eq]
  have h : (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)))
      = (-Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) * ∏ v, (sg v (c : F) : ℂ) * (z v : ℂ) := by
    rw [← hN, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  rw [h, hd, wC]
  generalize (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) = P at hP
  push_cast
  rw [mul_pow _ P, mul_pow, ← pow_mul, mul_comm (Module.finrank ℚ F) k, div_eq_mul_inv, inv_pow]
  have : (P ^ k)⁻¹ * P ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  generalize (P ^ k)⁻¹ = Q at this
  generalize (_ * _ * _ : ℂ)⁻¹ = R
  linear_combination (R * ((-Complex.I) ^ (k * Module.finrank ℚ F) * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) ^ k)) * this

theorem wcos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  intro F _ _ _ κ _ _ G hG t ht k hk a c x₀ ha
  letI : DecidableEq (InfinitePlace F) := Classical.decEq _
  obtain ⟨e, B, α, β, he, hα, hβ, hB, hdet⟩ := GlobalTheory.T.exists_realMatrix_for_lattice_and_dual_with_det F κ G hG t ht k hk a ha
  have hsm := (GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG).2.1
  have hc : (c : F) ≠ 0 := c.ne_zero
  funext z
  have hz : ∀ v, 0 < ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)).im := fun v => by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero (sg_ne c v)) (z v).im_pos
  have hP := GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks (InfinitePlace F) κ k hk B hB (e x₀) (fun v => (sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)) hz
  have hL : ∀ Φ : (κ → F) → ℂ, (∀ x, x - x₀ ∈ aL κ a → Φ x = 1) → (∀ x, x - x₀ ∉ aL κ a → Φ x = 0) →
      th G Φ (HilbertThetaSeries.act (toInf (wm c)) z)
      = ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))⁻¹)
        * (((B *ᵥ fun i => (m i : ℝ)) j + e x₀ j : ℝ) : ℂ) ^ 2) := by
    intro Φ h1 h0
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (α m : κ → F) + x₀ := fun m n h =>
      α.injective (Subtype.ext (add_right_cancel h))
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun m => ?_
      rw [h1 _ (by rw [add_sub_cancel_right]; exact (α m).2), one_mul, ← one_mul (QF G _), ez_QF G e he, map_add (f := _), hα]
      simp only [act_wm, map_one, Complex.ofReal_one, one_mul, Pi.add_apply]
    · intro x hx
      have hx' : x - x₀ ∈ aL κ a := by
        by_contra h
        exact hx (by simp [h0 x h])
      exact ⟨α.symm ⟨_, hx'⟩, by simp⟩
  have hR : th G (wT G k t a c {x₀} fun _ => 1) z = wC k t a (c : F) *
      ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, ((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))
        * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * e x₀ j : ℝ) : ℂ)) := by
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (c : F) • (β m : κ → F) := fun m n h =>
      β.injective (Subtype.ext (smul_right_injective _ hc h))
    rw [← hinj.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun m => ?_
      have h1 : (a / (c : F)) • (c : F) • (β m : κ → F) ∈ dualL F G := by
        rw [smul_smul, div_mul_cancel₀ _ hc]
        exact (β m).2
      rw [wT, if_pos h1, Finset.sum_singleton, one_mul, (hsm _ _ x₀).1, (hsm _ _ x₀).2.1, mul_div_cancel_left₀ _ hc,
        ez_QF G e he, et_BF G e he, hβ, mul_assoc, mul_comm (Complex.exp _)]
      simp only [map_pow, Complex.ofReal_pow]
    · intro y hy
      have hy' : (a / (c : F)) • y ∈ dualL F G := by
        by_contra h
        exact hy (by simp [wT, h])
      refine ⟨β.symm ⟨(c : F)⁻¹ • y, by rwa [smul_smul, ← div_eq_mul_inv]⟩, ?_⟩
      simp [smul_smul, hc]
  unfold sl0
  simp only [denom_wm]
  rw [hL _ (fun x h => if_pos h) (fun x h => if_neg h), hP, hR, ← mul_assoc, const_eq k t a c z _ hdet]

end GlobalTheory.WCos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  first | exact @GlobalTheory.WCos.wcos | exact GlobalTheory.WCos.wcos | (intros; apply GlobalTheory.WCos.wcos <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticePeriodicFunctionRangeFinite
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem isSB_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ)
    (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  intro F _ _ κ _ _ N Φ hN hSB
  classical
  obtain ⟨hsupp, hper⟩ := hSB
  have memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k) := by
    intro y
    simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]
  have memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x := by
    intro c x
    simp [aL]
  have intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      IsIntegral ℤ (∑ i, c i • integralBasis F i) := by
    intro c
    have hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_integralBasis F).mp hmem
    rw [← ha]
    exact RingOfIntegers.isIntegral_coe a
  have decomp : ∀ z : F, IsIntegral ℤ z →
      ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z := by
    intro z hz
    have hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM : (0 : ℤ) < ((N * N : ℕ) : ℤ) := by positivity
  let g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ := fun r =>
    Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))
  refine ((Set.finite_range g).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases h0 : Φ x = 0
  · exact Or.inl h0
  right
  obtain ⟨y, hy, rfl⟩ := (memaL _ x).mp (hsupp x h0)
  have hyi := (memLL y).mp hy
  choose c hc using fun k => decomp (y k) (hyi k)
  have hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ) :=
    fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  refine ⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
  · have h2 := Int.emod_lt_of_pos (c k i) hM
    have h3 := hcast k i
    omega
  · show Φ (fun k => (N : F)⁻¹ *
        ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)
    simp only [hcast]
    have hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F) := by
      rw [memaL]
      refine ⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩
      · rw [memLL]
        intro k
        exact intB _
      · funext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [zsmul_eq_mul]
        have hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) +
            ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F) := by
          exact_mod_cast (Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm
        have key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF →
            (N : F) * (qF * integralBasis F i) =
              (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i) := by
          intro cF rF qF h
          rw [h]
          field_simp
          ring
        exact key _ _ _ hdiv
    have hp := hper (fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl
    rw [add_sub_cancel] at hp
    exact hp.symm

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_periodic_function_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ) (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)
end

