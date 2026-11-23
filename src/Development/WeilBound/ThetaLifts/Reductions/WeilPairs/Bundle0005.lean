module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}

theorem hOF_eq_trace {m : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin m) (Fin m) E) (x y : WOF F E nS m) :
    hOF σ JS J x y = (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * J.map (incAF F E) * x)).trace := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dC_dual (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    (dC E nT)ᵀ * GlobalTheory.WeilSchrodinger.DblTargetF.dblG J * dCdE J = 1 := by
  have e : GlobalTheory.WeilSchrodinger.DblTargetF.dblG J = (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  rw [e, dCdE, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), ← add_smul]
  norm_num

theorem dC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (dC R n).map φ = dC S n := by
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dC, diagCols, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases k with k | k <;> simp [Matrix.one_apply, apply_ite φ]

theorem hOF_dual (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (v y : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dCd F J * v) (dC (AF F ⊗[F] E) nT * y) =
      (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * v)).trace := by
  have h := congrArg (fun M : Matrix (Fin nT) (Fin nT) E => M.map (incAF F E)) (dC_dual J hJ)
  simp only [Matrix.map_mul, Matrix.transpose_map, dC_map] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (dCd F J), ← Matrix.mul_assoc (dC _ nT)ᵀ, ← Matrix.mul_assoc (dC _ nT)ᵀ]
  rw [show (dC (AF F ⊗[F] E) nT)ᵀ * (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) * dCd F J = 1 from h,
    Matrix.one_mul]

theorem phase_move (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (s : GL (Fin nT) (AF F ⊗[F] E)) (y w : WOF F E nS nT) :
    phase σ JS J ξ₀ ψ ((s⁻¹).1 * y) ((s.1.map (cAF σ))ᵀ * w) = phase σ JS J ξ₀ ψ y w := by
  unfold phase symplOF
  rw [hOF_dual JS J hJ, hOF_dual JS J hJ, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (s.1.map (cAF σ))ᵀ, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]


variable (F E nS nT) in
def vecE : WOF F E nS nT ≃+ (Fin (nT * nS) → AF F ⊗[F] E) where
  toFun w k := w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun u i j := u (finProdFinEquiv (i, j))
  left_inv w := by ext i j; simp only [Equiv.symm_apply_apply]
  right_inv u := by ext k; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' _ _ := rfl

theorem integral_mul (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure) (A : GL (Fin nT) (AF F ⊗[F] E))
    (g : WOF F E nS nT → ℂ) : ∫ w, g (A.1 * w) ∂ν =
      ((((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (Matrix.GeneralLinearGroup.det A)) : ℝ) ^ nS)⁻¹ : ℝ) : ℂ) * ∫ w, g w ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  have : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  have c1 : Continuous (vecE F E nS nT) :=
    continuous_pi fun k => (continuous_apply (finProdFinEquiv.symm k).2).comp (continuous_apply (finProdFinEquiv.symm k).1)
  have c2 : Continuous (vecE F E nS nT).symm := continuous_pi fun i => continuous_pi fun j => continuous_apply _
  let eh : WOF F E nS nT ≃ₜ (Fin (nT * nS) → AF F ⊗[F] E) := .mk (vecE F E nS nT).toEquiv c1 c2
  let em := eh.toMeasurableEquiv
  let K : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) → Matrix (Fin (nT * nS)) (Fin (nT * nS)) (AF F ⊗[F] E) :=
    fun M => (M ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E))).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  have hK : ∀ M M', M * M' = 1 → K M * K M' = 1 := fun M M' h => by
    simp only [K]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv]
  let t : GL (Fin (nT * nS)) (AF F ⊗[F] E) := ⟨K A.1, K (A⁻¹).1, hK _ _ A.mul_inv, hK _ _ A.inv_mul⟩
  have hd : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det A ^ nS := by
    ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show (K A.1).det = _
    simp only [K]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_fin]
  have hv : ∀ w : WOF F E nS nT, (vecE F E nS nT).symm (t.1 *ᵥ vecE F E nS nT w) = A.1 * w := fun w => by
    ext i j
    show ∑ k, K A.1 (finProdFinEquiv (i, j)) k * vecE F E nS nT w k = ∑ k, A.1 i k * w k j
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ b, K A.1 (finProdFinEquiv (i, j)) (finProdFinEquiv (a, b)) *
      w (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1 (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = _
    simp only [K, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simp
  have h := GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E _ t (ν.map em) ((vecE F E nS nT).isAddHaarMeasure_map ν c1 c2)
    (fun u => g ((vecE F E nS nT).symm u))
  rw [integral_map_equiv, integral_map_equiv, hd, map_pow, map_pow, NNReal.coe_pow] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext w
    exact congrArg g (hv w).symm
  · congr 2
    funext w
    exact congrArg g ((vecE F E nS nT).symm_apply_apply w)

end

theorem change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem relIndex_ne_zero_of_compact {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H K : AddSubgroup G) (hK : IsCompact (K : Set G)) {V : Set G} (hV : V ∈ 𝓝 (0 : G))
    (h : ∀ u ∈ V, u ∈ K → u ∈ H) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1 : ((H.addSubgroupOf K : AddSubgroup K) : Set K) ∈ 𝓝 (0 : K) := by
    have h2 : (Subtype.val ⁻¹' V : Set K) ∈ 𝓝 (0 : K) := continuous_subtype_val.continuousAt.preimage_mem_nhds hV
    exact Filter.mem_of_superset h2 fun u hu => h u.1 hu u.2
  haveI := AddSubgroup.quotient_finite_of_isOpen (H.addSubgroupOf K) (AddSubgroup.isOpen_of_mem_nhds _ h1)
  exact AddSubgroup.index_ne_zero_of_finite

theorem ft_mem {α : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F) {γ : Matrix (Fin nT) (Fin nS) E} (hγ : γ ∈ Λ) :
    algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) γ ∈ latOF F E nS nT Λ :=
  AddSubgroup.subset_closure ⟨α, hα, γ, hγ, rfl⟩

theorem hOF_rat (M N : Matrix (Fin nT) (Fin nS) E) :
    hOF σ JS JT (ratWF (F := F) M) (ratWF (F := F) N) = incAF F E (hRatF σ JS JT M N) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hOF, hRatF, ratWF, Matrix.map_apply, GlobalTheory.HeisLineF.cAF_incAF, map_sum, map_mul]

theorem sympl_ft (hσ : ∀ x, σ (σ x) = x) (α β : Af F) (M N : Matrix (Fin nT) (Fin nS) E) :
    symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      pairA F 0 (α * β * algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT M N))) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : hOF σ JS JT (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N)) := by
    rw [hOF_smul_left, ← hOF_rat, ← hOF_smul_right σ JS JT hσ (algebraMap (AF F) (AEF F E) (pairA F 0 β)),
      GlobalTheory.HeisThetaF.cAF_algebraMap]
  have e2 : incAF F E ξ₀ * (algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N))) = (pairA F 0 α * pairA F 0 β) ⊗ₜ[F] (ξ₀ * hRatF σ JS JT M N) := by
    show ((1 : AF F) ⊗ₜ[F] ξ₀) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((pairA F 0 β ⊗ₜ[F] (1 : E)) *
      ((1 : AF F) ⊗ₜ[F] hRatF σ JS JT M N))) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [symplOF, e, e2, GlobalTheory.LatVac.trace_tmul]
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) * 0 * _ = 0
  rw [zero_mul, zero_mul]

theorem hRatF_smul (c : E) (M N : Matrix (Fin nT) (Fin nS) E) : hRatF σ JS JT (c • M) N = c * hRatF σ JS JT M N := by
  simp only [hRatF, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem psi_ft (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {α β : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F)
    (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf F) {M N : Matrix (Fin nT) (Fin nS) E} (hM : M ∈ Λ) (hN : N ∈ Λ) :
    ψ (symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N)) = 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [sympl_ft hσ]
  refine PositivityTheory.ThKG.Tow.Pln.psi_int hψ _ (fun a => ?_) _ (fun v => mul_mem (hα v) (hβ v))
  obtain ⟨n, hn⟩ := (h _).1 (Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) hM) N hN
  refine ⟨n, ?_⟩
  have e : algebraMap (𝓞 F) (𝓞 E) a • M = algebraMap F E (a : F) • M := rfl
  rw [← hn, e, hRatF_smul, ← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def, mul_left_comm]

theorem psi_lat (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {x y : WOF F E nS nT}
    (hx : x ∈ latOF F E nS nT Λ) (hy : y ∈ latOF F E nS nT Λ) : ψ (symplOF σ JS JT ξ₀ x y) = 1 := by
  have z1 : ∀ y, symplOF σ JS JT ξ₀ (0 : WOF F E nS nT) y = 0 := fun y => by
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y
    rw [add_zero] at this
    exact left_eq_add.1 this
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, M, hM, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, N, hN, rfl⟩ := hy
      exact psi_ft hσ hψ h hα hβ hM hN
    | zero => rw [GlobalTheory.HeisLineF.symplOF_zero_right, AddChar.map_zero_eq_one]
    | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_right, AddChar.map_add_eq_mul, hu, hv, one_mul]
    | neg u _ hu =>
      have := GlobalTheory.HeisLineF.symplOF_add_right σ JS JT ξ₀
        (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M) u (-u)
      rw [add_neg_cancel, GlobalTheory.HeisLineF.symplOF_zero_right] at this
      have h2 := congrArg ψ this
      rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
      exact h2.symm
  | zero => rw [z1, AddChar.map_zero_eq_one]
  | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, hu, hv, one_mul]
  | neg u _ hu =>
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ u (-u) y
    rw [add_neg_cancel, z1] at this
    have h2 := congrArg ψ this
    rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
    exact h2.symm

theorem one_int : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem lat_sd (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (hg : GoodLat Λ) (h : RatSD σ JS JT ξ₀ Λ) :
    SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  intro x
  refine ⟨fun hx a ha => psi_lat hσ hψ h hx ha, fun H => ?_⟩
  obtain ⟨γ, hγ⟩ := lat_approx hg (x : WOF F E nS nT) x.fin
  have hΛ : γ ∈ Λ := (h γ).2 fun N hN => by
    have h1 := ft_mem (F := F) one_int hN
    have h2 : ψ (symplOF σ JS JT ξ₀ (x : WOF F E nS nT) _) = 1 := H (XFF.mk _ (lat_fin h1)) h1
    have h3 := psi_lat (JS := JS) (JT := JT) (ξ₀ := ξ₀) hσ hψ h hγ h1
    rw [← sub_add_cancel (x : WOF F E nS nT) (algebraMap (AF F) (AEF F E) (pairA F 0 1) • ratWF (F := F) γ),
      GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, XFF.coe_mk, h3, one_mul, sympl_ft hσ, one_mul, one_mul,
      PositivityTheory.ThKG.Tow.Pln.psi_fin_rat hψ, Algebra.trace_trace, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have h4 : ((Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT γ N) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]; ring
    exact_mod_cast h4
  have h5 := add_mem hγ (ft_mem (F := F) one_int hΛ)
  rw [sub_add_cancel] at h5
  exact h5

theorem continuous_mtF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (mtF (F := F) σ J) ∧ Continuous fun g : GAF (F := F) σ J => mtF σ J g⁻¹ :=
  ⟨Units.continuous_val.comp continuous_subtype_val, Units.continuous_coe_inv.comp continuous_subtype_val⟩

theorem continuous_act : Continuous fun z : (GAF (F := F) σ JS × GAF (F := F) σ JT) × WOF F E nS nT =>
    actOF σ JS JT z.1.1 z.1.2 z.2 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((continuous_mtF JS).2.comp (continuous_fst.comp continuous_fst))

theorem continuous_act_left (x : WOF F E nS nT) :
    Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp continuous_snd).matrix_mul continuous_const).matrix_mul
    ((continuous_mtF JS).2.comp continuous_fst)

theorem continuous_act_right (g : GAF (F := F) σ JS) (h : GAF (F := F) σ JT) :
    Continuous fun x : WOF F E nS nT => actOF σ JS JT g h x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem idx_ne_zero (hg : GoodLat Λ) (B : Submodule (𝓞 E) (XFF F E nS nT)) (φ : WOF F E nS nT →+ WOF F E nS nT)
    (hφ : Continuous φ) (h1 : ∀ l ∈ latOF F E nS nT Λ, (φ l).map (infPartF F E) = 0)
    (h2 : ∀ b ∈ B, ∃ l ∈ latOF F E nS nT Λ, φ l = b) : idx (latF F E nS nT Λ) B ≠ 0 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have e : idx (latF F E nS nT Λ) B = (latOF F E nS nT Λ).relIndex (B.toAddSubgroup.map (XFF.incl F E nS nT)) :=
    AddSubgroup.relIndex_comap (latOF F E nS nT Λ) (XFF.incl F E nS nT) B.toAddSubgroup
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h3 := relIndex_ne_zero_of_compact (latOF F E nS nT Λ) ((latOF F E nS nT Λ).map φ)
    ((lat_compact hg).image hφ) hV (by rintro _ hu ⟨l, hl, rfl⟩; exact hV' _ hu (h1 l hl))
  rw [e]
  refine fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨b, hb, rfl⟩
  exact h2 b hb

theorem lat_lev (hg : GoodLat Λ) (U : AddSubgroup (WOF F E nS nT)) (hU : IsOpen (U : Set (WOF F E nS nT))) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latOF F E nS nT Λ, N • u ∈ U := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h := relIndex_ne_zero_of_compact U (latOF F E nS nT Λ) (lat_compact hg) (hU.mem_nhds U.zero_mem)
    fun u hu _ => hu
  exact ⟨_, Nat.pos_of_ne_zero h, fun u hu => AddSubgroup.nsmul_relIndex_mem U hu⟩

theorem nsmul_inv_smul {M : Type} [AddCommGroup M] [Module (AEF F E) M] {N : ℕ} (hN : 0 < N) (x : M) :
    N • (incAF F E (N : E)⁻¹ • x) = x := by
  have h : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← Nat.cast_smul_eq_nsmul (AEF F E), smul_smul, ← map_natCast (incAF F E) N, ← map_mul, mul_inv_cancel₀ h, map_one,
    one_smul]

theorem fin_smul (a : AEF F E) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : (a • u).map (infPartF F E) = 0 :=
  (finSubF F E nS nT).smul_mem a hu

theorem near (hg : GoodLat Λ) : ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT),
    ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h := (lat_compact (F := F) hg).eventually_forall_of_forall_eventually
    (x₀ := (1 : GAF (F := F) σ JS × GAF (F := F) σ JT)) (P := fun p y => actOF σ JS JT p.1 p.2 y - y ∈ V) fun y _ => by
      have h1 := ((continuous_act (σ := σ) (JS := JS) (JT := JT)).sub continuous_snd).continuousAt
        (x := ((1 : GAF (F := F) σ JS × GAF (F := F) σ JT), y))
      refine h1.preimage_mem_nhds ?_
      show V ∈ 𝓝 (actOF σ JS JT 1 1 y - y)
      rw [actOF_one, sub_self]
      exact hV
  filter_upwards [h] with p hp a ha
  have h2 := hV' _ (hp a ha) (rhoFF σ JS JT p a - a).fin
  have h3 := add_mem h2 (show (a : WOF F E nS nT) ∈ latOF F E nS nT Λ from ha)
  rw [sub_add_cancel] at h3
  exact h3

theorem near' (hg : GoodLat Λ) (x : XFF F E nS nT) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT), ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h0 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x) :=
    by
      have h00 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x :=
        continuous_act_left _
      have h01 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x - x :=
        h00.sub continuous_const
      exact h01.const_smul (incAF F E (N : E)⁻¹)
  have h1 : (fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x)) ⁻¹' V ∈ 𝓝 1 := by
    refine h0.continuousAt.preimage_mem_nhds ?_
    show V ∈ 𝓝 (incAF F E (N : E)⁻¹ • (actOF σ JS JT 1 1 x - x))
    rw [actOF_one, sub_self, smul_zero]
    exact hV
  filter_upwards [h1] with p hp
  refine ⟨incAF F E (N : E)⁻¹ • (rhoFF σ JS JT p x - x), hV' _ hp (XFF.fin _), ?_⟩
  rw [nsmul_inv_smul hN, add_sub_cancel]

end LatC

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SymplOHF
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heis_C {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

