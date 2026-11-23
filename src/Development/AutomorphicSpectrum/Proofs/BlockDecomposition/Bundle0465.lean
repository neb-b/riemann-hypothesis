module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
section
noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) K) 0 0 1 = 1 := by
  simp [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem neg_block_matrix {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_neg]
  rfl

theorem exists_blockMatrixTwoByTwoFin_eq {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    ∃ A B C D : Matrix (Fin n) (Fin n) K, g = blk4 A B C D := by
  refine ⟨(g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem is_siegel_parabolic_block_iff {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 a b c d) ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    have h' := h i j
    simpa only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using h'
  · rintro rfl i j
    simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]

theorem det_block_lower_zero {n : ℕ} (a b d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b 0 d).det = a.det * d.det := by
  simp only [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

section cT
variable (σ : K →+* K)

theorem cT_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  unfold cT; simp

theorem cT_zero {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  unfold cT; simp

theorem cT_neg {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_sub {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

theorem det_cT {a : ℕ} (x : Matrix (Fin a) (Fin a) K) : (cT σ x).det = σ x.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_cT {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : IsUnit (cT σ x).det := by
  rw [det_cT]; exact hx.map σ

theorem cT_inv {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : cT σ x⁻¹ = (cT σ x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hx, cT_one]

theorem cT_blk4 {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end cT

theorem Jm_mul_Jm (n : ℕ) : Jm K n * Jm K n = -1 := by
  rw [Jm, submatrix_fromBlocks_mul, ← block_matrix_one (K := K), neg_block_matrix]
  congr 1 <;> simp

theorem unitary_left_inv (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : (-(Jm K n * cT σ g * Jm K n)) * g = 1 := by
  unfold IsUnitary at hg
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g), hg, Jm_mul_Jm, neg_neg]

theorem isUnit_det_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (unitary_left_inv σ hg)

theorem inv_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : g⁻¹ = -(Jm K n * cT σ g * Jm K n) :=
  Matrix.inv_eq_left_inv (unitary_left_inv σ hg)

theorem unitary_mul (σ : K →+* K) {N : ℕ} {J g h : Matrix (Fin N) (Fin N) K}
    (hg : IsUnitary σ J g) (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul, show cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h by
    simp only [Matrix.mul_assoc], hg, hh]

section eId

theorem eId_mul_eId (n r : ℕ) : eId K n r * eId K n r = eId K n r := by
  rw [eId, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem cT_eId (σ : K →+* K) (n r : ℕ) : cT σ (eId K n r) = eId K n r := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, eId, Matrix.diagonal_apply, apply_ite σ]
  · simp [cT, eId, Matrix.diagonal_apply, h, Ne.symm h]

theorem eId_mul_extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : eId K n r * extB b = extB b := by
  ext i j
  simp only [eId, Matrix.diagonal_mul, extB]
  split_ifs <;> simp_all

theorem extB_mul_eId {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : extB b * eId K n r = extB b := by
  ext i j
  simp only [eId, Matrix.mul_diagonal, extB]
  split_ifs <;> simp_all

theorem cT_extB (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    cT σ (extB (n := n) b) = extB (cT σ b) := by
  ext i j
  simp only [cT, extB, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp_all

theorem extB_injective {n r : ℕ} (hr : r ≤ n) {b b' : Matrix (Fin r) (Fin r) K}
    (h : extB (n := n) b = extB b') : b = b' := by
  ext i j
  have h' := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  simpa [extB] using h'

end eId

theorem repMat_eq (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    repMat σ b a = blk4 ((1 - eId K n r) * a) (eId K n r * (cT σ a)⁻¹) (-(eId K n r * a))
      ((1 - eId K n r - extB b) * (cT σ a)⁻¹) := by
  rw [repMat, wr, nB, mA, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  congr 1 <;> simp [sub_mul, mul_sub, add_mul, eId_mul_extB] <;> abel

end GlobalTheory.CompanionTheory.BruhatCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicRestrictionMeasure
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GrowthHaar

theorem isHaarMeasure_map_restrict (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [MeasurableSpace (AutomorphicForm.archGroup E a)]
    [BorelSpace (AutomorphicForm.archGroup E a)] (U : Set (AdelicGLn.FiniteAdelicGL E a))
    (hUc : IsCompact U) (hU1 : U ∈ 𝓝 (1 : AdelicGLn.FiniteAdelicGL E a)) :
    ((μ.restrict ((fun h : GA E a => (AdelicGLn.prodEquiv E a h).2) ⁻¹' U)).map
      (fun h : GA E a => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1)).IsHaarMeasure := by
  haveI : T2Space (AdelicGLn.FiniteAdelicGL E a) := inferInstance
  haveI : T2Space (AutomorphicForm.archGroup E a) := inferInstance
  haveI : BorelSpace (GA E a) := inferInstance
  set q : GA E a → AdelicGLn.FiniteAdelicGL E a := fun h => (AdelicGLn.prodEquiv E a h).2 with hq_def
  set p : GA E a → AutomorphicForm.archGroup E a :=
    fun h => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1 with hp_def
  have hΦ : Continuous (AdelicGLn.prodEquiv E a) := (AdelicGLn.prodEquiv E a).continuous
  have hq : Continuous q := continuous_snd.comp hΦ
  have hp : Continuous p := (AutomorphicForm.archEquiv E a).continuous.comp (continuous_fst.comp hΦ)
  have hpm : Measurable p := hp.measurable
  have hS : MeasurableSet (q ⁻¹' U) := (hUc.isClosed.preimage hq).measurableSet
  have happly : ∀ B : Set (AutomorphicForm.archGroup E a), MeasurableSet B →
      ((μ.restrict (q ⁻¹' U)).map p) B = μ (p ⁻¹' B ∩ q ⁻¹' U) := fun B hB => by
    rw [Measure.map_apply hpm hB, Measure.restrict_apply (hpm hB)]
  have h1 : IsFiniteMeasureOnCompacts ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun K hK => ?_⟩
    rw [happly K hK.isClosed.measurableSet]
    have hK' : IsCompact ((AutomorphicForm.archEquiv E a).symm '' K) :=
      hK.image (AutomorphicForm.archEquiv E a).symm.continuous
    have hc : IsCompact (p ⁻¹' K ∩ q ⁻¹' U) := by
      have : p ⁻¹' K ∩ q ⁻¹' U = (AdelicGLn.prodEquiv E a).symm ''
          (((AutomorphicForm.archEquiv E a).symm '' K) ×ˢ U) := by
        ext h
        constructor
        · rintro ⟨hk, hu⟩
          exact ⟨AdelicGLn.prodEquiv E a h,
            ⟨⟨_, hk, (AutomorphicForm.archEquiv E a).symm_apply_apply _⟩, hu⟩,
            (AdelicGLn.prodEquiv E a).symm_apply_apply h⟩
        · rintro ⟨⟨x, y⟩, ⟨⟨k, hk, rfl⟩, hy⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · simpa [hp_def] using hk
          · simpa [hq_def] using hy
      rw [this]
      exact (hK'.prod hUc).image (AdelicGLn.prodEquiv E a).symm.continuous
    exact hc.measure_lt_top
  have hpL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      p (AutomorphicForm.infEmb E a s * h) = s * p h := fun s h => by
    simp [hp_def, AutomorphicForm.prodEquiv_infEmb]
  have hqL : ∀ (s : AutomorphicForm.archGroup E a) (h : GA E a),
      q (AutomorphicForm.infEmb E a s * h) = q h := fun s h => by
    simp [hq_def, AutomorphicForm.prodEquiv_infEmb]
  have h2 : Measure.IsMulLeftInvariant ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun s => ?_⟩
    have hms : Measurable fun x : AutomorphicForm.archGroup E a => s * x :=
      (continuous_const.mul continuous_id).measurable
    ext B hB
    rw [Measure.map_apply hms hB, happly _ (hms hB), happly B hB,
      ← measure_preimage_mul μ (AutomorphicForm.infEmb E a s) (p ⁻¹' B ∩ q ⁻¹' U)]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, hpL, hqL]
  have h3 : Measure.IsOpenPosMeasure ((μ.restrict (q ⁻¹' U)).map p) := by
    refine ⟨fun O hO ⟨s, hs⟩ => ?_⟩
    rw [happly O hO.measurableSet]
    have hV : IsOpen (p ⁻¹' O ∩ q ⁻¹' interior U) :=
      (hO.preimage hp).inter (isOpen_interior.preimage hq)
    have hne : (p ⁻¹' O ∩ q ⁻¹' interior U).Nonempty := by
      refine ⟨AutomorphicForm.infEmb E a s, ?_, ?_⟩
      · simpa [hp_def, AutomorphicForm.prodEquiv_infEmb] using hs
      · simpa [hq_def, AutomorphicForm.prodEquiv_infEmb] using mem_interior_iff_mem_nhds.2 hU1
    refine fun h0 => hV.measure_ne_zero μ hne (measure_mono_null ?_ h0)
    exact Set.inter_subset_inter_right _ (Set.preimage_mono interior_subset)
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

end GlobalTheory.CompanionTheory.GrowthHaar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_growth_bound : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsCompact (K : Set (G2 σ Y)) → IsHgt K a → (∀ x, 0 < a x) → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | exact GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow | (intros; apply GlobalTheory.CompanionTheory.EisTerm.flat_norm_le_height_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameBlockZeroStabilizesFlag
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem frameIdem_inl_mulVec {E : Type} [Field E] {n r : ℕ} (S : E →+* E)
    (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (v : Fin n → E) :
    frameIdem S J X Y (some (Sum.inl i)) *ᵥ v = fun a => X a i * ((cT S Y * J) *ᵥ v) i := by
  funext a
  simp only [frameIdem]
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, ite_and]

theorem stabilises_flag_span : ∀ (E : Type) [Field E] (S : E →+* E) (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E), cT S Y * J * X = 1 → ∀ (g : Matrix (Fin n) (Fin n) E) (j : Fin r), (∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 → frameIdem S J X Y α * g * frameIdem S J X Y β = 0) → ∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0 := by
  intro E _ S n r J X Y hXY g j hg l hl
  have hcol : (fun a => X a l) = X *ᵥ Pi.single l 1 := by
    funext a; simp
  have hx : frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l) = fun a => X a l := by
    rw [frameIdem_inl_mulVec, hcol, Matrix.mulVec_mulVec, hXY]
    funext a; simp
  have hβ : frameLev j (some (Sum.inl l) : FrameIx r) = 2 := by simp [frameLev, hl]
  set v : Fin n → E := g *ᵥ (fun a => X a l) with hv
  have hz : ∀ α : FrameIx r, frameLev j α < 2 → frameIdem S J X Y α *ᵥ v = 0 := by
    intro α hα
    have := hg α _ hα hβ
    calc frameIdem S J X Y α *ᵥ v
        = frameIdem S J X Y α *ᵥ (g *ᵥ (frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l))) := by
          rw [hx]
      _ = (frameIdem S J X Y α * g * frameIdem S J X Y (some (Sum.inl l))) *ᵥ (fun a => X a l) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [this, Matrix.zero_mulVec]
  have hsum : v = ∑ α, frameIdem S J X Y α *ᵥ v := by
    have h1 : (∑ α, frameIdem S J X Y α) *ᵥ v = ∑ α, frameIdem S J X Y α *ᵥ v :=
      map_sum (Matrix.mulVec.addMonoidHomLeft v) (fun α => frameIdem S J X Y α) Finset.univ
    rwa [sum_frameIdem, Matrix.one_mulVec] at h1
  refine ⟨fun m => if m ≤ j then ((cT S Y * J) *ᵥ v) m else 0, ?_, fun m hm => if_neg (not_le.2 hm)⟩
  refine hsum.trans ?_
  rw [Fintype.sum_option, Fintype.sum_sum_type, hz none (by simp [frameLev]), zero_add]
  have hinr : ∑ i, frameIdem S J X Y (some (Sum.inr i)) *ᵥ v = 0 := by
    refine Finset.sum_eq_zero fun i _ => hz _ ?_
    by_cases h : i ≤ j <;> simp [frameLev, h]
  rw [hinr, add_zero]
  funext a
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j
  · have := congrFun (frameIdem_inl_mulVec S J X Y i v) a
    simp only [Matrix.mulVec, dotProduct] at this
    simpa [h] using this
  · have h0 := congrFun (hz (some (Sum.inl i)) (by simp [frameLev, h])) a
    simp only [Matrix.mulVec, dotProduct] at h0
    simpa [h] using h0

end GlobalTheory.CompanionTheory.RapidDecay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUniqueStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_fixes_root_unique : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) (φ : G F Ω) → ∀ N : ℕ, 0 < N → ∀ ξ : Ω, IsPrimitiveRoot ξ (normV v ^ N - 1) → ∀ (a : ℕ) (t i : Dec (F := F) A), a < N → (i : G F Ω) ∈ Ine (F := F) A → ((φ ^ a * t ^ N * i : Dec (F := F) A) : G F Ω) ξ = ξ → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | exact GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot | (intros; apply GlobalTheory.CompanionTheory.TameAction.eq_zero_of_fixes_primitiveRoot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUnique
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.ArtinMapUniq

open PositivityTheory.FamInh

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_ideal_ramificationIdx (L : Type) [Field L] [NumberField L] [Algebra E L] :
    ∃ 𝔡 : Ideal (𝓞 E), 𝔡 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 L)),
      ¬ v.asIdeal ∣ 𝔡 → w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  refine ⟨(differentIdeal (𝓞 E) (𝓞 L)).under (𝓞 E), ?_, fun v w hv hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 E) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem res_unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (v : HeightOneSpectrum (𝓞 E)) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (w : HeightOneSpectrum (𝓞 L)) (hw : IsPlaceOver A w)
    [w.asIdeal.LiesOver v.asIdeal] (hr : w.asIdeal.ramificationIdx (𝓞 E) = 1)
    {x : (v.adicCompletion E)ˣ} (hx : IsUnifAt v x) :
    res L (art (localIdele E v x)) = res L (art' (localIdele E v x)) := by
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨σ', hσ', e'⟩ := (ha'.frob v A hA _).mp ⟨x, hx, rfl⟩
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia (res_isArithFrobAt hw hσ')
  rw [(inertia_eq_bot_iff v w).2 hr, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [← e, ← e', map_inv, map_inv, map_inv, map_inv, res_toAb, res_toAb, h]

theorem res_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (x : Ideles E) : res L (art x) = res L (art' x) := by
  have := isAlgClosure_top L
  letI : CommGroup (L ≃ₐ[E] L) :=
    { (inferInstance : Group (L ≃ₐ[E] L)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := L ≃ₐ[E] L)).comm a b }
  have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
  have : IsTopologicalGroup (L ≃ₐ[E] L) := inferInstance
  let f : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art
  let f' : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art'
  have hf : Continuous f := (continuous_res L).comp ha.quot.continuous
  have hf' : Continuous f' := (continuous_res L).comp ha'.quot.continuous
  have hk : ∀ b : Ideles E →* Gab E Ω, IsGlobalArtin b → ∀ k, b (diagUnits E k) = 1 := fun b hb k => by
    have hk : diagUnits E k ∈ b.ker := by
      rw [hb.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_ramificationIdx (E := E) L
  have hψ := GlobalTheory.FrobDense.eq_one_of_away (f * f'⁻¹) (hf.mul hf'.inv) (fun k => by
      simp [f, f', hk _ ha k, hk _ ha' k]) (Ideal.finite_factors (I := 𝔡) h𝔡).toFinset fun v hv => by
    refine GlobalTheory.FrobDense.eq_one_of_unif ((f * f'⁻¹).comp (localIdele E v)) fun y hy => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    have hv' : ¬ v.asIdeal ∣ 𝔡 := by simpa using hv
    have e := res_unif_eq ha ha' L v hA w hw (hun v w hv' hwv) hy
    simp [f, f', e]
  have := DFunLike.congr_fun hψ x
  simpa [f, f', mul_inv_eq_one] using this

theorem eq_inv_arithmetic_artin_map : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  intro E Ω _ _ _ _ _ art ha
  ext x
  have ha0 : IsGlobalArtin (art0 E Ω)⁻¹ := by
    refine ⟨(Homeomorph.inv (Gab E Ω)).isOpenQuotientMap.comp (isOpenQuotientMap_art0 E Ω),
      ?_, ?_, ?_, ?_⟩
    · rw [← ker_art0 E Ω]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    · intro v A hA g
      simp only [MonoidHom.inv_apply, inv_eq_iff_eq_inv]
      rw [art0_unit_iff hA, Subgroup.inv_mem_iff]
      rfl
    · intro v A hA g
      simp only [MonoidHom.inv_apply, map_inv, inv_eq_iff_eq_inv]
      exact art0_unif_iff hA _
    · intro v A hA
      rw [← closure_range_eq hA]
      congr 1
      ext g
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
  have h : art x * ((art0 E Ω)⁻¹ x)⁻¹ ∈ (⊥ : Subgroup (Gab E Ω)) :=
    mem_of_forall_res (H := ⊥) isClosed_singleton fun L _ _ _ => by
      rw [map_mul, map_inv, res_eq ha ha0 L x, mul_inv_cancel]
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at h

end GlobalTheory.CompanionTheory.ArtinMapUniq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOneStatement
section
theorem GlobalTheory.T.inducedFunction_at_one :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ),
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 :=
  GlobalTheory.CompanionTheory.ModelS.fRaw_one
end

