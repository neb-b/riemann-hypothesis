module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePow
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory.CoefHeight

open Polynomial

theorem val_coeff_prod_X_sub_C_le {K : Type} [Field K] (w : Valuation K ℝ≥0) {M : ℝ≥0} (hM : 1 ≤ M)
    (s : Multiset K) (hs : ∀ z ∈ s, w z ≤ M) (j : ℕ) :
    w ((s.map fun a => X - C a).prod.coeff j) ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha : w a ≤ M := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, w z ≤ M := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine (w.map_sub _ _).trans (max_le ?_ ?_)
    · cases j with
      | zero => rw [coeff_X_mul_zero, map_zero]; exact bot_le
      | succ i => rw [coeff_X_mul]; exact (ih hs' i).trans (pow_le_pow_right₀ hM (Nat.le_succ _))
    · rw [map_mul, pow_succ']
      exact mul_le_mul' ha (ih hs' j)

theorem nnnorm_coeff_minpoly_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ) :
    ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤
      max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set q := p.map (algebraMap F (FvBar F v)) with hqdef
  have hmon : q.Monic := (minpoly.monic hint).map _
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hq : q = (q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hmon
  have hroots : ∀ z ∈ q.roots, valBar F v z ≤ M := by
    intro z hz
    have hq0 : q ≠ 0 := hmon.ne_zero
    have hz' : aeval z p = 0 := by
      rw [mem_roots hq0, IsRoot, hqdef, eval_map_algebraMap] at hz; exact hz
    obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hz'
    have h1 : finEmb F v τ ((1 : v.adicCompletion F) ⊗ₜ[F] x) = z := by rw [finEmb_tmul, map_one, one_mul, hτ]
    show absBar F v z ≤ M
    rw [← h1]; exact (le_absFin F v τ _).trans (le_max_right _ _)
  have hcard : Multiset.card q.roots ≤ Module.finrank F E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdef, natDegree_map]; exact minpoly.natDegree_le x
  have key := val_coeff_prod_X_sub_C_le (valBar F v) hM q.roots hroots j
  rw [← hq] at key
  have hc : valBar F v (q.coeff j) = ‖algebraMap F (v.adicCompletion F) (p.coeff j)‖₊ := by
    show absBar F v _ = _
    rw [hqdef, coeff_map, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (FvBar F v), absBar_algebraMap]
  rw [← hc]
  exact key.trans (pow_le_pow_right₀ hM hcard)

end GlobalTheory.CoefHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

theorem polJ_aOf_eq_prod (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (_root_.GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen p q _ _ _ (_root_.GlobalTheory.PolarU.adMat_sq_mulVec_eigP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (_root_.GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem shc_pos (x : ℝ) : 0 < shc x := by
  unfold shc
  split_ifs with hx
  · exact one_pos
  · rcases lt_or_gt_of_ne hx with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

theorem polJ_conj {p q : ℕ} (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) (Y : Mat p q) :
    polJ (matG T k * Y * matG T k⁻¹) = polJ Y :=
  GlobalTheory.T.polarJacobian_blockDiag_conj_invariant p q _ _ Y (by rw [← matG_mul, mul_inv_cancel, matG_one]) hk ((Ksub T).inv_mem hk)

theorem exists_conj_aOf {p q : ℕ} (T : GrpData p q) {Y : Mat p q} (hY : Y ∈ pR p q) :
    ∃ k ∈ T.Kset, ∃ h : ℕ → ℝ, Y = matG T k * aOf p q h * matG T k⁻¹ := by
  obtain ⟨B, rfl⟩ := exists_pY hY
  obtain ⟨U, hU, V, hV, h, hB⟩ := _root_.GlobalTheory.RectSVD.exists_svd p q (Matrix.of B)
  obtain ⟨k, hk, hkm⟩ := _root_.GlobalTheory.PolarU.exists_lift_blocks p q T U hU V hV
  refine ⟨k, hk, h, ?_⟩
  rw [matG_inv_of_mem T hk, hkm, pY, hB]
  simp [aOf, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

theorem polJ_pos {p q : ℕ} (T : GrpData p q) (B : Fin p → Fin q → ℂ) : 0 < polJ (pY B) := by
  obtain ⟨k, hk, h, hB⟩ := exists_conj_aOf T (pY_mem B)
  rw [hB, polJ_conj T hk, polJ_aOf_eq_prod]
  exact Finset.prod_pos fun _ _ => shc_pos _

theorem cartan {p q : ℕ} (T : GrpData p q) (g : T.G) : ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  by_cases h : 1 ≤ p + q
  · exact (_root_.GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan p q h T).2 g
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    refine ⟨g * (T.expt (pY 0))⁻¹, ?_, pY 0, pY_mem 0, by simp⟩
    intro a
    rcases a with a | a <;> exact a.elim0

theorem isAddHaar_volume (p q : ℕ) : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem haar_polar {p q : ℕ} (T : GrpData p q) :
    ∃ (c : ℝ) (mK : Measure T.G), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (T.Kset)ᶜ = 0 ∧
    (∀ k ∈ T.Kset, Measure.map (fun x => k * x) mK = mK) ∧
    ∀ f : T.G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂T.haar = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ,
          (∫⁻ k, f (k * T.expt (pY B)) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  obtain ⟨-, hinv, hlc, hsc, ht2⟩ := _root_.GlobalTheory.coverUnitary_unimodular p q T
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ := _root_.GlobalTheory.exists_biinvariant_probability_on_compact_subgroup T.G (Ksub T) (_root_.GlobalTheory.PolarU.isCompact_Kset p q T)
  obtain ⟨L, hLc, hL⟩ := _root_.GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (_root_.GlobalTheory.PolarU.continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ p q _ (_root_.GlobalTheory.PolarU.SinhcPres.sAd_pY p q B)
  have hem : Measurable fun B : Fin p → Fin q → ℂ => T.expt (pY B) := (continuous_expt_pY T).measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.T.lintegral_haar_eq_compactSubgroup_transversal T.G (Fin p → Fin q → ℂ) T.haar mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) T.Kset (fun B => T.expt (pY B)) hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI := isAddHaar_volume p q
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ)) Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using polJ_pos T B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (matG T '' C)) :=
        (hC.image (continuous_matG T)).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact Units.isUnit _))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [matG_mul, matG_expt]
      exact hL _ B (matG_star_mul T hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := _root_.GlobalTheory.PolarU.exists_action_on_p p q T L hLc hL (cartan T) g
      refine ⟨ψ, hψc.measurable, _root_.GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := _root_.GlobalTheory.PolarU.jacobian_action_p p q (matG T g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := exists_blocks T hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg (matG T) h
          rwa [matG_mul, matG_mul, matG_expt, matG_expt, hm] at this)
        (fun B => by rw [hdet]; exact polJ_pos T B) (_root_.GlobalTheory.PolarU.SinhcPres.sAd_pY p q)
        (fun B => _root_.GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY p q B (_root_.GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × T.G => f (z.2 * T.expt (pY z.1)))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

theorem polar_coordinates : ∀ X : ProvA, CoverHaarIntegration X := by
  intro X p q
  refine ⟨haar_polar (X.grp p q), fun k hk Y _ => ?_, fun Y hY => ?_, fun h => ?_⟩
  · rw [← matG_inv]; exact polJ_conj _ hk Y
  · obtain ⟨k, hk, h, hY⟩ := exists_conj_aOf (X.grp p q) hY
    exact ⟨k, hk, h, by rw [← matG_inv]; exact hY⟩
  · rw [polJ_aOf_eq_prod, _root_.GlobalTheory.PolarU.RootProd.prod_shc_rootP]

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGL
section
open NumberField

noncomputable section
namespace GlobalTheory.RatCount
open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal

theorem nnnorm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) d = A i j
    simp [PiLp.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnNorm_single, nnNorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnNorm_apply_le _ i).trans h2

theorem htE_entry_le_heightGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N) :
    GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤
      GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  classical
  set x : E := (γ : Matrix (Fin N) (Fin N) E) i j with hx
  set g := Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ with hg
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro v
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    have he : ((bc (compFin F E v) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j = (1 : Fv F v) ⊗ₜ[F] x := by
      change compFin F E v ((1 : AF F) ⊗ₜ[F] x) = _
      simp [compFin, Algebra.TensorProduct.map_tmul]
    rw [← he]
    exact absFin_le_normFin F v _ i j
  have hinf : ∀ w : InfinitePlace F,
      max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) ≤ htInf F w (bc (compInf F E w) g) := by
    intro w
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    refine Finset.sup_le fun τ _ => ?_
    have he : (((bc (compInf F E w) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _).map (infEmb τ)) i j = τ.1 x := by
      change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
      simp [compInf, Algebra.TensorProduct.map_tmul, infEmb_tmul]
    rw [← he]
    exact (nnnorm_entry_le_opNorm _ i j).trans ((normInf_le_iff F w).1 le_rfl τ)
  unfold htE heightGL
  refine mul_le_mul' (Finset.prod_le_prod fun w _ => hinf w) ?_
  have hg' := finite_mulSupport_htFin F g
  refine finprod_le_finprod' (hg'.subset fun v hv hv' => hv ?_) hg' hfin
  exact le_antisymm ((hfin v).trans (le_of_eq hv')) (le_max_left _ _)

end GlobalTheory.RatCount
end
end

