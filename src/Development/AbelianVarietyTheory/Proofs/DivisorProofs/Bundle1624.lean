module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormula
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.WeylMeas

open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_meas : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  intro F _ _ ψ hψ hunr hne κ _
  classical
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI hB : ∀ v : Pl (F := F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI hSC : ∀ v : Pl (F := F), SecondCountableTopology (Fv F v) := fun v => GlobalTheory.SplitWeil.secondCountable _
  haveI hH : ∀ v : Pl (F := F), (measV ψ v).IsAddHaarMeasure := fun v => (isSelfDualFor_measV ψ hψ.1 v (hne v)).1
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  have hOint : ∀ v : Pl (F := F), (v.adicCompletionIntegers F : Set (Fv F v)) =
      ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := fun v => by
    ext x; exact (GlobalTheory.WeylFour.IndOSelf.mem_int_iff x).symm
  have hOc : ∀ v : Pl (F := F), IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isCompact_int _
  have hOo : ∀ v : Pl (F := F), IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isOpen_int _
  have hOpi : ∀ v : Pl (F := F), {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    ext x; simp
  have hOm : ∀ v : Pl (F := F), MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun v => by
    rw [hOpi v]; exact MeasurableSet.univ_pi fun _ => (hOo v).measurableSet
  set c : Pl (F := F) → ℝ≥0∞ := fun v =>
    (Measure.pi fun _ : κ => measV ψ v) {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} with hcdef
  have hcpi : ∀ v, c v = ∏ _i : κ, measV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    simp only [c]; rw [hOpi v, Measure.pi_pi]
  have hc0 : ∀ v, c v ≠ 0 := fun v => by
    rw [hcpi v]
    exact Finset.prod_ne_zero_iff.2 fun _ _ =>
      ((hOo v).measure_pos (measV ψ v) ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hct : ∀ v, c v ≠ ⊤ := fun v => by
    rw [hcpi v]
    exact ENNReal.prod_ne_top fun _ _ => (hOc v).measure_lt_top.ne
  have hc1 : ∀ v, PsiUnr ψ v → c v = 1 := fun v hv => by
    have h1 := (GlobalTheory.WeylFour.IndOSelf.isUnitVol_measV ψ v hv).2
    rw [← hOint v] at h1
    rw [hcpi v, h1, Finset.prod_const_one]
  set μv : ∀ v : Pl (F := F), Measure (κ → Fv F v) := fun v => (c v)⁻¹ • Measure.pi fun _ : κ => measV ψ v with hμvdef
  haveI hμvH : ∀ v, (μv v).IsAddHaarMeasure := fun v =>
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (hct v)) (ENNReal.inv_ne_top.2 (hc0 v))
  have hμv1 : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := fun v => by
    simp only [μv]
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hc0 v) (hct v)
  have hpi : ∀ v, (Measure.pi fun _ : κ => measV ψ v) = c v • μv v := fun v => by
    simp only [μv, smul_smul, ENNReal.mul_inv_cancel (hc0 v) (hct v), one_smul]
  obtain ⟨c₀, hc₀, hform⟩ := GlobalTheory.AdelicHaarPure.integral_pure_haar F κ (Measure.addHaar : Measure (κ → AF F))
    (measI F κ) μv hμv1

  have hind1 : ∀ v, ∫ x, GlobalTheory.RatWeilOp.ind κ v x ∂(μv v) = 1 := fun v => by
    have := integral_indicator_const (μ := μv v) (1 : ℂ) (hOm v)
    simpa [GlobalTheory.RatWeilOp.ind, Measure.real, Pi.one_def, hμv1 v] using this

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbcs : HasCompactSupport (fun z => b z) := b.hasCompactSupport
  have hf₀c : Continuous (fun z => ((b z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous
  have hf₀cs : HasCompactSupport (fun z => ((b z : ℝ) : ℂ)) := hbcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hf₀i : Integrable (fun z => ((b z : ℝ) : ℂ)) (measI F κ) := hf₀c.integrable_of_hasCompactSupport hf₀cs
  have hBpos : 0 < ∫ z, b z ∂(measI F κ) :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := measI F κ) (x := 0) hbcs (fun z => b.nonneg)
      (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; exact one_ne_zero)
  have hfam0 : GlobalTheory.RatWeilOp.IsFam (fun v : Pl F => GlobalTheory.RatWeilOp.ind κ v) :=
    ⟨fun v => GlobalTheory.WeylFour.IndOSelf.indO_mem_SB v κ, Filter.Eventually.of_forall fun v => rfl⟩
  obtain ⟨-, h0⟩ := hform (fun z => ((b z : ℝ) : ℂ)) _ hf₀c hf₀i hfam0
  rw [finprod_congr hind1, finprod_one, mul_one, integral_complex_ofReal] at h0
  set H : (κ → AF F) → ℂ := fun x => ((b (fun i => evI F (x i)) : ℝ) : ℂ) *
    ∏ᶠ v, GlobalTheory.RatWeilOp.ind κ v (fun i => evFin F v (x i)) with hHdef
  have key : ∀ z w : ℂ, (z.im = 0 ∧ 0 ≤ z.re) → (w.im = 0 ∧ 0 ≤ w.re) → ((z * w).im = 0 ∧ 0 ≤ (z * w).re) := by
    rintro z w ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [Complex.mul_im, h1, h3]; simp, by rw [Complex.mul_re, h1, h3]; simpa using mul_nonneg h2 h4⟩
  have hP : ∀ x, (H x).im = 0 ∧ 0 ≤ (H x).re := by
    intro x
    refine key _ _ ⟨by simp, by simpa using b.nonneg⟩ ?_
    refine finprod_induction (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re) ⟨by simp, by simp⟩ key (fun v => ?_)
    by_cases h : (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_mem h]
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_notMem h]
  have hHr : H = fun x => (((H x).re : ℝ) : ℂ) := funext fun x => Complex.ext (by simp) (by simp [(hP x).1])
  have hL : ∫ x, H x ∂(Measure.addHaar : Measure (κ → AF F)) =
      ((∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) : ℝ) : ℂ) := by
    conv_lhs => rw [hHr]
    exact integral_complex_ofReal
  have hLnn : 0 ≤ ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) := integral_nonneg fun x => (hP x).2
  set L := ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) with hLdef
  set B := ∫ z, b z ∂(measI F κ) with hBdef
  have hc₀eq : c₀ = ((L / B : ℝ) : ℂ) := by
    have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hBpos.ne'
    rw [Complex.ofReal_div, eq_div_iff hB0, ← hL, ← h0]
  set t := L / B with htdef
  have ht0 : t ≠ 0 := fun h => hc₀ (by rw [hc₀eq, h, Complex.ofReal_zero])
  have htpos : 0 < t := lt_of_le_of_ne (div_nonneg hLnn hBpos.le) (Ne.symm ht0)

  obtain ⟨T, hT⟩ : ∃ T : Finset (Pl (F := F)), ∀ v ∉ T, PsiUnr ψ v :=
    ⟨(Filter.eventually_cofinite.1 hunr).toFinset, fun v hv => by simpa using hv⟩
  set Cr : ℝ := ∏ v ∈ T, (c v).toReal with hCrdef
  have hCr : 0 ≤ Cr := Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg
  refine ⟨ENNReal.ofReal (Cr / t) • Measure.addHaar, inferInstance, fun g φ hgc hgi hSB hev => ?_⟩
  have hfam : GlobalTheory.RatWeilOp.IsFam φ := ⟨hSB, hev⟩
  obtain ⟨hI, hE⟩ := hform g φ hgc hgi hfam
  refine ⟨hI.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  have hloc : ∀ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) = ((c v).toReal : ℂ) * ∫ z, φ v z ∂(μv v) :=
    fun v => by rw [hpi v, integral_smul_measure, Complex.real_smul]
  have hsub : Function.mulSupport (fun v => ((c v).toReal : ℂ)) ⊆ (T : Set (Pl (F := F))) := fun v hv => by
    by_contra h
    exact hv (by show ((c v).toReal : ℂ) = 1; rw [hc1 v (hT v h)]; simp)
  have hs2 : (Function.mulSupport fun v => ∫ z, φ v z ∂(μv v)).Finite :=
    (Filter.eventually_cofinite.1 hev).subset fun v hv h => hv (by
      show ∫ z, φ v z ∂(μv v) = 1
      rw [h]; exact hind1 v)
  have hCprod : ∏ᶠ v, ((c v).toReal : ℂ) = (Cr : ℂ) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, hCrdef, Complex.ofReal_prod]
  rw [integral_smul_measure, hE, ENNReal.toReal_ofReal (div_nonneg hCr htpos.le), hc₀eq, finprod_congr hloc,
    finprod_mul_distrib (T.finite_toSet.subset hsub) hs2, hCprod, Complex.real_smul]
  have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0
  rw [Complex.ofReal_div]
  field_simp

end GlobalTheory.WeylMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.FrameExt

theorem idem_factor {K : Type} [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q * Q = Q) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K), Z * C = Q ∧ C * Z = 1 := by
  let W := LinearMap.range Q.mulVecLin
  let b := Module.finBasis K W
  have key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w := by
    rintro ⟨w, v, rfl⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hQ]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict)
        = Q.mulVecLin := LinearMap.ext fun v => by simp
    rw [this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := LinearMap.ext fun c => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]

end GlobalTheory.FrameExt

theorem GlobalTheory.FrameExt.exists_fr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M :=
    fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]
  have cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0 :=
    Matrix.ext fun i j => by simp [Formalism.UG.cT]
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hBX : cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hcm hJ hW
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := by rw [hA]; exact hW.xx
  have hAY : A * Y = 1 := by rw [hA]; exact hW.xy
  have hBY : B * Y = 0 := by rw [hB]; exact hW.yy
  have hBX' : B * X = 1 := by rw [hB]; exact hBX
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAQ : A * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]
    simp
  have hBQ : B * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]
    simp
  have hQQ : Q * Q = Q := by
    calc Q * Q = (1 - X * B - Y * A) * Q := by rw [← hQ]
      _ = Q - X * (B * Q) - Y * (A * Q) := by
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q := by rw [hBQ, hAQ]; simp
  obtain ⟨m, Z, C, hZC, hCZ⟩ := GlobalTheory.FrameExt.idem_factor Q hQQ
  have hQZ : Q * Z = Z := by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]
  have hAZ : A * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]
  have hBZ : B * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]

  have hzc : cT (σ : E →+* E) Z * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hAZ
    rwa [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  have hzd : cT (σ : E →+* E) Z * J * Y = 0 := by
    have := congrArg (cT (σ : E →+* E)) hBZ
    rwa [hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z := ⟨_, rfl⟩
  have hJ₀h : cT (σ : E →+* E) J₀ = J₀ := by
    rw [hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]
  have key : cT (σ : E →+* E) Z * J = J₀ * C := by
    calc cT (σ : E →+* E) Z * J = cT (σ : E →+* E) Z * J * (X * B + Y * A + Z * C) := by
          rw [hZC, hQ]; simp
      _ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]
      _ = J₀ * C := by rw [hzc, hzd]; simp
  have hJZ : J * Z = cT (σ : E →+* E) C * J₀ := by
    have := congrArg (cT (σ : E →+* E)) key
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h] at this
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀) := by
    rw [← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]
  have hdet₀ : J₀.det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_
    rw [← hCZ, hZ]; simp only [Matrix.mul_assoc]
  have hJ₀u : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hdet₀
  refine ⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩
  · have := congrFun (congrFun hJ₀h i) j
    simpa [Formalism.UG.cT] using this
  · rw [← hA]; exact hAZ
  · rw [← hB]; exact hBZ
  · rw [← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]
    abel
  · have htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]; congr 1; abel
    rw [Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ] at htr
    simp only [Matrix.trace_one, Fintype.card_fin] at htr
    have h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E) := by push_cast at htr ⊢; rw [htr]; ring
    exact Nat.cast_injective h3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg (Submodule.IsLattice.span_eq_top (self := hX.lat))
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

theorem exists_finG_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram →
    ∃ g : GfC V, finG V g = M := by
  intro D V M hM
  obtain ⟨g0, hg0⟩ := GlobalTheory.FunObj.UA_le_range_finE V hM
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g0) (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g0)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  rw [← hg0]
  change Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g0)
  rw [k2]

end GlobalTheory.FrameTransport

end
end

