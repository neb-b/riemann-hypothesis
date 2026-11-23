module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaNonzeroF

theorem herm_inv_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) :
    ∀ i j, σ (J⁻¹ j i) = J⁻¹ i j := by
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hmap : (J⁻¹).map σ * J.map σ = 1 := by
    have := congrArg (fun M => M.map σ) hinv
    simpa [Matrix.map_mul, Matrix.map_one] using this
  have hT : (J.map σ)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have h2 : J * ((J⁻¹).map σ)ᵀ = 1 := by
    calc J * ((J⁻¹).map σ)ᵀ = (J.map σ)ᵀ * ((J⁻¹).map σ)ᵀ := by rw [hT]
      _ = 1 := by rw [← Matrix.transpose_mul, hmap, Matrix.transpose_one]
  have hX : ((J⁻¹).map σ)ᵀ = J⁻¹ := (Matrix.inv_eq_right_inv h2).symm
  intro i j
  have := congrFun (congrFun hX i) j
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

theorem exists_isThetaFunOF_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  have hstd := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
  let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
  have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
  have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
  have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
    simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]
    ring
  have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
  have hB' : JB.det ≠ 0 := by
    simp only [JB, Matrix.det_neg, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
      (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
  let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
      co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hco
  have hJA : JA = JTᵀ := rfl
  have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by
    ext i j
    simp [JB, incM]
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩
  · rw [GlobalTheory.TransportF.thetaTr_eqF co' τ]
    exact _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  · intro h
    have h0 := congrFun h 0
    apply hne
    have hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
      funext x
      simp [GlobalTheory.WeilM.schr]
    simpa [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs] using h0

end GlobalTheory.ThetaNonzeroF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodicMeasurableSchwartzBound
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical Topology ContDiff

noncomputable section

namespace GlobalTheory.Cofactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

private theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (pureA F f g) :=
  (hf.comp (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i)))).mul
    (hg.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))

theorem hasCompactSupport_pureA {f : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (pureA F f g) := by
  let H : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hH : Continuous H := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)
  refine HasCompactSupport.intro ((hf.isCompact.prod hg.isCompact).image hH) fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨(fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2),
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩, ?_⟩
  funext i
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl


variable (F κ) in
theorem exists_bump : ∃ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, HasCompactSupport f ∧ f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, h1, ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]


variable (κ) in
def intPts (κ : Type)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F}

theorem intPts_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    intPts κ v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
  ext x; simp [intPts]

theorem isCompact_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsCompact (intPts κ v) := by
  rw [intPts_eq]
  exact isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isOpen_intPts (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : IsOpen (intPts κ v) := by
  rw [intPts_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {U : Set X} (hc : IsCompact U) (ho : IsOpen U) :
    U.indicator (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]; rfl
  · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem exists_cofactor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  intro F _ _ κ _ v
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨f, hfc, hf0⟩ := exists_bump F κ
  let φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ := fun w => (intPts κ w).indicator 1
  have hφ : ∀ w, φ w ∈ GlobalTheory.WeilM.SB _ := fun w => indicator_mem_SB (isCompact_intPts w) (isOpen_intPts w)
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have key : ∀ ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) ψ r = pureA F f g := by
    intro ψ hψ
    have h1 : ∀ w, Function.update φ v ψ w ∈ GlobalTheory.WeilM.SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hw]; exact hφ w
    have h2 := GlobalTheory.PureFactor.update_eventually φ v ψ hstd
    exact ⟨_, ⟨isLocallyConstant_finprod_evalV _ h1 h2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h1 h2⟩,
      hrt ψ⟩
  have hev : Continuous fun x : κ → AF F => fun i => evFin F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))
  have h0 : (0 : κ → Fv F v) ∈ intPts κ v := fun _ => zero_mem _
  have hrc : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro x
    let y : κ → Fv F v := fun i => evFin F v (x i)
    let U : Set (κ → Fv F v) := Homeomorph.addRight y '' intPts κ v
    have hUo : IsOpen U := (Homeomorph.addRight y).isOpenMap _ (isOpen_intPts v)
    have hUc : IsCompact U := (isCompact_intPts v).image (Homeomorph.addRight y).continuous
    have hy : y ∈ U := ⟨0, h0, by simp⟩
    obtain ⟨g, hg, e⟩ := key _ (indicator_mem_SB hUc hUo)
    refine (continuous_pureA f.continuous hg.1.continuous).continuousAt.congr ?_
    filter_upwards [hev.continuousAt.preimage_mem_nhds (hUo.mem_nhds hy)] with z hz
    rw [← e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens
    rw [Set.indicator_of_mem (show (fun i => evFin F v (z i)) ∈ U from hz), Pi.one_apply, one_mul]
  refine ⟨r, intPts κ v, hrc.measurable, hr, fun ψ hψ => ?_, isCompact_intPts v,
    ⟨0, by rw [(isOpen_intPts v).interior_eq]; exact h0⟩, fun μ hμ => ?_⟩
  · obtain ⟨g, hg, e⟩ := key ψ hψ
    exact Submodule.subset_span ⟨f, g, hg, e⟩
  obtain ⟨g, hg, e⟩ := key _ (hφ v)
  set P := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r with hP
  have hPc : Continuous P := e ▸ continuous_pureA f.continuous hg.1.continuous
  have hPs : HasCompactSupport P := e ▸ hasCompactSupport_pureA hfc hg.2
  have hP0 : P 0 = 1 := by
    rw [hP, hrt (φ v), Function.update_eq_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have a1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [a1, hf0, one_mul]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have : (fun i => evFin F w ((0 : κ → AF F) i)) ∈ intPts κ w := by
      intro i
      show evFin F w 0 ∈ _
      rw [map_zero]; exact zero_mem _
    exact Set.indicator_of_mem this _
  have hI : (fun x : κ → AF F => (intPts κ v).indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2) =
      fun x => ‖(P * P) x‖ₑ := by
    funext x
    simp only [hP, Pi.mul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, φ]
    by_cases hx : (fun i => evFin F v (x i)) ∈ intPts κ v
    · simp [Set.indicator_of_mem hx, sq]
    · simp [Set.indicator_of_notMem hx]
  rw [hI]
  have hPP : Continuous (P * P) := hPc.mul hPc
  refine ⟨fun h => ?_, (hPP.integrable_of_hasCompactSupport hPs.mul_left).2.ne⟩
  rw [lintegral_eq_zero_iff hPP.measurable.enorm] at h
  have h3 : (P * P) =ᵐ[μ] 0 := h.mono fun x hx => by simpa using hx
  have h4 := congrFun ((hPP.ae_eq_iff_eq μ continuous_zero).1 h3) 0
  simp [hP0] at h4

end GlobalTheory.Cofactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMul
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

open scoped WithZero

namespace GlobalTheory.CdvrPlaceVal

theorem mem_range_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (IsDiscreteValuationRing.maximalIdeal T.V) x hx
    have hu : IsUnit (d : T.V) := by
      by_contra hu
      exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
    obtain ⟨u, hu⟩ := hu
    refine ⟨n * ↑u⁻¹, ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

theorem vV_eq_mul_vAdd (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR)
    (iK : K →+* T.Fr)
    (h : ∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  let v1 : Valuation K ℤᵐ⁰ := (valV T.V).comap iK
  have hv1 : ∀ z, v1 z = valV T.V (iK z) := fun z => rfl
  have hle : ∀ z : K, v1 z ≤ 1 ↔ 𝔓.valuation K z ≤ 1 := fun z => by
    rw [← h z, mem_range_iff_valV_le_one, hv1]
  have hunit : ∀ w : K, 𝔓.valuation K w = 1 → v1 w = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have h0 : v1 w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    have h1 : v1 w ≤ 1 := (hle w).2 hw.le
    have h2 : v1 w⁻¹ ≤ 1 := (hle w⁻¹).2 (by rw [map_inv₀, hw, inv_one])
    rw [map_inv₀] at h2
    have h1' := (WithZero.log_le_log h0 one_ne_zero).2 h1
    have h2' := (WithZero.log_le_log (inv_ne_zero h0) one_ne_zero).2 h2
    rw [WithZero.log_inv, WithZero.log_one] at h2'
    rw [WithZero.log_one] at h1'
    rw [← WithZero.exp_log h0, show WithZero.log (v1 w) = 0 by omega]
    rfl
  obtain ⟨ϖ, hϖ⟩ := 𝔓.valuation_exists_uniformizer K
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hv1ϖ0 : v1 ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hlt : v1 ϖ < 1 := by
    have hle1 : v1 ϖ ≤ 1 := (hle ϖ).2 (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    refine lt_of_le_of_ne hle1 fun heq => ?_
    have h3 : v1 ϖ⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have h4 := (hle ϖ⁻¹).1 h3
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg] at h4
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h4
    norm_num at h4
  have ha : 0 < vV T.V (iK ϖ) := by
    have h5 : WithZero.log (v1 ϖ) < WithZero.log 1 := (WithZero.log_lt_log hv1ϖ0 one_ne_zero).2 hlt
    rw [WithZero.log_one, hv1] at h5
    simp only [vV]
    omega
  refine ⟨(vV T.V (iK ϖ)).toNat, by omega, fun z => ?_⟩
  rw [Int.toNat_of_nonneg ha.le]
  by_cases hz : z = 0
  · subst hz; simp [vV, vAdd]
  have hz2 : 𝔓.valuation K z = WithZero.exp (-vAdd 𝔓 z) := by
    simp only [vAdd, neg_neg]; exact (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm
  have hw : 𝔓.valuation K (z * ϖ ^ (-vAdd 𝔓 z)) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hz2, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu := hunit _ hw
  have hz' : z = (z * ϖ ^ (-vAdd 𝔓 z)) * ϖ ^ (vAdd 𝔓 z) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hv : v1 z = v1 ϖ ^ (vAdd 𝔓 z) := by
    conv_lhs => rw [hz']
    rw [map_mul, hu, one_mul, map_zpow₀]
  have e1 : vV T.V (iK z) = -WithZero.log (v1 z) := rfl
  have e2 : vV T.V (iK ϖ) = -WithZero.log (v1 ϖ) := rfl
  rw [e1, e2, hv, WithZero.log_zpow, smul_eq_mul]
  ring

end GlobalTheory.CdvrPlaceVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEq
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatPointNe

theorem evR_sig_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x _ Z τ s K _ _ _ y hy h0
  have ht : Tested y := GlobalTheory.FlagTan.fromTest_of_isLocalRing y
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hy ht]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.FlatPointNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := {z | z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem (latAtV X W v), zero_mem (latAtV X W v)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2⟩

theorem mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    z ∈ latDbl X W v ↔ z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v := Iff.rfl

theorem fromCols_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h₁ : γ₁ ∈ latAtV X W v) (h₂ : γ₂ ∈ latAtV X W v) : Matrix.fromCols γ₁ γ₂ ∈ latDbl X W v := by
  rw [mem_latDbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  exact ⟨h₁, h₂⟩

theorem at_of_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hz : z ∈ latDbl X W v) : At (evFin F v) z := by
  intro u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.2 u hu
  ext i (j | j)
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

end GlobalTheory.DblVacEigen
end
end

