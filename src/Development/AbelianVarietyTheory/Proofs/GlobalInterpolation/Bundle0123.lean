module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.GaugeEx
open GlobalTheory.UnitVectorStabiliser GlobalTheory.HermLineZeros
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelicStabUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_stepData (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    (hJ : IsHermND σ J) (x : Fin 1 → Fin (M + 1) → E) (hx : hE σ J (x 0) (x 0) ≠ 0) :
    ∃ (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      StepData σ J x a B J' := by
  have herm := hf_herm (σ : E →+* E) J (conj_invol h) hJ.1
  obtain ⟨a, ha⟩ := exists_of_fixed h (hE σ J (x 0) (x 0)) (herm _ _)
  let φ := hfLin (σ : E →+* E) J (x 0)
  have hφ : φ ≠ 0 := fun h0 => hx (LinearMap.congr_fun h0 (x 0))
  have hk : Module.finrank E (LinearMap.ker φ) = M := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fin_fun] at this
    omega
  let b := Module.finBasisOfFinrankEq E _ hk
  let B : Matrix (Fin (M + 1)) (Fin M) E := Matrix.of fun i j => (b j : Fin (M + 1) → E) i
  have hG : ∀ i j, (Formalism.UG.cT (σ : E →+* E) B * J * B) i j =
      Formalism.UG.hform (σ : E →+* E) J (b i) (b j) := fun i j => by
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  refine ⟨a, B, _, hJ, ?_, ha.symm, fun j => (b j).2, rfl, fun i j => ?_, fun hd => ?_⟩
  · rintro rfl
    exact hx (by rw [← ha, map_zero])
  · rw [hG, hG]
    exact herm _ _
  · obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    let y : LinearMap.ker φ := ∑ j, c j • b j
    have h1 : ∀ i, hfLin (σ : E →+* E) J y (b i) = 0 := fun i => by
      have h2 : hfLin (σ : E →+* E) J (b i) y = 0 := by
        rw [← show _ = (0 : E) from congrFun hc0 i]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Matrix.mulVec,
          dotProduct, hG, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact (herm _ _).symm.trans ((congrArg _ h2).trans (map_zero _))
    have h3 : ∀ z : LinearMap.ker φ, hfLin (σ : E →+* E) J y z = 0 := fun z =>
      LinearMap.congr_fun (b.ext (f₁ := hfLin (σ : E →+* E) J y ∘ₗ Submodule.subtype _) (f₂ := 0) h1) z
    have h4 : hfLin (σ : E →+* E) J y (x 0) = 0 :=
      (herm _ _).symm.trans ((congrArg _ (show Formalism.UG.hform _ J (x 0) y = 0 from y.2)).trans (map_zero _))
    obtain ⟨t, p, hp, -⟩ := exists_proj (σ : E →+* E) J (x 0) hx.isUnit (LinearMap.ker φ) fun _ => Iff.rfl
    have h5 : ∀ z, Formalism.UG.hform (σ : E →+* E) J z y = 0 := fun z => by
      have : hfLin (σ : E →+* E) J y z = 0 := by
        rw [hp z, map_add (f := _), map_smul, h3, h4, smul_zero, add_zero]
      exact (herm _ _).symm.trans ((congrArg _ this).trans (map_zero _))
    have h6 : J *ᵥ (y : Fin (M + 1) → E) = 0 := funext fun i => by
      have := h5 (Pi.single i 1)
      rw [hf_eq] at this
      simpa [dotProduct, Pi.single_apply, apply_ite] using this
    have h7 : y = 0 := Subtype.ext (Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h6)
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h7))

theorem isUnimodularLC_of_equiv {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [MeasurableSpace H]
    (hH : IsUnimodularLC H) (e : G ≃* H) (h1 : Continuous e) (h2 : Continuous e.symm) :
    IsUnimodularLC G := by
  obtain ⟨_, _, _, _, _, -, hH⟩ := hH
  let e' : G ≃ₜ H := ⟨e.toEquiv, h1, h2⟩
  haveI := e'.isEmbedding.t2Space
  haveI := e'.isClosedEmbedding.locallyCompactSpace
  haveI := e'.secondCountableTopology
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ hμ => ⟨fun g => ?_⟩⟩
  haveI := hH _ (MulEquiv.isHaarMeasure_map μ e h1 h2)
  have h3 := congrArg (Measure.map e.symm) (map_mul_right_eq_self (μ.map e) (e g))
  rw [Measure.map_map h2.measurable h1.measurable,
    Measure.map_map (measurable_mul_const _) h1.measurable,
    Measure.map_map h2.measurable ((measurable_mul_const _).comp h1.measurable)] at h3
  convert h3 using 1
  · congr 1
    funext y
    simp
  · rw [show e.symm ∘ e = id from funext fun y => by simp, Measure.map_id]

theorem unimodularOver_of_forall (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R]
    (hR : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ μ : Measure (HA R σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) : UnimodularOver R σ J := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsUnimodularLC (HA R σ J) :=
    fun M J hJ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨Measure.haar, inferInstance⟩, hR M J hJ⟩
  refine ⟨key M J hJ, fun x hx => ?_⟩
  cases M with
  | zero => exact absurd (by simp [hE, Formalism.UG.hform]) hx
  | succ M =>
    obtain ⟨a, B, J', hS⟩ := exists_stepData h hJ x hx
    borelize R
    obtain ⟨-, ⟨e, he, -⟩, hc⟩ := GlobalTheory.FrameStep.frameStep F E σ h R M J x a B J' hS
    exact isUnimodularLC_of_equiv (key M J' hS.2.2.2.2.2) e (hc e he).1 (hc e he).2

theorem unimodularOver_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨d, hd⟩ := exists_conj_ne h
  exact unimodularOver_of_forall h (AF F) fun M J hJ μ _ =>
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (conj_invol h) (sub_ne_zero.2 hd)
      (by rw [map_sub, conj_invol h, neg_sub]) hJ μ

end GlobalTheory.AdelicStabUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (_root_.GlobalTheory.SplitResidueCard.card_kv D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSubgroupQuotientInvariantMeasure
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureCompact

theorem compactClause : CompactClause := by
  intro G _ _ _ _ _ _ H _ _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  borelize G
  refine _root_.GlobalTheory.WeilCriterion.modulusClause G H hH.isClosed fun h => ?_
  rw [GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact H hH h.2,
    GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact (⊤ : Subgroup H) (by simpa using isCompact_univ)
      (Subgroup.mem_top h)]

end GlobalTheory.QuotientMeasureCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndexStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_different_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F), (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔ ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧ dualIndex F ψ₀ v = normDifferentV F v := by
  first | exact @GlobalTheory.StdDual.dualV_eq_inv_different_cm | exact GlobalTheory.StdDual.dualV_eq_inv_different_cm | (intros; apply GlobalTheory.StdDual.dualV_eq_inv_different_cm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEqStandardAdeleCharRationalDilate
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.AdelicCharDilate

theorem exists_eq_std_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  intro F E _ _ _ _ _ _ σ hCM _ _ ψ₀ h₀ ψ h
  haveI := hCM.1
  exact _root_.GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 h

end GlobalTheory.AdelicCharDilate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprime
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomKapi


open Formalism.L2.Th1.H in
theorem nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (S M : AddSubgroup V) {z : V} (hz : z ∈ M) :
    relIdx S M • z ∈ S := by
  have h := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)
  have h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S := AddSubgroup.mem_addSubgroupOf.1 h
  simpa [relIdx, AddSubgroup.relIndex] using h2

theorem denom_prime_to : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D cc δ B hcc q _ hcop u hn hnq G hG x hx
  set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) with hndef
  set N := Ideal.absNorm cc with hNdef
  have hq : q.Prime := Fact.out
  have hnc : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
  refine ⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B

  have hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀
  have hw₀mem : w₀ ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨_, hNc, rfl⟩
  have hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx
  have hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E)) := by
    rw [map_smul]
    exact congrArg (w₀ • ·) (B.gC_spec x)
  have hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) := by
    rw [hgC, map_smul, hG]
  have hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) :=
    ⟨_, ⟨_, hz, rfl⟩, rfl⟩
  have hS := nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM
  rw [← hndef, hu] at hS
  have hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice := by
    have := hS w (Set.mem_univ w)
    simpa using this
  obtain ⟨c, -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)
  have hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E) := by
    apply mul_left_cancel₀ hδ
    rw [← hc', hw₀]
    push_cast
    simp only [map_mul, map_natCast, nsmul_eq_mul]
    ring
  have hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K) :=
    Subtype.coe_injective (D.host.φ₀.injective hC)
  exact ⟨c, hK.symm⟩

end GlobalTheory.MomKapi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprime
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatInvDenom

theorem lamMM_form (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ z ∈ lamMM D (lamOf D cc δ), ∃ e ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      z = fun τ => δ * embT D τ e := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    obtain ⟨c, -, rfl⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ w hw
    refine ⟨((c : D.host.K) : D.host.E) * a, ?_, ?_⟩
    · exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.intK D c⟩ : 𝓞 D.host.E) ha
    · funext τ
      rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (SetLike.coe_mem _)]
      ring
  | zero => exact ⟨0, Submodule.zero_mem _, by funext τ; simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    obtain ⟨e2, he2, rfl⟩ := h2
    exact ⟨e1 + e2, Submodule.add_mem _ he1 he2, by funext τ; simp only [Pi.add_apply, map_add (f := _)]; ring⟩
  | neg x _ h1 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    exact ⟨-e1, Submodule.neg_mem _ he1, by funext τ; simp only [Pi.neg_apply, map_neg]; ring⟩

theorem inverseIsometry_fourfoldLattice_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  intro D cc δ B hcc hδ12 q _ hNq u hu hidx hq hidx' G hG v hv
  have hqp : q.Prime := Fact.out
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      (Formalism.L2.Th1.H.pow4 B.lamM)) with hM

  have hSd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) S :=
    Formalism.L2.Th1.H.stdSelfDual B.L _
  have hMd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) M :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual_img _ _ u hu _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ12)
  have heq : Formalism.L2.Th1.H.relIdx S M = Formalism.L2.Th1.H.relIdx M S :=
    Formalism.L2.Th1.H.indexEq _ _ (Formalism.L2.Th1.H.stdHBasic B.L _).2.1 S M hSd hMd hidx hidx'
  set n := Formalism.L2.Th1.H.relIdx M S with hn
  have hnq : Nat.Coprime n q := by
    rw [← heq]; exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 hq)
  have h1 : ∀ x ∈ S, n • x ∈ M := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf S) (⟨x, hx⟩ : S)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set N := Ideal.absNorm cc with hNdef
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  choose o ho using hv
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hz : (δ * (N : ℂ)) • V ∈ S := by
    rw [hS, Formalism.L2.Th1.H.mem_stdLat]
    intro w
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B]
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K) * o w, cc.mul_mem_right _ hNc, ?_⟩
    simp only [hV, Pi.smul_apply, smul_eq_mul, ← ho w]
    push_cast
    rw [map_mul, map_natCast]
    ring
  set y := B.γ₀.g.symm (G.symm v) with hy
  have hgy : u (B.gC (emb4 D y)) = V := by
    rw [show B.gC (emb4 D y) = _ from B.gC_spec y, hy, LinearEquiv.apply_symm_apply, hG (G.symm v),
      LinearEquiv.apply_symm_apply]
  obtain ⟨m', ⟨m₀, hm₀, rfl⟩, hm'⟩ := h1 _ hz
  have hm0eq : m₀ = ((n : ℂ) * δ * (N : ℂ)) • emb4 D y := by
    apply B.gC.injective
    apply u.injective
    have e1 : u (B.gC m₀) = n • ((δ * (N : ℂ)) • V) := hm'
    rw [e1, map_smul, map_smul, hgy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.mp (by
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.card_tau]
    exact Nat.mul_pos (by decide) D.R.ord_pos)
  refine ⟨n * N, Nat.Coprime.mul_left hnq hNq, fun a => ?_⟩
  obtain ⟨e, he, hee⟩ := lamMM_form D cc δ _ (hm₀ a)
  have h2 := congrFun hee τ
  rw [hm0eq] at h2
  simp only [Formalism.L2.Th1.H.slice, Pi.smul_apply, smul_eq_mul, emb4] at h2
  have h3 : embT D τ (((n * N : ℕ) : D.host.E) * y a) = embT D τ e := by
    apply mul_left_cancel₀ hδ
    rw [map_mul, map_natCast]
    push_cast
    linear_combination h2
  rw [(embT D τ).injective h3]
  exact he

end GlobalTheory.LatInvDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory

theorem decay_integrable_periodise : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧
      (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧
      Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  intro F _ _ N hF Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hsz : ∀ u : Fin N → AF F, 0 ≤ sz u := fun u =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun w _ => abs_nonneg _
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [hsz 0]) k)) (hC 0)
  have key : ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧
      (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
    intro ω hω
    obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
    refine ⟨c, hcs, hc0, fun ξ y hy => ?_⟩
    by_cases hmem : fin (rat ξ + y) ∈ K
    · have h1 := hcb ξ y hy hmem
      have h2 := hC (rat ξ + y)
      calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨ν, hν⟩ := _root_.GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
    obtain ⟨-, -, -, ⟨K₀, hK₀, hcov⟩, -⟩ := _root_.GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
    obtain ⟨c, hcs, hc0, hcb⟩ := key K₀ hK₀
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    let S : (Fin N → F) → Set (Fin N → AF F) := fun ξ => (fun u => u + -rat ξ) ⁻¹' K₀
    have hSm : ∀ ξ, MeasurableSet (S ξ) := fun ξ =>
      hK₀.measurableSet.preimage (measurable_add_const _)
    have hSμ : ∀ ξ, μ (S ξ) = μ K₀ := fun ξ => measure_preimage_add_right μ (-rat ξ) K₀
    have hpt : ∀ u, ‖Φ u‖ₑ ≤ ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u := by
      intro u
      obtain ⟨ξ, hξ⟩ := hcov u
      have hu : u ∈ S ξ := by
        show u + -rat ξ ∈ K₀
        rw [← sub_eq_add_neg]; exact hξ
      refine le_trans ?_ (ENNReal.le_tsum ξ)
      rw [Set.indicator_of_mem hu]
      have h3 := hcb ξ (u - rat ξ) hξ
      rw [add_sub_cancel] at h3
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal h3
    have hfin : (∑' ξ, ENNReal.ofReal (C * c ξ)) < ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg hC0 (hc0 ξ)) (hcs.mul_left C)]
      exact ENNReal.ofReal_lt_top
    unfold HasFiniteIntegral
    calc ∫⁻ u, ‖Φ u‖ₑ ∂μ
        ≤ ∫⁻ u, ∑' ξ, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ := lintegral_mono hpt
      _ = ∑' ξ, ∫⁻ u, (S ξ).indicator (fun _ => ENNReal.ofReal (C * c ξ)) u ∂μ :=
          lintegral_tsum fun ξ => (measurable_const.indicator (hSm ξ)).aemeasurable
      _ = ∑' ξ, ENNReal.ofReal (C * c ξ) * μ K₀ := by
          congr 1; ext ξ; rw [lintegral_indicator_const (hSm ξ), hSμ]
      _ = (∑' ξ, ENNReal.ofReal (C * c ξ)) * μ K₀ := ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hfin hK₀.measure_lt_top
  · intro u
    obtain ⟨c, hcs, hc0, hcb⟩ := key {u} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb ξ u rfl) (hcs.mul_left C)
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
    obtain ⟨c, hcs, hc0, hcb⟩ := key ω hωc
    have hon : ContinuousOn (fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u)) ω :=
      continuousOn_tsum (fun ξ => (hc.comp (continuous_const.add continuous_id)).continuousOn)
        (hcs.mul_left C) (fun ξ y hy => hcb ξ y hy)
    exact hon.continuousAt hωn

end GlobalTheory
end

