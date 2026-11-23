module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise Topology

namespace GlobalTheory.AutomorphicL2Local

theorem continuous_integral_inv_mul_of_locallyIntegrable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} {f φ : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : LocallyIntegrable φ μ) :
    (∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ) ∧ Continuous fun x => ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  have hi : ∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ := fun x =>
    hφ.integrable_smul_left_of_hasCompactSupport (g := fun y => f (x⁻¹ * y)) (by fun_prop)
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  refine ⟨hi, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hK : IsCompact (U * tsupport f) := hU.mul hc.isCompact
  refine continuousAt_of_dominated (bound := (U * tsupport f).indicator fun y => M * ‖φ y‖)
    (.of_forall fun x => (hi x).1) ?_ ?_ (.of_forall fun y => ?_)
  · filter_upwards [hx] with x hxU
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ U * tsupport f
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport (f := f) fun h => hy ⟨x, hxU, _, h, by simp⟩]
      simp
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M)
  · exact Continuous.continuousAt (by fun_prop)

theorem continuous_convR_lift : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ F : L2 Γ μ, (∀ x, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧ Continuous (convR μ f (lift Γ F)) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F
  have hφ : LocallyIntegrable (lift Γ F) μ :=
    locallyIntegrable_iff.2 fun C hC => (memLp_restrict_compact G Γ μ F C hC).2
  obtain ⟨h1, h2⟩ := continuous_integral_inv_mul_of_locallyIntegrable hf hc hφ
  refine ⟨fun x => ?_, h2.congr fun x => (convR_eq f _ x).symm⟩
  simpa using (h1 x).comp_mul_left x

end GlobalTheory.AutomorphicL2Local
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
section
noncomputable section

namespace GlobalTheory.DecompCompare

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G] (Γ K : Subgroup G)

end Group

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Stab

theorem frame_inv {n P Q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G P Q)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) :
    ∃ L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ, L * A = 1 ∧ A * L = 1 := by
  obtain ⟨A₀, L₀, h0, hl, hr⟩ := GlobalTheory.VolPairExists.exists_frame h
  obtain ⟨e, -⟩ := h
  have h1 : (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
    calc (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A
        = L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) := by simp only [Matrix.mul_assoc]
      _ = L₀ * Formalism.UG.Jpq P Q * (A₀ * L₀)ᴴ * Formalism.UG.Jpq P Q * A₀ := by
          rw [hA, ← h0, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = L₀ * (Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q) * A₀ := by
          rw [hr, Matrix.conjTranspose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [GlobalTheory.VolPairExists.jpq_mul_self, Matrix.mul_one, hl]
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv e).1 h1⟩

variable (D : D7)

theorem KSub_eq (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) :
    KSub D W P Q θ A = levelW D.sp.cm W := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun ρ => ?_⟩⟩
  have hsig : Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := by
    have := hW (embOf D ρ)
    rwa [hs] at this
  obtain ⟨L, hl, hr⟩ := frame_inv hsig (hA ρ)
  have hu : (infMat D.sp.cm.sig W.gram (θ ρ) h)ᴴ * W.gram.map (embOf D ρ) * infMat D.sp.cm.sig W.gram (θ ρ) h =
      W.gram.map (embOf D ρ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH (D := D) (θ := θ) hθ W h ρ
  refine ⟨GlobalTheory.VolPairExists.mkU _ (GlobalTheory.VolPairExists.conj_unitary (hA ρ) hr hu), Set.mem_univ _, ?_⟩
  rw [GlobalTheory.VolPairExists.mat_mkU, Matrix.mul_assoc, hl, Matrix.mul_one]

theorem exists_data (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q)) :
    (∃ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ) := by
  refine ⟨GlobalTheory.DualPairCompare.exists_infFam D, ?_⟩
  have hsig : ∀ ρ, Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := fun ρ => by
    have := hW (embOf D ρ)
    rwa [hs] at this
  choose A L hA _ using fun ρ => GlobalTheory.VolPairExists.exists_frame (hsig ρ)
  exact ⟨A, hA⟩

theorem isOpen_levelW (W : HSpace D.host.E) :
    IsOpen (levelW D.sp.cm W : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) :=
  GlobalTheory.StabOpen.isOpen_stab_latHat D W

end GlobalTheory.DecompCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
section
noncomputable section

namespace GlobalTheory.StdFrame

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OrthFrame (V : HSpace E) : Prop :=
  (∀ a b, V.hT (V.frame a) (V.frame b) = if a = b then 1 else 0) ∧ ∀ a, V.frame a ∈ V.L0

theorem OrthFrame.gram_eq {V : HSpace E} (h : OrthFrame V) : V.gram = 1 := by
  ext a b
  rw [Matrix.one_apply]
  exact h.1 a b

theorem OrthFrame.mem_iff {V : HSpace E} (h : OrthFrame V) (x : Fin V.rank → E) :
    ∑ a, x a • V.frame a ∈ V.L0 ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx a
    have hd : ∑ a, x a • V.frame a ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 := by
      rw [V.baseLattice_isUnimodular]; exact hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hd
    have h1 : V.hT (V.frame a) (∑ b, x b • V.frame b) ∈ (1 : Submodule (𝓞 E) E) := hd _ (h.2 a)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul, h.1] using h1
  · intro hx
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx a)
    rw [← ho, algebraMap_smul]
    exact V.L0.smul_mem o (h.2 a)

def reframe (V : HSpace E) (b : Module.Basis (Fin V.rank) E V.V) : HSpace E := { V with frame := b }

theorem exists_orthFrame (V : HSpace E) {n : ℕ} (hn : V.rank = n) (h : Formalism.HermitianLatticesTheory.IsOrthoLattice V.hT V.L0 n) :
    ∃ b, OrthFrame (reframe V b) := by
  subst hn
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  refine ⟨Module.Basis.mk h1 h2.ge, fun (a b : Fin V.rank) => ?_, fun (a : Fin V.rank) => ?_⟩
  · show V.hT (Module.Basis.mk h1 h2.ge a) (Module.Basis.mk h1 h2.ge b) = _
    rw [Module.Basis.mk_apply, Module.Basis.mk_apply, h4]
    rfl
  · show Module.Basis.mk h1 h2.ge a ∈ V.L0
    rw [Module.Basis.mk_apply, h3]
    exact Submodule.subset_span ⟨a, rfl⟩

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hLat_one {D : D7} (V : HSp D) : Bridge.hLat V 1 = GlobalTheory.Member.latC V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem vStd_iff_gram_and_lattice (D : D7) (i : Fin D.R.m) :
    VStd D i ↔ (Vc D i).gram = 1 ∧
      L0c D (Vc D i) = ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) : Set (Fin (Vc D i).rank → D.host.E)) := by
  rw [VStd, hLat_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]

def FrameChoice (D : D7) (i : Fin D.R.m) : Prop := OrthFrame (D.sp.V ((i : ℕ) + 1))

theorem vStd_of_frameChoice : ∀ (D : D7) (i : Fin D.R.m), FrameChoice D i → VStd D i := by
  intro D i h
  refine (vStd_iff_gram_and_lattice D i).2 ⟨h.gram_eq, ?_⟩
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact (h.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem nV_pos (R : Ranks) : 0 < R.nV := by
  have := R.rank_add_five_le
  unfold Ranks.nV
  omega

theorem neg_eq_false_of_vStd (D : D7) (i : Fin D.R.m) (h : VStd D i) : D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  let τ := D.host.φ₀
  have hs := D.sp.V_sig ((i : ℕ) + 1) τ
  rw [factVSig _ _ D.sp _ (by omega) (by omega) τ, if_pos hneg] at hs
  have h1 : Formalism.UG.HasSignature ((Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)).map τ)
      (Vc D i).rank 0 := by
    have h0 : (Matrix.of fun a b => (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b)) = 1 := h.1
    rw [h0, Matrix.map_one _ (map_zero _) (map_one _)]
    simpa using Formalism.UG.P.stdform_sig_one (n := Fin (Vc D i).rank)
  have h2 := (sig_family (Vc D i) τ (D.sp.cm.cmUnram.2.1 τ) _ h1 hs).1
  have := nV_pos D.R
  simp only at h2
  omega

theorem neg_eq_false_of_posDef (D : D7) (i : Fin D.R.m) (h : (Vc D i).IsPosDef) :
    D.sp.Vneg ((i : ℕ) + 1) = false := by
  by_contra hneg
  rw [Bool.not_eq_false] at hneg
  have h1 := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) D.host.φ₀
  rw [if_pos hneg] at h1
  have h2 := congrArg Prod.snd ((h D.host.φ₀).symm.trans h1)
  exact (nV_pos D.R).ne h2

end GlobalTheory.StdFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivSplitPrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SplitCompletion

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx


open scoped WithZeroTopology in
theorem exists_extension {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | (apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension ..)

theorem exists_ringEquiv_splitPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v),
    ∃ φ : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E ≃+* Fv F v, (∀ x : E, φ (algebraMap E _ x) = τ x) ∧
      (∀ y, Valued.v (φ y) = Valued.v y) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro F E _ _ _ _ _ v τ
  obtain ⟨φ, hφc, hφ, hφv⟩ := exists_extension (GlobalTheory.AdelicU.splitPrime τ) v (τ : E →+* Fv F v)
    (GlobalTheory.AdelicU.valued_apply_eq_valuation τ)
  obtain ⟨ψ, hψc, hψ, -⟩ := exists_extension v (GlobalTheory.AdelicU.splitPrime τ)
    ((algebraMap E _).comp (algebraMap F E)) fun a =>
      (ReciprocityTheory.Aut.adic_valued_algebraMap _ _).trans ((GlobalTheory.AdelicU.valued_apply_eq_valuation τ _).symm.trans
        (GlobalTheory.AdelicU.valued_apply_algebraMap τ a))
  have hid : φ ∘ ψ = id := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer (hφc.comp hψc) continuous_id
    (funext fun a => ((congrArg φ (hψ a)).trans (hφ _)).trans (τ.commutes a))
  let e := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, congrFun hid y⟩⟩
  refine ⟨e, hφ, hφv, hφc, continuous_of_valued_eq (v.valuedAdicCompletion_surjective F) e.symm.toRingHom fun y => ?_⟩
  exact (hφv _).symm.trans (congrArg _ (e.apply_symm_apply y))

end GlobalTheory.SplitCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplexStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ) (s : ℂ → ℂ), (∀ j, AlgEnt (f j)) → AlgEnt s → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0 → GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  first | exact @GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | exact GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | (intros; apply GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
section
noncomputable section

namespace GlobalTheory.Equiv.StdSpace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coe_pi_one_eq_intVecs (n : ℕ) :
    ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
      Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D n := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact ⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩

theorem identityClassLattice_eq_selfDualFrameLattice (V : HSp D) : (Bridge.hLat V 1 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem lattice_clause_iff (V : HSp D) :
    (Bridge.hLat V 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔
      L0c D V = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D V.rank := by
  rw [← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]

end GlobalTheory.Equiv.StdSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2KernelIntegral

theorem integrable_descend_orbitSum {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {h : G → ℂ} (hh : Integrable h μ) :
    Integrable (descend Γ (orbitSum Γ h)) (quotMeasure Γ μ) := by
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]
    have hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ := fun γ =>
      hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving
    exact (AEMeasurable.tsum hm).aestronglyMeasurable
  · have h1 := lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm
    refine lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)
    exact lintegral_mono fun q => enorm_tsum_le_tsum_enorm

theorem convR_eq_integral_kernelQ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ (F : L2 Γ μ) (x : G),
      Integrable (fun q => kernelQ Γ f (mk Γ x) q * F q) (quotMeasure Γ μ) ∧
        convR μ f (lift Γ F) x = ∫ q, kernelQ Γ f (mk Γ x) q * F q ∂quotMeasure Γ μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x
  have hf' : Continuous fun y => f (x⁻¹ * y) := hf.comp (continuous_const_mul _)
  have hc' : HasCompactSupport fun y => f (x⁻¹ * y) := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hloc : LocallyIntegrable (lift Γ F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (_root_.GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F C hC).2
  have hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ :=
    hloc.integrable_smul_left_of_hasCompactSupport hf' hc'
  have key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) =
      fun q => kernelQ Γ f (mk Γ x) q * F q := by
    funext q
    induction q using Quotient.inductionOn with
    | h y =>
      refine ((leftInv_orbitSum _).descend_mk y).trans ?_
      change _ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)
      rw [kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]
      exact tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)
  refine ⟨key ▸ integrable_descend_orbitSum hi, ?_⟩
  rw [convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]

end GlobalTheory.AutomorphicL2KernelIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransportStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_parameter_series_deriv_transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  first | exact @GlobalTheory.DerivTransport.atU_deriv | exact GlobalTheory.DerivTransport.atU_deriv | (intros; apply GlobalTheory.DerivTransport.atU_deriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeWpDerivModelParameterSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCube_wpDeriv_model_parameter_series : (∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F)) → ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colC g.abelian₂ v) ∧ g.atU (GlobalTheory.FrobStick.colC g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * g.wq⁻¹ * (PowerSeries.C g.W.a₁ * PowerSeries.X + PowerSeries.C g.W.a₃ * PowerSeries.X ^ 3 * g.wq - 2) := by
  first | exact @GlobalTheory.FrobStick.colC_atU | exact GlobalTheory.FrobStick.colC_atU | (intros; apply GlobalTheory.FrobStick.colC_atU <;> assumption)
end

