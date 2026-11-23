module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExistsUnifFv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocPosV
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem locPos_holds : LocPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).2 v
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let b := Module.finBasis F E
  set X1 := ratTup (F := F) (Fv F v) X0 with hX1
  set T := hermOf (Fv F v) σ (gramE σ J X0) hT with hTdef
  have hgT : gramH (Fv F v) σ hσ J hJ.1 X1 = T := Subtype.ext (gramR_ratTup (Fv F v) σ J X0)
  have hX1U : LinearIndependent (Fv F v ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Fv F v) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  obtain ⟨N, hN, hd⟩ := gramFilt_of (dxOpen_of secGram_holds) F E σ hσ M J hJ.1 hJ.2 a ha1 (by omega) v
    _ b X1 hX1U
  obtain ⟨Λ0, hB, hΛ0o, hΛ0c, hsub⟩ := isCOBasis_latSub b v a M N hN
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ :=
    hd X1 (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB hsub
  let Nb : Set (HermR (Fv F v) σ a) :=
    {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
  have hNb : Nb ∈ 𝓝 T :=
    (isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a).mem_nhds
      (isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  have hval := fibCos μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (continuous_gramH (Fv F v) σ hσ J hJ.1) (fun _ => rfl)
    _ Set.univ fibV hfib T Filter.univ_mem Nb hNb
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) Λ H hΛo hΛc hΛa hHo hHc hHb D hD X1
    hyp (by rw [hgT, sub_self]; exact zero_mem _)
  have hΛ0pos : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ 0 :=
    ((hΛo 0).measure_pos μv ⟨0, zero_mem _⟩).ne'
  have hΛ0fin : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ ⊤ :=
    ((hΛc 0).measure_lt_top).ne
  have hH0pos : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0 :=
    ((hHo 0).measure_pos νv ⟨0, zero_mem _⟩).ne'
  have hH0fin : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤ := ((hHc 0).measure_lt_top).ne
  have hQo : IsOpen {x | x - X1 ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - X1 ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - X1 ∈ Λ 0} := by
    have e : {x | x - X1 ∈ Λ 0} = (fun w => w + X1) '' (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - X1, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [e]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  refine ⟨{x | x - X1 ∈ Λ 0}.indicator 1, ⟨(LocallyConstant.indicator
    (LocallyConstant.const _ (1 : ℂ)) ⟨hQcl, hQo⟩).isLocallyConstant,
    HasCompactSupport.intro' hQc hQcl fun Y hY => Set.indicator_of_notMem hY _⟩, ?_⟩
  rw [hval]
  have hr : 0 < (μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) /
      νv (H 0 : Set (HermR (Fv F v) σ a))).toReal :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩).ne'
      (ENNReal.div_ne_top hΛ0fin hH0pos)
  exact_mod_cast hr.ne'

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoFibInv
section
noncomputable section

namespace PI.VolStabS.TopoFibInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open scoped TensorProduct

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X]

theorem isFibreFamily_map (e : V ≃ₜ V) {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν B fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hf : ∀ x, f (e x) = f x) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν B (fun b => (fib b).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι b ∧ x ∈ U)
      rw [hf x, hx]
    rw [this]
    exact hfib.1 b
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    refine lintegral_congr fun b => ?_
    exact (lintegral_map_equiv _ _).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b hb => (integrable_map_equiv em φ).2 (h1 b hb), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib b).map em)) = fun b => ∫ x, (φ ∘ e) x ∂(fib b) :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    exact h2

end Abstract

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gramR_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (h • X) = gramR R σ J X := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  funext x y
  change hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR R σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

theorem linIndep_mulVec {A : Type} [CommRing A] (G : GL (Fin M) A) (X : Fin a → Fin M → A) :
    LinearIndependent A (fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) ↔ LinearIndependent A X := by
  have inj : ∀ H : GL (Fin M) A, LinearMap.ker (mulVecLin (H : Matrix (Fin M) (Fin M) A)) = ⊥ :=
    fun H => by
      refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
      have := congrArg (fun z => ((H⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ z) hxy
      simpa [mulVecLin_apply, mulVec_mulVec] using this
  constructor
  · intro hl
    have h2 := hl.map' (mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) (inj G⁻¹)
    have e : (⇑(mulVecLin ((G⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A)) ∘
        fun x => (G : Matrix (Fin M) (Fin M) A) *ᵥ X x) = X := by
      funext x
      simp [mulVec_mulVec]
    rw [e] at h2
    exact h2
  · intro hl
    exact hl.map' (mulVecLin (G : Matrix (Fin M) (Fin M) A)) (inj G)

theorem linIndep_smul (h : HA R σ J) (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) (h • X) ↔ LinearIndependent (R ⊗[F] E) X :=
  linIndep_mulVec (HA.mat R σ J h) X

end Loc

end PI.VolStabS.TopoFibInv

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MuInvInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ h : HA (Ainf F) σ J, μinf.map (fun X => h • X) = μinf

def MuInvV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ h : HA (Fv F v) σ J, μv.map (fun X => h • X) = μv

theorem fibInvInf_of (hP : FibPin) (hM : MuInvInf) : FibInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfi h Φinf
    hcΦ hcs
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Ainf F) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfi
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h)
    (fun x => TopoFibInv.gramR_smul (Ainf F) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Ainf F) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 μinf hμ νinf hν _ _ hfam hfi Φinf
    hcΦ hcs
  rw [integral_map_equiv] at this
  exact this

theorem fibInvV_of (hP : FibPin) (hM : MuInvV) : FibInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfv h Φv hSB
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let e := smulHomeo (Fv F v) σ (a := a) J h
  have hfam := TopoFibInv.isFibreFamily_map e hfv
    (hM F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h)
    (fun x => TopoFibInv.gramR_smul (Fv F v) σ J h x)
    (Set.ext fun X => TopoFibInv.linIndep_smul (Fv F v) σ J h X)
  have := (hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2 v μv hμ νv hν _ _ hfam hfv Φv hSB
  rw [integral_map_equiv] at this
  exact this

theorem nuInv_of_steps (hD : DetAdm) (hC : CompG) (hP : FibPin) (hMI : MuInvInf) (hMV : MuInvV) :
    NuInv :=
  nuInv_of_loc gramPres_holds (pullLoc_of hC (fibInvInf_of hP hMI) (fibInvV_of hP hMV)) hD

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnifVSpec
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def unifV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fv F v :=
  ((v.valuation_exists_uniformizer F).choose : Fv F v)

theorem unifV_val {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
  rw [unifV, v.valuedAdicCompletion_eq_valuation', (v.valuation_exists_uniformizer F).choose_spec]

theorem unifV_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    unifV v ≠ 0 ∧ Tendsto (fun k : ℕ => unifV v ^ k) atTop (𝓝 0) ∧
      unifV v ∈ v.adicCompletionIntegers F := by
  have hv := unifV_val v
  have h1 : Valued.v (unifV v) < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖unifV v‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

def lamF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) (n : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) :=
  smulSub (unifV v ^ (n + 1)) (latSub b v a M)

def hF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    (n : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  smulSub (unifV v ^ (n + 1)) (hermO b v σ a)

def LatFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (a M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)),
    (∀ n, IsOpen (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    (∀ n, IsCompact (lamF b v a M n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
    Antitone (lamF b v a M) ∧ lamF b v a M 0 ≤ latSub b v a M ∧
    (∀ n, IsOpen (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ n, IsCompact (hF b v σ a n : Set (HermR (Fv F v) σ a))) ∧
    (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (hF b v σ a n : Set (HermR (Fv F v) σ a)) ⊆ N')

def HensAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ y ∈ latSub b v a M, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0 →
      ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
        (∀ n, (lamF b v a M n).map D = hF b v σ a n) ∧ ∀ n, ∀ Z ∈ lamF b v a M 0,
          ∀ W ∈ lamF b v a M n, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈ hF b v σ a (n + 1)

def IdxAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure →
      ν.IsAddHaarMeasure →
      μ (latV b v) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (2 * M * a) * μ (lamF b v a M 0) ∧
      ν (hermO b v σ a) = (Nat.card (𝓞 F ⧸ v.asIdeal) : ENNReal) ^ (a ^ 2) * ν (hF b v σ a 0)

def CntAA : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
    ∀ (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧
        Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
        μ (latV b v ∩ gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ hF b v σ a 0}) =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
            μ (lamF b v a M 0)

theorem resAA_of (hV : VolAA) (hL : LatFacts) (hH : HensAA) (hI : IdxAA) (hC : CntAA) :
    ResAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hV F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b,
    hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hI F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b,
    hC F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv hh hi hc
  intro μv hμ νv hν
  have := hμ.1
  have := hν.1
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hL F E σ d b a M v
  refine ⟨latSub b v a M, lamF b v a M, hF b v σ a, rfl,
    (PositiveNearLattice.isClopen_latV b v a M).isOpen, PositiveNearLattice.isCompact_latV b v a M, l4, l1, l2, l3,
    l5, l6, l7, hh, ?_⟩
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, hcard, hcnt⟩ :=
    hc μv hμ.1
  refine ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2, hJ', hJu, hT', hTu, ?_, ?_⟩
  · rw [hcard]; rfl
  obtain ⟨e1, e2⟩ := hi μv νv hμ.1 hν.1
  rw [hv.1 μv hμ, ← hcard] at e1
  rw [hv.2 νv hν, ← hcard] at e2
  show (μv (latV b v ∩ _) / νv _).toReal = _
  rw [hcnt, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have f1 := congrArg ENNReal.toReal e1
  have f2 := congrArg ENNReal.toReal e2
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_one] at f1 f2
  have hq : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  have hle : a ^ 2 ≤ 2 * M * a := by nlinarith
  have hp : (Nat.card k : ℝ) ^ (2 * M * a) = (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
      (Nat.card k : ℝ) ^ (a ^ 2) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hA : (0 : ℝ) < (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) := pow_pos hq _
  have hB : (0 : ℝ) < (Nat.card k : ℝ) ^ (a ^ 2) := pow_pos hq _
  rw [hp] at f1
  have hn : (νv (hF b v σ a 0)).toReal = 1 / (Nat.card k : ℝ) ^ (a ^ 2) := by
    field_simp; linarith
  have hm : (μv (lamF b v a M 0)).toReal =
      1 / ((Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) * (Nat.card k : ℝ) ^ (a ^ 2)) := by
    field_simp; linarith
  rw [hm, hn]
  field_simp

end PI.VolStabS
end
end

