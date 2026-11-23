module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsTiedSymChiZeroFinite
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem formsTiedSym_chi_zero_finite : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U, (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ) :=
  fun D _ _ _ Tf h =>
    _root_.GlobalTheory.unipotent_type_character_finite_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glev0 D.what₂.LL D.what₂.embLL D.host.g_prime (fun i => (h i).1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeFactsAll
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlac
section
namespace GlobalTheory.LocalUnitaryUnimod

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem unimodularOver_adicCompletion :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (Fv F v) hσ hJ

end GlobalTheory.LocalUnitaryUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
section
namespace GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular

theorem quotientMeasures : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures :=
  ⟨_root_.GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause, _root_.GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause, _root_.GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause, _root_.GlobalTheory.normaliseGroupClause_holds, _root_.GlobalTheory.QuotDiscrete.discreteClause, _root_.GlobalTheory.WeilCriterion.modulusClause,
    _root_.GlobalTheory.QuotientMeasureCompact.compactClause⟩

end GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

end GlobalTheory.MomT.FromComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverField
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapIsom

theorem form_u (D : D7) (L : PeriodPair) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hu : Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, u x w * (starRingEnd ℂ) (u y w) = ∑ w, x w * (starRingEnd ℂ) (y w) := by
  have h := hu x y
  change Formalism.L2.Th1.H.matH (hOne L _) (u x) (u y) = Formalism.L2.Th1.H.matH (hOne L _) x y at h
  rw [matH_hOne, matH_hOne] at h
  have hA : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos L).ne'
  exact (div_left_inj' hA).1 h

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hqc ι u hu h1 h2 h3
  obtain ⟨G, hG, hdet⟩ := GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) u
    (_root_.GlobalTheory.LatDesc.unitary_maps_rational D cc δ B hcc u h1)
  have hG' : ∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E))
      = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E) := fun v => hG v
  let γ : IsoK D :=
    { g := B.γ₀.g.trans G
      isom := by
        intro x y
        apply D.host.φ₀.injective
        have e1 := form_u D B.L u hu (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))
          (fun w => D.host.φ₀ ((B.γ₀.g y w : D.host.K) : D.host.E))
        rw [hG', hG'] at e1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← B.γ₀.isom x y, map_sum, map_sum]
        simp only [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
        exact e1 }
  refine ⟨γ, ⟨fun x hx => _root_.GlobalTheory.MomKapi.denom_prime_to D cc δ B hcc q hqc u h1 h2 G hG' x hx,
    fun v hv => _root_.GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime D cc δ B hcc hδ q hqc u hu h1 h2 h3 G hG' v hv⟩, ?_⟩
  have hd : γ.detRel B.γ₀ = LinearMap.det (G : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) := by
    have e : (B.γ₀.g.symm.trans γ.g) = G := by
      apply LinearEquiv.ext; intro v
      show G (B.γ₀.g (B.γ₀.g.symm v)) = G v
      rw [LinearEquiv.apply_symm_apply]
    unfold IsoK.detRel
    rw [e]
  rw [hdet, hd]
  rfl

end GlobalTheory.KapIsom
end
end

