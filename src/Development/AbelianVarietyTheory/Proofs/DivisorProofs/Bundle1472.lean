module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_abelian | exact GlobalTheory.AbCoh.primF_of_abelian | (intros; apply GlobalTheory.AbCoh.primF_of_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField
open GlobalTheory.AbelianProjective

theorem exists_affine_loci_of_normChart : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∀ N₀ : LB B.left, N₀.IsLB → NormChart B N₀ → ∃ (I : Type) (t : I → N₀.Sec), (⨆ i, Out.nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (t i)) := by
  intro Ω _ _ B _ hB N₀ hN₀ ⟨W, V, π, a, U, N, n, hfin, hop, hne, hlft, hU, hUne, hN, H, hn⟩
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨_, t, ?_, fun w => ?_⟩
  · by_contra hne'
    have hc : ((⨆ i, Out.nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne' (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U hUne (Out.nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint Ω) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : Out.nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (Out.nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

theorem exists_normChart : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ N₀ : LB A.left, N₀.IsLB ∧ NormChart A N₀ := by
  intro K _ B _ hB
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (LB.isLB_pull hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (LB.isLB_pull hN' _) (LB.isLB_pull hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  exact ⟨N₀, hN₀, W, V, π, a, U, N, n, hfin, inferInstance, inferInstance, inferInstance, hU, ⟨_, hxU⟩, hN, H, hn⟩

theorem isProjBy_of_cover_baseChange {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (A : Over (Sp K)) [IsProper A.hom]
    {B : Over (Sp Ω)} {φ : B.left ⟶ A.left} (h : IsPullback φ B.hom A.hom (spMap i)) {N₀ : LB A.left} (hN₀ : N₀.IsLB)
    {I : Type} (t : I → (N₀.pull φ).Sec) (hc : ⨆ j, Out.nonzeroLocus (t j) = ⊤)
    (ha : ∀ j, IsAffineOpen (Out.nonzeroLocus (t j))) : GlobalTheory.AbLaw.IsProjBy A.hom := by
  have : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have hN := LB.isLB_pull hN₀ φ
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun j => (Out.nonzeroLocus (t j) : Set B.left))
    (fun j => (Out.nonzeroLocus (t j)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ j, Out.nonzeroLocus (t j) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hamp : GlobalTheory.IsAmpleLB (N₀.pull φ) := GlobalTheory.isAmpleLB_of_cover hN le_rfl
    (fun j : F => GlobalTheory.secToPow (t j.1) 1) (top_unique fun x _ => by
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, hj⟩, ?_⟩
      rw [GlobalTheory.nonzeroLocus_secToPow _ le_rfl]
      exact hx)
    fun j => (GlobalTheory.nonzeroLocus_secToPow (t j.1) le_rfl).symm ▸ ha j.1
  exact GlobalTheory.ProjFinite.isProjBy_of_fieldExtension i h hN₀ hN (GlobalTheory.lbIso_refl hN)
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 hamp)

theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  obtain ⟨N₀, hN₀, hc⟩ := exists_normChart K A hA
  let Ω := AlgebraicClosure K
  let B : Over (Sp Ω) := (Over.pullback (spMap (algebraMap K Ω))).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap (algebraMap K Ω))) B.hom A.hom (spMap (algebraMap K Ω)) :=
    IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨I, t, hcov, ha⟩ := exists_affine_loci_of_normChart Ω B hB _ (LB.isLB_pull hN₀ _) (_root_.GlobalTheory.ProjField.normChart_baseChange K Ω A hA N₀ hN₀ hc)
  exact isProjBy_of_cover_baseChange _ A sqB hN₀ t hcov ha
end GlobalTheory.ProjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2Statement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_mem_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  first | exact @GlobalTheory.WeilM.schA_memLp_two | exact GlobalTheory.WeilM.schA_memLp_two | (intros; apply GlobalTheory.WeilM.schA_memLp_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZero
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.GhostKer

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_frobenius (b : Ainf p O) : phiInv p O (WittVector.frobenius b) = b := by
  rw [WittVector.frobenius_eq_map_frobenius]
  unfold phiInv
  ext n
  simp only [WittVector.map_coeff]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem frobenius_iterate_teichmuller (k : ℕ) (x : PreTilt O p) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[k] (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]


variable (p O) in
def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by rw [ghost, iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghost_succ_xi {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (k : ℕ) :
    ghost p O (k + 1) (xi ε) = p := by
  have h : ghost p O (k + 1) (WittVector.teichmuller p (root ε)) = 1 := by
    rw [ghost, frobenius_iterate_teichmuller, WittVector.fontaineTheta_teichmuller, pow_succ',
      pow_mul, root, frobeniusEquiv_symm_pow_p, map_pow]
    have h0 := hε.zeta_zero
    simp only [zeta, Function.iterate_zero, id] at h0
    rw [h0, one_pow]
  change ghostHom p O (k + 1) (xi ε) = p
  unfold xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_pow]
  change ∑ i ∈ Finset.range p, (ghost p O (k + 1) (WittVector.teichmuller p (root ε))) ^ i = p
  simp [h]

theorem nu_eq_mu_root (x : PreTilt O p) : nu x = mu (root x) := rfl

end SlopeTestRemainingChoices

theorem mu_dvd_of_ghost : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε a ha
  have h1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have key : ∀ n, ∀ a : Ainf p O, (∀ m, ghost p O m a = 0) → mu ε ∣ mu (root^[n] ε) * a := by
    intro n
    induction n with
    | zero => intro a _; exact dvd_mul_right _ _
    | succ n ih =>
      intro a ha
      have ha0 : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
        rw [RingHom.mem_ker]; exact ha 0
      rw [GlobalTheory.AinfXi.ker_theta hv ε h1, Ideal.mem_span_singleton] at ha0
      obtain ⟨b, rfl⟩ := ha0
      have hb : ∀ m, ghost p O m (WittVector.frobenius b) = 0 := by
        intro m
        rw [ghost_frobenius]
        have h3 := ha (m + 1)
        rw [ghost_mul, ghost_succ_xi hε] at h3
        exact (mul_eq_zero.1 h3).resolve_left hp0
      obtain ⟨c, hc⟩ := ih _ hb
      have hc' := congrArg (phiInv p O) hc
      have e : root (root^[n] ε) = root^[n + 1] ε := (Function.iterate_succ_apply' root n ε).symm
      rw [map_mul, map_mul, phiInv_frobenius, phiInv_mu, phiInv_mu, nu_eq_mu_root, e] at hc'
      refine ⟨phiInv p O c, ?_⟩
      linear_combination xi ε * hc' + phiInv p O c * xi_mul_nu ε
  exact GlobalTheory.MuDivides.mu_dvd_of_forall_dvd p C v O hv ε h1 a (fun n => key n a ha)

end GlobalTheory.GhostKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k]

def auxiliaryVectorUniformizerExponent (a a' : ℤ) (c : ℕ) {n : Type*} : n ⊕ Fin c → ℤ
  | .inl _ => 0
  | .inr p => a * ((c : ℤ) - p) - a' * ((p : ℤ) + 1)

def vtxExp (a a' : ℤ) (c t x : ℕ) : ℤ :=
  if t ≤ x then a * ((c : ℤ) - ((x - t : ℕ) : ℤ)) - a' * (((x - t : ℕ) : ℤ) + 1) else 0

variable (G : Grid k)

def colDiag (ϖ : kˣ) (a a' : ℤ) (j : ℕ) : GL (Fin (G.rank (G.m, j))) k :=
  diagGL fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x

def boxExp (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ :=
  a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1

variable [ValuativeRel k]

def box (ϖ : kˣ) (a a' : ℤ) : Set (Vars G) :=
  Set.univ.pi fun j => Set.univ.pi fun v => {x : k | valuation k x ≤ valuation k ((ϖ ^ boxExp G a a' j v : kˣ) : k)}

variable {G}


omit [ValuativeRel k] in
theorem vtxExp_frame (a a' : ℤ) {t c b : ℕ} (h : t + c = b) (y : Fin t ⊕ Fin c) :
    vtxExp a a' c t (frame h y) = auxiliaryVectorUniformizerExponent a a' c y := by
  rcases y with x | p
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_left, x.2]
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_right]

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevW


open MeasureTheory IsDedekindDomain NumberField Matrix Polynomial in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.LevW.levW_of_parts : _root_.GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Hk3.HoweUnram → ∀ {D : _root_.Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : _root_.Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : _root_.Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : _root_.Formalism.IndefR.Links.Face3 D A3) {s : ℕ}, _root_.GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → _root_.Formalism.L2.DIV.GoodStable A3.A.X → _root_.GlobalTheory.CuspMult.CuspDecomp D → _root_.GlobalTheory.CuspMult.MultEq R.toRealDat → R.PGEquiv F → (∀ b, (_root_.Formalism.IndefR.Cx.lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → _root_.Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → R.toRealDat.LUnif → R.PLevW F := by
  intro hDecay hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hConv hOk hChar hEx hInert hStable hIrr hMult hEquiv hPos hScal hThmA hLift hUnif
  have hCarry := _root_.GlobalTheory.Hk3.carries_of_rows_top hDecay hHowe R F hConv hOk hChar hEx hInert hEquiv hPos
  have hSum := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hChar hEx
    (_root_.GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hDecay _) hStable hIrr hMult hCarry
  have hBlock := _root_.GlobalTheory.Hk3.inBlock_of_cuspRapidDecay hDecay R F hConv hOk hChar hEx hEquiv
  intro j
  rw [_root_.GlobalTheory.WType.range_w0C_type R F hOk hChar hEx hUnif j,
    _root_.GlobalTheory.WgLift.principal_lift_forms_eq_good_forms R F hOk hChar hEx hSum hScal hThmA hLift hBlock j]
  rfl

end GlobalTheory.LevW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SumW

theorem tw_sub_eq_map {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (V : Submodule ℂ E) :
    Tw.sub c V = V.map (Tw.mkL c E) := by
  ext x
  constructor
  · intro hx; exact ⟨Tw.out x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact hy

theorem tw_sub_iSup {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (U : ι → Submodule ℂ E) :
    Tw.sub c (⨆ p, U p) = ⨆ p, Tw.sub c (U p) := by
  simp only [tw_sub_eq_map, Submodule.map_iSup]

theorem inner_tw_eq_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (x y : Tw c E)
    (h : inner ℂ (Tw.out x) (Tw.out y) = 0) : inner ℂ x y = 0 := by
  rw [Tw.inner_eq, h, map_zero]

theorem iSup_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ c, U c) ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) =
      ⨆ c, U c ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) := by
  have := GlobalTheory.iSup_stable_inf_typeSpace ρ P ((Units.map σ.toMonoidHom).comp ψ) U (fun _ => True) hU
  simpa only [iSup_pos trivial, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this

theorem iSup_inf_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E) (R0 : Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) (hsum : (⨆ c, U c) = R0) :
    (⨆ c, U c ⊓ (R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id))) =
      R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) := by
  have hle : ∀ c, U c ≤ R0 := fun c => hsum ▸ le_iSup U c
  have h1 := iSup_inf_typeSp σ ρ P ψ U hU
  set Kt := ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) with hKt
  calc (⨆ c, U c ⊓ (R0 ⊓ Kt)) = ⨆ c, U c ⊓ Kt :=
        iSup_congr fun c => by rw [← inf_assoc, inf_of_le_left (hle c)]
    _ = (⨆ c, U c) ⊓ Kt := h1.symm
    _ = R0 ⊓ Kt := by rw [hsum]

theorem partsW_base : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).PartsW false := by
  intro hCRD hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hEx hInert hGS hCD hME hOkH hPG hPos hkap hB hU
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  obtain ⟨hCore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hcar := _root_.GlobalTheory.Hk3.carries_of_rows_top hCRD hHowe R F hLI hOk hW hEx hInert hPG hPos
  have hspan := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hW hEx hS hGS hCD hME hcar
  have horth := _root_.GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne R F hOk hW hEx hS hOkH hkap hB
  intro j
  have htype := _root_.GlobalTheory.WType.range_w0C_type R F hOk hW hEx hU j
  refine ⟨fun p q hpq w hw w' hw' => ?_, ?_⟩
  · exact inner_tw_eq_zero (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) w w' (horth j p q hpq _ hw.1 _ hw'.1)
  · obtain ⟨-, -, -, -, -, hst, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hCore hS hirr R.SF hSF j
    have hstab : ∀ p g, (R.Wp3 j p).map (R.gW j (sg0 D A3.A) g) ≤ R.Wp3 j p := by
      intro p g
      unfold RealDat3.Wp3
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun c _ => by rw [hWc]; exact hst c g
    have hstabX : ∀ p g, ((R.toCx3 F).Wp j p).map (R.gWx F j g) ≤ (R.toCx3 F).Wp j p := by
      rintro p g _ ⟨y, hy, rfl⟩
      exact hstab p g (Submodule.mem_map_of_mem hy)
    have hsumX : (⨆ p, (R.toCx3 F).Wp j p) =
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat j)) :=
      (tw_sub_iSup (twAt D.what₂.embLL A3.A.v0) (R.Wp3 j)).symm.trans
        (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (hspan j))
    rw [htype]
    unfold typeSubspace
    exact iSup_inf_inf_typeSp _ (R.gWx F j) F.P0 F.ψ0⁻¹ ((R.toCx3 F).Wp j) _ hstabX hsumX

end GlobalTheory.SumW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceOfInputs
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.EllTraceProof
open GlobalTheory.TruncKer

end GlobalTheory.EllTraceProof
end
end

