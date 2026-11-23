module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0009
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0010
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0904
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanInverseThetaIdentity
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacFixOpen


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vacO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → T.SigOK →
    ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J → om (x, 1) f₀ = f₀ := by
  intro D ψ θ S T χS χT om hW hSs hTs sS sT hcS hcT ΛS ΛT hsdS hsdT f₀ hvac
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const :
      Continuous fun x : GA D S => ((x, (1 : GA D T)) : GA D S × GA D T))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial x →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n₁.factorial k → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, 1) f₀ = c • f₀ := by
    intro k hk hc
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        fun _ => True), u = actO S T k 1 u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ 1 u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D T) u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one T θ τ (sT τ)) hΛ f₀ hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ S T sS sT hSs hTs hcS hcT ΛS ΛT hsdS hsdT f₀ _ hvac hvac'
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D S => om (k, 1) f₀ w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k → om (k, 1) f₀ = f₀ := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, 1) f₀ = c • f₀ ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.SmoothVac.om_pow_eq om (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om ((1 : GA D S), (1 : GA D T)) f₀ w₀ = f₀ w₀ := by
      show om 1 f₀ w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖f₀ w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (f₀ w₀)]
  obtain ⟨n, hn⟩ := key
  have hN : 0 < n₁.factorial * n.factorial := Nat.mul_pos n₁.factorial_pos n.factorial_pos
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial)).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S hN, fun k hk hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S k := congrArg Subtype.val e
  refine hn k hk ?_
  have hc := hk'.2
  unfold GlobalTheory.Member.FinCong at hc ⊢
  rw [← e']
  exact hc

end GlobalTheory.VacFixOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionConductorTwistedCharacterAdmissi
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
private theorem isAdmCoc_latOne_of_eigenvector_characters {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ ψ κ κ₁ : G →* Oˣ) (p : Xs)
      (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (a : ℕ)
      (z : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1)
      (hχ : χ = θ) (hψ : ψ = κ * θ) (hκ : κ₁ = 1) (hlam : lam ≠ 0)
      (hM : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = M g 0 0)
      (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
      (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin 1 → LL) ⧸ stdG O LL 1) (fun g => actD (stdLatG hinj M) g) f)
      (hz : ∀ g, iotaC LL lam a (z g) = f g)
      (hu : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ g : Oˣ) : O) • u)
      (he : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ₁ g : Oˣ) : O) • u) :
      tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (latOne hinj ψ) ↥(Xq LL lam a) χ z := by
  obtain ⟨u, hu0, hu⟩ := hu
  obtain ⟨e, he0, he⟩ := he
  subst hκ
  have hI := UpperTheory.KN.iotaC_injective_and_equivariant hinj M χ ψ lam a hM
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (latOne hinj ψ) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant N _ _ (iotaC LL lam a) z f hI.1 hI.2 hz hpres
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N θ χ p (latOne hinj ψ) ↥(Xq LL lam a) z
    (LinearMap.toSpanSingleton LL _ u) e x₀ hχ hlam hfull h3
    (fun s t hst => smul_left_injective LL hu0 hst) (fun g v => ?_) he0 (fun g => ?_) hx b hb
  · rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, Matrix.mulVec_smul, hu g, hψ]
    funext m
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]
    ring
  · rw [he g]
    simp

theorem _root_.GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c))
      ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ c hc z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have hpid : IsPrincipalIdealRing ↥(OL C.LL) := hdvr.toIsPrincipalIdealRing
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (chiRatO D.nd i c) z hz
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  have hκ : chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) = 1 := by simp [chiOC]
  have H := isAdmCoc_latOne_of_eigenvector_characters (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
    (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
    (fun x => locOC C (rTwO D.nd i r x)) θ (chiT C θ 1) (chiT C θ c)
    (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) π
    Subtype.val_injective (locOC C (chiRatO D.nd i c)) a z' (fun g => liftQ C.le 1 (z g))
    (chiT_one_eq_theta C θ) rfl hκ hlam.ne_zero (chiT_ratio C θ c) hSet.2 h2 hz' (hE.2 c hc)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
  exact H
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateHalfVacuumTranslateSumIsThetaFockVacuum
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjHalfVac

theorem sum_conj_half_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y) → IsThetaFunO ψ V W (∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) (∑ y ∈ Y, heisO ψ V W y f₀) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY
  obtain ⟨hpair, _, _, _, _, _, _, _, hvac⟩ := hP
  have hstd : IsStdChar D ψ (-1) := hvac.1
  have hth0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  have hinf : infPart D (cA D eT) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hT)
  have hfin : ∀ y ∈ Y, map y ⇑(infPart D) = 0 := fun y hy =>
    GlobalTheory.DatumFock.infPart_of_isHalf hinf (hY y hy)
  refine ⟨?_, fun τ => ?_⟩
  · classical
    induction Y using Finset.induction_on with
    | empty => simpa using GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := V) (T := W)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact GlobalTheory.OrientedHeis.theta_add
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hth0 a)
        (ih (fun y hy => hY y (Finset.mem_insert_of_mem hy)) (fun y hy => hfin y (Finset.mem_insert_of_mem hy)))
  · have hF : IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) f₀ :=
      hvac.2.fock τ
    have := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ V W hstd.1 hpair.inf f₀ hth0 τ _ hF
      (WO V W) Y id (fun _ => 1) (fun y hy => hfin y hy)
    simpa using this

end GlobalTheory.ConjHalfVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreRationalFormsSubsetCoverForms
section
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUp

theorem baseForms_sub_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  intro D T hL j hj σ hσ C hU a n hD hP
  constructor
  · intro x hx
    obtain ⟨f, ⟨hf, hh⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := _root_.GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨hf₂, _root_.GlobalTheory.CoverHol.cover_pull_holSub0 D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩
  · intro S S₂ hS
    intro x hx
    obtain ⟨f, ⟨hf, hh, hi⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := _root_.GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨⟨hf₂, _root_.GlobalTheory.CoverHol.cover_pull_holSub0 D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩,
      _root_.GlobalTheory.CoverUpInt.pull_integral D T hL j hj σ hσ C hU a n hD S S₂ hS f hf hi f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩

end GlobalTheory.CoverUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelationsStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  first | (exact @GlobalTheory.JSW.MatchedVec.matched_vectors) | (exact GlobalTheory.JSW.MatchedVec.matched_vectors) | (intros; apply GlobalTheory.JSW.MatchedVec.matched_vectors  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsScalarMove
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ

end GlobalTheory.Unframe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact _root_.GlobalTheory.JR.SizeOne.unitMatch_zero
  | succ r ih => exact _root_.GlobalTheory.JR.UnitStep.unitMatch_succ (_root_.GlobalTheory.JR.weilEt_of_weilField hW) _root_.GlobalTheory.JR.gammaOne_holds r (_root_.GlobalTheory.JR.fourierMatch_of_weilField hW (r + 1)) ih

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  first | (exact @GlobalTheory.RamShift.condOne_condExp) | (exact GlobalTheory.RamShift.condOne_condExp) | (intros; apply GlobalTheory.RamShift.condOne_condExp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacterStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  first | exact @GlobalTheory.JSW.whit_mul_locGL_tD_shift | exact GlobalTheory.JSW.whit_mul_locGL_tD_shift | (intros; apply GlobalTheory.JSW.whit_mul_locGL_tD_shift <;> assumption)
end

