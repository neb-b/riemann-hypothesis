module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0063
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcRegAlgPolarizedPair
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BcPolar
theorem bc_regAlg_polarizedPair_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  intro hL F K _ _ _ _ _ _ _ h2 a ha π χ P hreg hpol hBC
  refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ?_⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F K)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hBC.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · obtain ⟨χ', hs, hd⟩ := _root_.GlobalTheory.PolarBc.bcDual_of_polarized hL.aut.js.1 hL.aut.gk F K h2 a ha π χ P hpol hBC
    obtain ⟨k, hk⟩ := GlobalTheory.BcPolar.exists_sign_twist χ' hs a
    refine ⟨χ' * quadChar K ^ k, fun v => (hk v).trans (zpow_natCast _ _), ?_⟩
    rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
end GlobalTheory.BcPolar
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeCharLocalArtinEqCyclotomicTwist
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (ξ : G F Ω →* (Qbar l)ˣ) (t : ℤ), IsOpen (ξ.ker : Set (G F Ω)) → IsCharOf ι χ (cycBar F Ω l ^ t * ξ) → ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, ((χ.loc w (a s) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (t * deg s) * ι (ξ (s : G F Ω) : Qbar l) := by
  intro N F Ω _ _ _ _ _ l _ ι χ ξ t hξ ⟨hc, art, n, hart, _, hL⟩ w hw A h a ha s
  haveI : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen hξ
  have hN : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := UpperTheory.V.Loc.laHecke h art hart ι χ n _ hL ⟨a, ha⟩
  have h2 := UpperTheory.V.Loc.laArith N.aut.art h hw ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype)
    (hc.comp continuous_subtype_val) t ξ.ker.index (Nat.pos_of_ne_zero hN) fun g _ => by
      have e : ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype) g * cycBar F Ω l g ^ (-t) = ξ g := by
        show cycBar F Ω l g ^ t * ξ g * cycBar F Ω l g ^ (-t) = ξ g
        rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, ← map_pow]
      exact ξ.ker.pow_index_mem _
  have h3 := UpperTheory.V.Loc.laUnique h ⟨a, ha⟩ _ _ _ h1 h2
  haveI : Fintype {j : w.adicCompletion F →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb w)
  have h4 : locPow ι n w (a s : w.adicCompletion F) = Hi.algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ t := by
    unfold locPow Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_injective (congrFun h3 j), zpow_one]
  have h0 : Hi.algPow w (fun _ : F →+* Qbar l => 1) (a s : w.adicCompletion F) ^ t ≠ 0 := by
    refine zpow_ne_zero _ ?_
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero)
  have h5 := hL.loc (a s) s (ha.glob art hart s)
  have h6 := UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s
  have h7 : (((cycBar F Ω l ^ t * ξ) (s : G F Ω) : (Qbar l)ˣ) : Qbar l) =
      (cycBar F Ω l (s : G F Ω) : Qbar l) ^ t * (ξ (s : G F Ω) : Qbar l) := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul]
    rfl
  rw [h7, h6, h4, mul_zpow, mul_right_comm, mul_left_inj' h0, eq_comm, RingEquiv.symm_apply_eq] at h5
  rw [h5, map_mul, map_zpow₀, map_zpow₀, map_natCast, ← zpow_mul, mul_comm t]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.InertiaLeRangeOfUnramified
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.QuadraticCharacterUnramified
end GlobalTheory.QuadraticCharacterUnramified
theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoComm
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LocCompCLit
open Matrix
section
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩
end
theorem main_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  intro H E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp H.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end GlobalTheory.LocCompCLit
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem dr_of_above (H : HeckeLAdicCharacterAbove) : HeckeLAdicCharacterDeRham := by
  intro E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB
  have := H E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB
  exact ⟨this.1, this.2.2.2⟩
private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl
private theorem ex_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') :
    ∃ j : Emb l w, j.1.comp (algebraMap F (w.adicCompletion F)) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
    have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
    refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
    exact iff_of_eq (congrArg (· < 1) h1.symm)
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩
theorem UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (ω : (w.adicCompletion F)ˣ →* ℂˣ) (hh : (F →+* Qbar l) → ℤ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), OrdChar ι a ω hh ψ → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {hh τ}) (fun s => Polynomial.X - Polynomial.C (ω (a s) : ℂ)) ∧ PotCrys A (GlobalTheory.TripleGal.rk1 ψ) := by
  intro N F Ω _ _ _ _ _ l _ A w h _ ι a ha ω hh ψ ho
  have art := N.aut.art
  obtain ⟨hc, hla⟩ := (UpperTheory.V.Loc.ordCharIff art h ι a ha hh ψ).1.1 ⟨ω, ho⟩
  have hdr := UpperTheory.V.Loc.laDeRham art art.heckeLAdicCharacter (dr_of_above N.aut.chA) N.aut.berger h ψ hc _ hla
  refine ⟨fun O _ _ _ Bw hj => ⟨(hdr O Bw hj).1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩,
    fun O _ _ _ Bw hj => (hdr O Bw hj).2.1⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj τ LL' τ' hτ
    exact (hdr O Bw hj).2.2 j
  · obtain ⟨ξ, hs, hξ, e⟩ := UpperTheory.V.Loc.laWD art art.heckeLAdicCharacter (dr_of_above N.aut.chA)
      N.aut.chW N.aut.berger h ψ hc _ hla O Bw hj ι a ha
    have hv : ((ψ (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) =
        ι.symm (ω (a s)) * algPow w (-hh) (a s : w.adicCompletion F) := ho.val s _ rfl (Set.mem_univ _)
    have h1 : algPow w (-hh) (a s : w.adicCompletion F) * ∏ᶠ τ : Emb l w, τ.1 (a s : w.adicCompletion F) ^
        hh (τ.1.comp (algebraMap F (w.adicCompletion F))) = 1 := by
      haveI := finite_contEmb (l := l) w
      unfold algPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun j => ?_
      rw [Pi.neg_apply, zpow_neg]
      exact inv_mul_cancel₀ (zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero))
    have h2 : (ξ s : ℂ) = ω (a s) := by
      rw [hξ, hv, mul_assoc, h1, mul_one, ι.apply_symm_apply]
    rw [e, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp [h2]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocLaArtinLit
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
abbrev _root_.UpperTheory.V.Loc.localArtinReciprocity_type : Prop := ∀ (H : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w),
    ∃ a, IsLocalArtin h a
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentiallySemistableType
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
def TypeVAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → ∀ rc, Win.IsRecV h rc → IsTypeWD h χ (rc (algNorm τ)) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
def PotentiallySemistableType : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreUniq
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x
private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e
private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e
theorem UpperTheory.V.Hi.core_unique_of_axioms_weight_char :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (D' : W.GDet n (H.TK θ a K) H.Gq) (ψ' : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D' ψ' → D' = D ∧ ψ' = ψ := by
  intro _ L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ _ a K _ _ D ψ hU D' ψ' hU'
  refine ⟨UpperTheory.V.CA.d_gext D' D fun g i _ _ => congrFun (cu_ext _ hA.dense (hU'.cont i) (hU.cont i) ?_) g, ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    simp only [W.GDet.lam, hU.frob ⟨w, hw⟩ B σ hB hσ, hU'.frob ⟨w, hw⟩ B σ hB hσ]
  · funext v i
    have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec (H.ovr v))) := UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (H.ovr v)
    refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (hU'.ψ_cont v i) (hU.ψ_cont v i) ?_) g)
    rintro _ ⟨s, rfl⟩
    refine congrArg Units.val (cu_gen (H.art v) (hA.art_spec v).surj ((ψ' v i).comp _) ((ψ v i).comp _)
      (fun s y hy => ?_) (fun s hs => ?_) s)
    · have e := (hU'.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      have e' := (hU.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      exact mul_right_cancel (inv_injective (Units.ext
        ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
    · exact mul_right_cancel (cu_prod _ _ (fun j => Units.ext
        ((hU'.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).trans
          (hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).symm)) i)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPCohC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
theorem UpperTheory.V.Af.clozelCohC_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Published.ClozelCohC := by
  intro lit E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := lit.aut.coh E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsRec
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
end
abbrev _root_.UpperTheory.V.Hi.psRec_s_ty : Prop :=
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (IsSubquotient σ.ρ (PS ω) ↔ ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ)))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypePS2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
def TypePS2Alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ : SmIrr (GLw n w)), π.IsLocComp w τ →
    ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    ∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧
      ∀ i (g : Ine (F := L) A), ω i (artOf h (ineIncl h g)) = χ i g
def ResidualEqualityRankTwo : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ), 1 ≤ n →
    ∀ (π π' : CuspSub L n) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (τ τ' : SmIrr (GLw n w)), π.IsLocComp w τ →
    π'.IsLocComp w τ' → ∀ χ : Fin n → Ine (F := L) A →* ℂˣ, (∀ i, ∃ ψ : Weil h →* ℂˣ, ∀ g, ψ (ineIncl h g) = χ i g) → (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ))) →
    (∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → IsTypeWD h χ (rc (algNorm τ'))) → KEq τ τ'
end UpperTheory.V.Z.J.D
end
end
end

