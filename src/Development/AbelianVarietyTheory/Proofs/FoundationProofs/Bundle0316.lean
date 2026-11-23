module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstantTermAlongFlagEqZeroOfCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp

theorem constTerm_eq_zero_of_mem_cuspCont (D : D7) (V : HSp D) (φ : GA D V → ℂ) (h : φ ∈ cuspCont V) (𝔉 : IsoFlag V)
    (h𝔉 : 𝔉.Proper) : constTerm 𝔉 φ = 0 := by
  have hi : (⟨1, Nat.succ_lt_succ h𝔉⟩ : Fin (𝔉.k + 1)) ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have h0 : constTermOn (GQ V) (NA (.single (𝔉.isIsotropic hi))) φ = 0 :=
    (isCuspFun_iff h.2.1).1 h.2.2 _ (𝔉.isIsotropic hi)
  funext x
  refine (Stages.constTermOn_stages (GA D V) (GQ V) (NA 𝔉) (NA (.single (𝔉.isIsotropic hi)))
    (𝔉.unip_single_le D.sp.cm _ hi) (fun p hp n hn => IsoFlag.conj_mem_unip ?_ hn) (cocompact_flag D V 𝔉)
    (cocompact_single _) φ h.2.1 h.1 x).trans ?_
  · rw [IsoFlag.par_single]
    exact 𝔉.par_le_parab D.sp.cm _ _ (𝔉.unip_le_par D.sp.cm _ hp)
  · rw [h0]
    exact (cocompact_flag D V 𝔉).constTermOn_const 0 x

end GlobalTheory.Cusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecompositionGroupMulEquivLocalGaloisCyclotomic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.DecLocal

theorem exists_mulEquiv_cyc : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  intro F Ω _ _ _ _ _ l _ v A hv hA
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := l) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt l :=
    ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (PadicAlgCl l) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK l K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycK l K.1 r σ : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GK l K.1) (PadicAlgCl l) σ) _
      hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

end GlobalTheory.DecLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsObj

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting hiding levJ

section Space

variable {D : D7}

theorem gramAt_posDef {V : HSp D} (hp : V.IsPosDef) (hs : V.SigOK) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have := hs (tauE D τ)
  rw [hp] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem exists_compact_of_fin (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hC : IsCompact C) : ∃ K : Set (GA D V), IsCompact K ∧ ∀ k : GA D V, (∀ i j, (finHom V k).1 i j ∈ C) → k ∈ K := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  choose R hR using fun τ => GlobalTheory.DefiniteQuotient.exists_bound_unitary (hV τ)
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k hk => hKe k fun i j => hCe' _ (hk i j) fun τ => ?_⟩
  have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k) * V.gram.map (incA D) * Formalism.L2.Theta.mt V k = V.gram.map (incA D) := k.2
  have e : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k)).map ((θ τ).comp (infPart D)) =
      ((Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
    ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
  have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
  simp only [Matrix.map_mul, e, hJ] at this
  exact ((hR τ _ this i j).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))

theorem finite_stab (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V))
    {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)} (hC : IsCompact C) (hJ : ∀ k ∈ J, ∀ i j, k.1.1 i j ∈ C) (g : Bridge.Gf V) :
    Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, h2, -, hg, hd, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_fin V hV hC
  obtain ⟨x, rfl⟩ := (finHom V).rangeRestrict_surjective g
  have hK' : IsCompact ((fun k => x * k * x⁻¹) '' K) := hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : GQ V → GA D V) ⁻¹' ((fun k => x * k * x⁻¹) '' K)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK').finite_of_discrete
  refine Set.Finite.subset hfin fun γ hγ => ⟨x⁻¹ * γ.1 * x, hKe _ ?_, by group⟩
  have h := hJ _ ((Bridge.mem_stab _).1 hγ)
  rw [map_mul, map_mul, map_inv]
  exact h

theorem exists_cover_of_compact {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) {C : Set G} (hC : IsCompact C)
    (hCe : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) :
    ∃ (m : ℕ) (c : Fin m → H), ∀ g, ∃ (a : Fin m) (γ : Γ) (k : J), g = π.comp Γ.subtype γ * c a * k := by
  obtain ⟨S, -, hS⟩ := hC.elim_nhds_subcover (fun x => {y | π (x⁻¹ * y) ∈ J}) fun x _ =>
    (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp)
  refine ⟨_, fun a => π (S.equivFin.symm a).1, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hCe x
  obtain ⟨s, hs, hcs⟩ := Set.mem_iUnion₂.1 (hS hc)
  exact ⟨S.equivFin ⟨s, hs⟩, ⟨γ, hγ⟩, ⟨_, hcs⟩, by simp [mul_assoc]⟩

theorem exists_cover (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V)) (ho : IsOpenLev V J) :
    ∃ (m : ℕ) (c : Fin m → Bridge.Gf V), ∀ g, ∃ (a : Fin m) (γ : GQ V) (k : J), g = Bridge.ratF V γ * c a * k :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (GlobalTheory.DefiniteQuotient.exists_compact V hV).elim fun _ h =>
    exists_cover_of_compact (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective J ho h.1 h.2

end Space

section Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T)

theorem isPosDef_of_vStd (hV : VStd D i) : (Vc D i).IsPosDef := fun τ => by
  have h := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) τ
  rw [GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hV, if_neg Bool.false_ne_true] at h
  rw [D.sp.V_rank _ (by omega) i.2]
  exact h

end Levels


section Record

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (K' : Type) [Field K']

end Record

end GlobalTheory.RepsObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCharFnAndIsPseudoCoeffOfCompact
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

variable {H : Type} [Group H] [TopologicalSpace H]
  {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] {D : H →* (V →L[ℂ] V)} {π : H →* (U →L[ℂ] U)}

theorem continuous_trace_rep (hD : IsUnitaryRep D) :
    Continuous fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) := by
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  exact continuous_finsetSum _ fun i _ => continuous_const.inner (hD.continuous_apply _)


omit [TopologicalSpace H] in
theorem trace_rep_conj (x s : H) :
    LinearMap.trace ℂ V (D (x⁻¹ * s * x) : V →ₗ[ℂ] V) = LinearMap.trace ℂ V (D s : V →ₗ[ℂ] V) := by
  have h := Representation.char_conj (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D) s x⁻¹
  rwa [inv_inv] at h

variable [MeasurableSpace H] [BorelSpace H] {μ : Measure H}

theorem hasTrace_repOp_of_finiteDimensional [CompleteSpace V] [IsFiniteMeasureOnCompacts μ] (hD : IsUnitaryRep D)
    {f : H → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    HasTrace (repOp D μ f) (∫ g, f g * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ) := by
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  simp only [trace_eq_linearMap_trace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), Finset.mul_sum,
    ContinuousLinearMap.coe_coe, hD.inner_repOp hf hc]
  exact (integral_finsetSum _ fun i _ => (hf.mul (continuous_const.inner
    (hD.continuous_apply _))).integrable_of_hasCompactSupport hc.mul_right).symm

variable [IsTopologicalGroup H] [CompactSpace H] [μ.IsHaarMeasure]

theorem integral_conj_trace_mul_trace (hD : IsUnitaryRep D) (hi : IsTopIrreducible D) :
    ∫ g, conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ = μ.real univ := by
  let ρ : Representation ℂ H V := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D
  have := hi.1
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)⟩
  have : ρ.IsIrreducible := ⟨fun S => (hi.2 S.toSubmodule ⟨S.toSubmodule.closed_of_finiteDimensional,
    fun g v hv => S.apply_mem_toSubmodule g hv⟩).imp (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h⟩
  have h := integral_conj_character_mul_character_self (haarProb H) ρ hD.continuous_apply hD.norm_apply
  conv_lhs => rw [eq_smul_haarProb μ]
  rw [integral_smul_measure]
  exact (congrArg _ h).trans (by simp [Measure.real])

theorem integral_inner_smul_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (e x : V) (v : U) :
    ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ = 0 := by
  have hI : ∀ z : V, Integrable (fun g => ⟪D g e, z⟫_ℂ • π g v) μ := fun z =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  let T : V →ₗ[ℂ] U :=
    { toFun := fun x => ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hI x) (hI y)]
        simp [add_smul]
      map_smul' := fun c x => by simp [mul_smul, integral_smul] }
  have hT : LinearMap.toContinuousLinearMap T ∈ AutMult.homIn D π ⊤ := AutMult.mem_homIn_top.2 fun g x => by
    change ∫ k, ⟪D k e, D g x⟫_ℂ • π k v ∂μ = π g (∫ k, ⟪D k e, x⟫_ℂ • π k v ∂μ)
    rw [← integral_mul_left_eq_self _ g, ← (π g).integral_comp_comm (hI x)]
    simp only [map_mul, ContinuousLinearMap.mul_apply, AutMult.inner_map_map hD, map_smul]
  have h0 : AutMult.homIn D π ⊤ = ⊥ := AutMult.multIn_eq_zero_iff.1 (by_contra fun h =>
    hne (AutMult.uEquiv_of_multIn_ne_zero ⟨‹_›, hD, hi⟩ ⟨‹_›, hπ, hi'⟩ h).symm)
  rw [h0, Submodule.mem_bot] at hT
  exact DFunLike.congr_fun hT x

theorem repOp_conj_trace_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (c : ℂ) :
    repOp π μ (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c) = 0 := by
  ext v
  rw [hπ.repOp_apply (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c)
    ((Complex.continuous_conj.comp (continuous_trace_rep hD)).div_const c)
    (HasCompactSupport.of_compactSpace _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), map_sum, inner_conj_symm, div_eq_inv_mul,
    mul_smul, integral_smul, Finset.sum_smul, ContinuousLinearMap.coe_coe]
  have hI : ∀ e : V, Integrable (fun g => ⟪D g e, e⟫_ℂ • π g v) μ := fun e =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  rw [integral_finsetSum _ fun i _ => hI _]
  simp [integral_inner_smul_eq_zero hD hi hπ hi' hne]

theorem isCharFn_and_isPseudoCoeff_of_compact [T2Space H] [SecondCountableTopology H] [CompleteSpace V]
    {n : Type} [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ} (hι : Continuous (matCoord ι))
    (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hχ : (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V))) ∈ CcMat ι) :
    IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) ∧
      IsPseudoCoeff ι μ D fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ := by
  have h0 : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos μ univ_nonempty).ne', measure_ne_top _ _⟩
  have hc := continuous_trace_rep hD
  have hf : Continuous fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ :=
    (Complex.continuous_conj.comp hc).div_const _
  have hΘ : IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) :=
    ⟨hc.locallyIntegrable, fun s _ => hc.continuousAt, fun f hf' =>
      hasTrace_repOp_of_finiteDimensional hD (continuous_of_mem_ccSmooth hι hf') hf'.1⟩
  refine ⟨hΘ, ?_, ?_, fun U _ _ _ π hπ hirr _ hne => ?_, fun s _ hT => absurd (isClosed_cent s).isCompact hT,
    _, hΘ, fun s _ hT dt _ _ => ?_⟩
  · simp only [div_eq_inv_mul]
    exact (CcMat ι).smul_mem (μ.real univ : ℂ)⁻¹ hχ
  · convert hasTrace_repOp_of_finiteDimensional (μ := μ) hD hf (HasCompactSupport.of_compactSpace _) using 1
    simp only [div_mul_eq_mul_div, integral_div, integral_conj_trace_mul_trace hD hi, div_self h0]
  · rw [repOp_conj_trace_eq_zero hD hi hπ hirr hne]
    exact ⟨isTraceClass_zero, trace_zero⟩
  · haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
    convert hasOrbInt_of_finite (dh := μ) (dt := dt)
      (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ)
      ((hf.comp (f := fun x => x⁻¹ * s * x) (by fun_prop)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) using 2
    simp only [trace_rep_conj, integral_const, Complex.real_smul]
    field_simp

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMember
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de hA
    have hno := (_root_.GlobalTheory.LowestTypeDrop.lowestType_not_jointShape t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLie

theorem hasDerivAt_constTermOn {G : Type} [Group G] [TopologicalSpace G] {Γ N : Subgroup G} [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : Cocompact Γ N) {φ ψ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ)
    {u : ℝ → G} (hu : Continuous u) (hd : ∀ g t, HasDerivAt (fun s => φ (g * u s)) (ψ (g * u t)) t) (x : G) :
    HasDerivAt (fun s => constTermOn Γ N φ (x * u s)) (constTermOn Γ N ψ (x * u 0)) 0 := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun p : N × ℝ => ψ (p.1 * (x * u p.2))) (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := probMeasure Γ N) (bound := fun _ => C)
    (F := fun s q => φ ((q.out : N) * (x * u s))) (F' := fun s q => ψ ((q.out : N) * (x * u s)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (.of_forall fun s => (hc.integrable hφ hφc _).1) (hc.integrable hφ hφc _)
    (hc.integrable hψ hψc _).1 (.of_forall fun q s hs' => ?_) (integrable_const C) (.of_forall fun q s _ => ?_)).2
  · obtain ⟨γ, hγ, hk⟩ := hs q.out
    exact (congrArg norm (leftInv_integrand hψ (x * u s) γ hγ q.out)).ge.trans
      (hC (_, s) ⟨hk, Metric.ball_subset_closedBall hs'⟩)
  · simpa only [mul_assoc] using hd ((q.out : N) * x) s

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : GA D V → ℂ}

theorem gelf_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (hφ : φ ∈ SmFun θ V) (τ' : D.what₂.Tau) (k : ℕ) :
    gelf θ V τ' k (Rder θ V τ X φ) = Rder θ V τ X (gelf θ V τ' k φ) := by
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  obtain ⟨c, hc, hg⟩ := GlobalTheory.SmoothForms.exists_gelf R τ'
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  have e : ∀ f : GlobalTheory.SmoothForms.SmF θ V, Rder θ V τ X f.1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X') f).1 := fun f => GlobalTheory.SmoothForms.Rder_eq R τ X' f.1
  have hcomm : Commute (GlobalTheory.SmoothForms.envRep R τ' (c k))
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X')) := by
    rw [← GlobalTheory.SmoothForms.envRep_ι]
    by_cases h : τ' = τ
    · subst h
      have hm : c k ∈ Subalgebra.center ℂ _ := hc ▸ Algebra.subset_adjoin ⟨k, rfl⟩
      exact Commute.map (Subalgebra.mem_center_iff.1 hm _).symm _
    · exact GlobalTheory.SmoothForms.envRep_comm R h _ _
  change gelf θ V τ' k (Rder θ V τ X ψ.1) = Rder θ V τ X (gelf θ V τ' k ψ.1)
  rw [e ψ, hg, hg, e]
  exact congrArg (fun S : Module.End ℂ (GlobalTheory.SmoothForms.SmF θ V) => (S ψ).1) hcomm.eq

theorem fg_comap {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W) :
    (W.comap (SmFun θ V).subtype).FG :=
  Module.Finite.iff_fg.1 (FiniteDimensional.of_injective ((SmFun θ V).subtype.restrict (q := W) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h)))

theorem derEnd_coe (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (f : SmFun θ V) : (derEnd hθ τ X f).1 = Rder θ V τ X f.1 :=
  GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX f.1

theorem isAutFunSm_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (Rder θ V τ X φ) := by
  refine { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (h.left γ hγ) τ X, level := ?_, cont := ?_,
           smooth := Rder_mem h.smooth hX, zfin := ?_, growth := ?_ }
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hf τ X φ) g
    rw [show rTr V k φ = φ from funext (e k hk hf)] at this
    exact this.symm
  · exact GlobalTheory.Size.continuous_rWord hθ h.smooth h.cont (GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h) (l := [(τ, X)])
      fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨((W.comap (SmFun θ V).subtype).map (derEnd hθ τ X)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 (((fg_comap hW).map _).map _),
      ⟨_, ⟨⟨φ, h.smooth⟩, m, rfl⟩, derEnd_coe hθ hX _⟩, ?_⟩
    rintro τ' k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨_, (linOnSm_gelf τ' k).mem _ f.2⟩, s τ' k _ hf, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, derEnd_coe hθ hX, derEnd_coe hθ hX, gelf_Rder hθ hX f.2]
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hN (l ++ [(τ, X)]) (GlobalTheory.Mem.Lift.append_mem_lie hl hX) x

theorem isKFinite_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {K : Subgroup (GA D V)} (hK : K ≤ GinfC V)
    (hs : φ ∈ SmFun θ V) (h : GlobalTheory.Doubling.IsKFinite K φ) : GlobalTheory.Doubling.IsKFinite K (Rder θ V τ X φ) := by
  obtain ⟨W, hW, m⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  refine GlobalTheory.Doubling.isKFinite_iff.2
    ⟨(Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (fg_comap hW)).map _), fun k hk => ?_⟩
  have hr : ∀ k ∈ K, IsRealPt θ k := fun k hk => ⟨hK hk, FockCompare.RealAction.infMat_mem_UH hθ V k⟩
  have hi := hr _ (inv_mem hk)
  refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ X))
    (n := ⟨rTr V k φ, rTr_mem hθ (hr k hk) hs⟩) (m k hk), ?_⟩
  rw [Submodule.subtype_apply, derEnd_coe hθ (adAt_mem hi hX)]
  funext g
  have := congrFun (Rder_rTr hθ hi hX (rTr V k φ)) (g * k)
  rw [show rTr V k⁻¹ (rTr V k φ) = φ from funext fun y => by simp [rTr]] at this
  rw [this, rTr, mul_inv_cancel_right]

theorem isCuspFun_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IsCuspFun V (Rder θ V τ X φ) := by
  have h' := isAutFunSm_Rder hθ hX h
  refine (isCuspFun_iff h'.left).2 fun W hW => funext fun x => ?_
  have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff h.left).1 hc W hW
  have := hasDerivAt_constTermOn (cocompact_single hW) h.left h.cont h'.left h'.cont (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
    (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.smooth hX)) x
  rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
  exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

end GlobalTheory.CuspLie

end
end

