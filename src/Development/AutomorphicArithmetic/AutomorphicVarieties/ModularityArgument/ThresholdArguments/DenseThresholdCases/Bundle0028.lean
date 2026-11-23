module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SphUntw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.UnramifiedAlgebraicWeights
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphUntw
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
section WD
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem comm_one {G H : Type} [Group G] [CommGroup H] (f : G →* H) (s t : G) : f ⁅s, t⁆ = 1 := by
  rw [map_commutatorElement]
  exact (Commute.all _ _).commutator_eq
private theorem lpDim_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).lpDim = x.lpDim := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.lpDim_mk, WD.lpDim_mk]
private theorem gd_lpTwist {x : WD h} (hx : Gd x) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : Gd (x.lpTwist ξ hξ) := by
  refine ⟨fun s t => ?_, (GlobalTheory.GalCut7.IwahoriTwist.monodromy_vanishes_weilTwist_iff x ξ hξ).2 hx.2⟩
  have h1 : WD.charPol x ⁅s, t⁆ = _ := hx.1 s t
  show WD.charPol _ _ = _
  rw [GlobalTheory.GalCut.SsTwist.charPol_lpTwist, comm_one ξ s t, lpDim_lpTwist, h1]
  simp
end WD
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem good_chars {n : ℕ} {x : IrrGL (k := k)} (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hs : HasSupport x.rep (GlobalTheory.RoadU.chars ξ hξ)) : Good x := by
  refine ⟨_, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
  simp [IrrGL.ofChar]
private theorem good_zero (τ : SmIrr (GL (Fin 0) k)) : Good (IrrGL.of τ.ρ τ.smooth τ.irred) := by
  obtain ⟨t, x, hx, -, hc, -, hs⟩ := GlobalTheory.BCen.SuppEmbed.exists_embedding_prodIrr_support k 0 _ τ.ρ τ.smooth τ.irred
  refine ⟨_, ((hs _).2 rfl).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred), fun y hy => ?_⟩
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
  have h0 := (Finset.sum_eq_zero_iff.1 hx) a (Finset.mem_univ a)
  have h1 := (hc a).1
  omega
end Loc
theorem sphUntw_alt : _root_.UpperTheory.V.Z.Desc.W.SphUntwAlt := by
  intro _ K Ω _ _ _ _ _ n κ w τ τ' B hB ⟨e⟩
  have hχ : IsSmoothChar (κ.loc w) := GlobalTheory.HeckeComp.smooth_loc κ w
  have ex : (IrrGL.of τ.ρ τ.smooth τ.irred).tw (κ.loc w) hχ = IrrGL.of τ'.ρ τ'.smooth τ'.irred := by
    rw [IrrGL.tw_of]
    exact IrrGL.of_eq_of.2 ⟨e.symm⟩
  have ex' : IrrGL.of τ.ρ τ.smooth τ.irred = (IrrGL.of τ'.ρ τ'.smooth τ'.irred).tw (κ.loc w)⁻¹ hχ.inv := by
    rw [← ex, IrrGL.tw_tw]
    simp only [mul_inv_cancel, IrrGL.tw_one]
  have hGG : Good (IrrGL.of τ'.ρ τ'.smooth τ'.irred) ∧ Good (IrrGL.of τ.ρ τ.smooth τ.irred) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨good_zero τ', good_zero τ⟩
    · obtain ⟨ξ, hξ, -, hs, -⟩ := GlobalTheory.T.supercuspidal_support_characters K n hn w τ' B hB
      have h1 := GlobalTheory.RoadU.CharTwist.hasSupport_rep_tw hs _ hχ.inv
      rw [GlobalTheory.RoadU.CharTwist.chars_tw, ← ex'] at h1
      exact ⟨good_chars ξ hξ hs, good_chars _ _ h1⟩
  obtain ⟨hG', hG⟩ := hGG
  refine ⟨hG, fun A h rc hrc => ?_⟩
  obtain ⟨b, hb, ε, L⟩ := toV' hrc
  have hsph := GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB
  have hu : (rc (IrrGL.of τ'.ρ τ'.smooth τ'.irred)).unr :=
    (L.sph _).1 (fixed_ne_bot_of_equiv (IrrGL.equivOf τ'.ρ τ'.smooth τ'.irred) hsph)
  have hg := (UpperTheory.V.Z.Win.Gu.gdLaws K Ω A w h).2.2.2 _ hu
  rw [algNorm, L.nu_eq, (UpperTheory.V.Z.Win.Gu.gdLaws K Ω A w h).2.1, ex', L.twist _ _ _ hG', L.one, lpChar_lpOfChar]
  exact gd_lpTwist hg _ _
end UpperTheory.V.Z.Desc.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSplitSat
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne GlobalTheory.LFun GlobalTheory.PRep UpperTheory.V.Af.Gu
private theorem sat_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv ρ') {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' B := by
  have he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    e.toIntertwiningMap.isIntertwining _ _ g v
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    have h1 := hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    refine (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map
      e.toLinearEquiv.toLinearMap he h0
    rw [he]
    exact GlobalTheory.LGrp.mem_fixed.1 hy k hk
theorem UpperTheory.V.Z.Desc.W.splitSat_alt :
    _root_.UpperTheory.V.Z.Desc.W.SplitSatAlt := by
  rintro - E _ _ n c a d hn w ρ σ had hsp S hS τ ⟨e⟩ B hB
  obtain ⟨S', s1, s2⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d hn ρ σ (fun i => (had i).2) hsp B (sat_of_equiv e hB)
  obtain rfl : S = S' := funext fun i => (hS i).unique (s1 i)
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] at s2
  apply Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective
  rw [← s2]
  unfold satTot
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Multiset.coe_mapAddMonoidHom (fun z : ℂˣ => (z : ℂ)), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  have hq : Ideal.absNorm w.asIdeal = normV w := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  simp only [Function.comp_apply, Units.val_mul, coe_qPow, Fin.revPerm_apply, Fin.val_rev, hq]
  congr 2
  rw [Nat.cast_sub k.2]
  push_cast
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
section Real
variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]
private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))
private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp
private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩
private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
    simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]
private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm
private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]
end Real
private theorem expo_intC {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (τ : E →+* ℂ) : expo χ τ = n τ := by
  refine (GlobalTheory.CuspRep.InfType.expo_of_infType E χ).1 n (fun k => h k fun φ => ?_) τ
  exact absurd (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
private theorem reg_shift {n : ℕ} {m : Multiset ℂ} (h2 : m.Nodup) (h3 : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2)
    {s : ℂ} (hs : ∃ k : ℤ, s = k) :
    (m.map (· + s)).Nodup ∧ ∀ z ∈ m.map (· + s), ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  obtain ⟨j, rfl⟩ := hs
  refine ⟨h2.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h3 y hy
  exact ⟨k + j, by push_cast; ring⟩
theorem UpperTheory.V.Af.twist_invariance_automorphic :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.Twi := by
  rintro - F Ω _ _ _ _ _ l _ ι n r κ ⟨sat, inf, hc, hr, hA⟩ ⟨χ, -, art, a, ha, hχ, hL⟩
  rcases hc with ⟨_, π, rfl, rfl⟩ | ⟨_, π, rfl, rfl⟩
  · refine ⟨_, _, Or.inl ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hA art χ a κ ha hL⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 ⟨_, expo_intC hχ τ⟩⟩
  · refine ⟨_, _, Or.inr ⟨inferInstance, π.twist χ, rfl, rfl⟩, fun τ => ?_,
      sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
    obtain ⟨m, h1, h2, h3⟩ := hr τ
    exact ⟨_, h1.twist χ, reg_shift h2 h3 (expo_intR hχ _)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedAlgebraicWeights
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.NewLevel
open UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
private theorem level_zero_eq_maximal_compact (w : HeightOneSpectrum (𝓞 ℚ)) : UpperTheory.V.Sd.K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers ℚ ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _
private theorem locGL_comm' {v w : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion ℚ))
    (k : GL (Fin 2) (w.adicCompletion ℚ)) : locGL ℚ 2 v g * locGL ℚ 2 w k = locGL ℚ 2 w k * locGL ℚ 2 v g := by
  refine UpperTheory.V.Af.GlobalFixedVectors.gl_ext fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]
private theorem normV_surj' {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp
private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j
private noncomputable def LowS (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) :=
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2)))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0))) ⊓
  (⨅ v : InfinitePlace ℚ, LinearMap.ker (Eo v 0 0 + Eo v 1 1))
private theorem mem_LowS {k : ℕ} {φ : TR.Sm ℚ 2} : φ ∈ LowS k ↔ ((∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (k : ℂ)) • φ) ∧
      (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) ∧
      (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0)) := by
  simp only [LowS, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply, sub_eq_zero, and_assoc]
private theorem lowS_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : φ ∈ LowS k) (u : GL (Fin 2) (Af ℚ)) : TR.finRep ℚ 2 u φ ∈ LowS k := by
  obtain ⟨h1, h2, h3⟩ := mem_LowS.1 h
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine mem_LowS.2 ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h1, map_smul]
  · rw [e, e, e, e, ← map_sub, h2, map_smul, map_add (f := _)]
  · rw [e, e, ← map_add (f := _), h3, map_zero]
theorem not_dvd_level_of_satake_hecke_poly_cofinite : _root_.UpperTheory.V.Af.Hypotheses' → Published.CuspSemisimpleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π : TR.CuspSub ℚ 2),
    (∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) →
    ∀ (w : Pl) (Bs : Multiset ℂˣ), π.HasSat w Bs → ¬ normV w ∣ g.M := by
  intro P hS k hk g j π hπ w Bs hw hd
  have hM : 1 ≤ g.M := g.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨π₀, ψ, hψ, hψ0, hlev, hlow, hsat⟩ := UpperTheory.V.Z.Kato.NewVec.newVec hS P.admR k hk g
  obtain ⟨B, hB⟩ := GlobalTheory.NewLevel.spherical_of_normTwist P.smoR k hk g j π π₀ hπ hsat w Bs hw
  let L : Submodule ℂ (TR.Sm ℚ 2) :=
    LowS k ⊓ ⨅ q, ⨅ (_ : q ≠ w), Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))
  let U : Submodule ℂ π₀.V := L.comap π₀.V.subtype
  have hU : ∀ h, ∀ x ∈ U, π₀.locRep w h x ∈ U := by
    intro h x hx
    simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hx ⊢
    refine ⟨lowS_fin hx.1 _, fun q hq u hu => ?_⟩
    have h1 : TR.finRep ℚ 2 (locGL ℚ 2 q u) x.1 = x.1 := hx.2 q hq u hu
    change TR.finRep ℚ 2 (locGL ℚ 2 q u) (TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1) = TR.finRep ℚ 2 (locGL ℚ 2 w h) x.1
    rw [← Module.End.mul_apply, ← map_mul, locGL_comm' hq, map_mul, Module.End.mul_apply, h1]
  have hU0 : U ≠ ⊥ := by
    intro h
    have hm : (⟨ψ, hψ⟩ : π₀.V) ∈ U := by
      simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
      exact ⟨mem_LowS.2 hlow, fun q _ => hlev q⟩
    rw [h, Submodule.mem_bot] at hm
    exact hψ0 (congrArg Subtype.val hm)
  obtain ⟨σ, hσ⟩ := (_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P ℚ 2 π₀ w).1
  have hiso := (_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P ℚ 2 π₀ w).2 σ hσ
  have hσf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := by
    refine hiso.hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w 2).2 ?_
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    exact ⟨y, hy0, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hy u hu⟩
  obtain ⟨x, hxU, hx0, hxf⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed σ.ρ σ.irred (π₀.locRep w) hiso.2 U hU hU0 _ hσf
  simp only [U, L, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply] at hxU
  obtain ⟨hxl, hxq⟩ := hxU
  obtain ⟨hwt, hlo, hone⟩ := mem_LowS.1 hxl
  have hx0' : (x : TR.Sm ℚ 2) ≠ 0 := fun e => hx0 (Subtype.ext e)
  have hp := (places w).1
  have hN : 1 ≤ g.M / normV w := Nat.div_pos (Nat.le_of_dvd hM hd) hp.pos
  have hNM : g.M / normV w ∣ g.M := Nat.div_dvd_of_dvd hd
  have hNne : g.M / normV w ≠ g.M := (Nat.div_lt_self hM hp.one_lt).ne
  have hcusp := π₀.cusp x.1 x.2
  have hfix : ∀ u ∈ K1G (g.M / normV w), TR.finRep ℚ 2 u x.1 = x.1 :=
    GlobalTheory.NewLevelInv.inv_K1G g.M w hM hd x.1 hcusp.1.level (fun q hq => hxq q hq) (by
      rw [level_zero_eq_maximal_compact]; exact fun u hu => congrArg Subtype.val (hxf u hu))
  obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt P ℚ π₀
  have hc : ∀ (z : Ideles ℚ) (g' : GA ℚ 2),
      x.1.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g') = ((ω.1 z : ℂˣ) : ℂ) * x.1.1 g' :=
    fun z g' => hω z x.1 x.2 g'
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Br.charOf _ hN ω x.1 hx0' hone hfix hc
  obtain ⟨f, hf, hL⟩ := UpperTheory.V.Br.deadel k _ hN χ ω hχ x.1 hcusp ⟨hwt, hlo, hone⟩ hfix hc
  haveI : NeZero (g.M / normV w) := ⟨by omega⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine hx0' (Subtype.ext (funext fun g' => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp _ hN g'
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : UpperTheory.V.Sd.IsHol k (lev (g.M / normV w)) ω x.1 :=
    ⟨hcusp.1, fun q u hu => hfix _ (kLocal _ hN q u hu), hc, hwt, hlo⟩
  refine hf0 (g.new _ hNM hNne f χ hf ?_)
  refine Filter.eventually_cofinite.2 ((Set.finite_le_nat g.M).subset fun q hq => ?_)
  simp only [Set.mem_setOf_eq] at hq
  have hqp : Nat.Prime q := by
    by_contra h
    exact hq (fun hp => False.elim (h hp))
  by_contra hqM
  have hqd : ¬ q ∣ g.M := fun h => hqM (Nat.le_of_dvd hM h)
  obtain ⟨wq, rfl⟩ := normV_surj' hqp
  obtain ⟨α, β, hq2, hsum, -⟩ := hsat wq hqd
  have hqN : ¬ normV wq ∣ g.M / normV w := fun h => hqd (h.trans hNM)
  have hv : GlobalTheory.LFun.IsSatVecGL wq (UpperTheory.V.Sd.locSm ℚ wq) x.1 {α, β} :=
    (hq2.2 x (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal _ hN wq u (by
      rwa [(places wq).2.2.2 _ hN hqN, level_zero_eq_maximal_compact])))) hx0).map π₀.V.subtype (fun _ _ => rfl) hx0'
  obtain ⟨h1, -⟩ := UpperTheory.V.Br.eigOf k _ hk1 hN χ ω hχ f x.1 hL hhol wq α β hqN hv
  rw [hsum] at h1
  exact hq (fun _ => h1)
end GlobalTheory.NewLevel
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWAutKQ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.GalN.V.autKQ0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ), Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → AutP ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) := by
  intro hP K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r wt hc hr ⟨θ, hθ, hd⟩ hirr
  obtain ⟨P, hreg, hA⟩ := hr hc K hK hirr
  obtain ⟨χ, -, hpol, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP.toClassicalTheorems K hK n hn l Ω ι r wt θ P hθ hd hA
  exact ⟨P, hreg, ⟨χ, hpol⟩, hA⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af
theorem UpperTheory.GalN.V.automorphy_bridge_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Af.AutBridgeAlt := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hNotBoth (hR : IsTotallyReal F) (hC : _root_.NumberField.IsTotallyComplex F) : False := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex v)) (hR.isReal v)
  have hC : ∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    have hRegInf (π : CuspSub F n) : RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
      refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩)
        (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
      rintro ⟨m, hm, h⟩
      rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
      exact h
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
      · exact (hNotBoth h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    have hRegInf (π : TR.CuspSub F n) :
        RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
      refine ⟨fun h v => ?_, fun h τ => h _⟩
      simpa only [InfinitePlace.mk_embedding] using h v.embedding
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (hNotBoth hF h).elim
      · exact ⟨π, (hRegInf π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (hRegInf π).2 hr, ha⟩
  · intro _ h0
    obtain ⟨π, hr, -, ha⟩ := _root_.UpperTheory.GalN.V.autCsd0_of_isAutCsdA h0
    exact hC.2 ⟨π, hr, ha⟩
end
end

