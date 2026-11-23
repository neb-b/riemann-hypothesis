module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
section
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

private theorem regInf_iff {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) :
    RegInf n π.HasInfChar ↔ (CG.mk π).IsRegAlg := by
  refine Iff.trans (forall_congr' fun τ => ⟨?_, fun h => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, h⟩⟩) (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm
  rintro ⟨m, hm, h⟩
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
  exact h

private theorem regInf_iff_real {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (π : TR.CuspSub F n) :
    RegInf n (fun τ : F →+* ℂ => π.HasInfChar (InfinitePlace.mk τ)) ↔ π.IsRegAlg := by
  refine ⟨fun h v => ?_, fun h τ => h _⟩
  have := h v.embedding
  simpa only [InfinitePlace.mk_embedding] using this

theorem UpperTheory.V.Af.autBridge :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.AutBridge := by
  intro _ F Ω _ _ _ _ l _ ι n r
  have hC : ∀ [_root_.NumberField.IsTotallyComplex F], IsAut ι r ↔ ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π := by
    intro hF
    constructor
    · rintro ⟨sat, inf, ⟨_, π, rfl, rfl⟩ | ⟨h, -⟩, hr, ha⟩
      · exact ⟨π, (regInf_iff π).1 hr, ha⟩
      · exact (not_both F h hF).elim
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inl ⟨hF, π, rfl, rfl⟩, (regInf_iff π).2 hr, ha⟩
  refine ⟨?_, hC, ?_⟩
  · intro hF
    constructor
    · rintro ⟨sat, inf, ⟨h, -⟩ | ⟨_, π, rfl, rfl⟩, hr, ha⟩
      · exact (not_both F hF h).elim
      · exact ⟨π, (regInf_iff_real π).1 hr, ha⟩
    · rintro ⟨π, hr, ha⟩
      exact ⟨_, _, Or.inr ⟨hF, π, rfl, rfl⟩, (regInf_iff_real π).2 hr, ha⟩
  · rintro _ ⟨π, hr, -, ha⟩
    exact hC.2 ⟨π, hr, ha⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem of_model (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hc : Continuous R) (hs : IsSSRep R) (H : ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ)
    (hr : Continuous r) (ha : AttC ι r π) (w) (σ) (hσ : π.IsLocComp w σ) : LocGlob ι r w σ := by
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => (H w σ hσ A h rc hrc).1 hw, hf⟩
  intro A h rc hrc
  obtain ⟨h1, h2⟩ := H w σ hσ A h rc hrc
  refine ⟨fun hw => (h1 hw).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], fun O _ _ _ Bw hj => ?_⟩
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) (h2 O Bw hj).1
  exact ⟨h3.1, by rw [h3.2]; exact (h2 O Bw hj).2⟩

private theorem cls_char {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E)
    {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (h : ((CuspSub.triv E le_rfl).twist χ).IsLocComp w σ) (hχ) :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (χ.loc w) hχ := by
  obtain ⟨f, h0, hf⟩ := h
  have hop : ∀ g (x : ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V),
      ((CuspSub.triv E le_rfl).twist χ).locRep w g x = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • x := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_triv_twist, ← CuspSub.chiDet_locGL]
    simp [opMul, opTriv, opAdd]
  let L : ℂ ≃ₗ[ℂ] ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ _ (oneFn E 1) oneFn_ne_zero).trans ((CuspSub.triv E le_rfl).toTwist χ)
  let f' : σ.V →ₗ[ℂ] ℂ := L.symm.toLinearMap ∘ₗ f
  have hf' : ∀ g v, f' (σ.ρ g v) = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • f' v := fun g v => by simp [f', hf, hop]
  have h0' : f' ≠ 0 := fun h => h0 (LinearMap.ext fun v => L.symm.injective (by simpa [f'] using LinearMap.congr_fun h v))
  have hinj : Function.Injective f' := by
    rcases ((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f') (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢; rw [hf', hv, smul_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0'
  have hsurj : Function.Surjective f' := LinearMap.range_eq_top.1
    ((eq_bot_or_eq_top (LinearMap.range f')).resolve_left fun h => h0' (LinearMap.range_eq_bot.1 h))
  refine (IrrGL.of_eq_of (σ := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).ρ) (hs' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).smooth)
    (hi' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).irr)).2 ⟨.mk (LinearEquiv.ofBijective f' ⟨hinj, hsurj⟩) fun g => ?_⟩
  ext v
  exact hf' g v

private theorem rank_one (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {π : CuspSub K 1} (hreg : (CG.mk π).IsRegAlg) :
    ∃ R : G K Ω →* GL (Fin 1) (Qbar l), Continuous R ∧ IsSSRep R ∧ ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose m hm using (CG.isRegAlg_ofChar χ).1 hreg
  have hχ := _root_.GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo K χ m hm
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμ, hL⟩, -⟩ := hμ l ι χ m hχ
  have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
    fun g => rfl
  have hc : Continuous (GlobalTheory.TripleGal.rk1 μ) := by
    refine (Continuous.units_map _ ?_).comp hμ
    exact continuous_matrix fun i j => by
      fin_cases i; fin_cases j
      simpa using continuous_id'
  refine ⟨_, hc, fun W _ => ?_, fun w σ hσ A h rc hrc => ?_⟩
  · obtain ⟨W', hW⟩ := W.exists_isCompl
    refine ⟨W', fun g v hv => ?_, hW⟩
    have := W'.smul_mem (μ g : Qbar l) hv
    convert this using 1
    ext i
    simp [hval, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hcp := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have e0 : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
  rw [rec_algNorm hrc, e0, WD.lpTw_zero, cls_char χ hσ hcp.1]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hcp.1]
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ⟨?_, ?_⟩⟩
  · have h1 := isWDOf_wdOf (h := h) (r := GlobalTheory.TripleGal.rk1 μ) hw ι (Units.continuous_val.comp hc)
    rwa [wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (χ.loc w).comp a) fun _ => ha.smooth hcp.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h1
  · obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val))
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.litN.aut.chA K Ω l _ _ ⟨T⟩ ι art hart χ m μ hχ hμ hL w A h O Bw hj).1
  · exact Lev.SsCmp.of_eq (P.litN.aut.chW K Ω l _ _ (Loc.tiedP l) ι art hart χ m μ hχ hμ hL w A h O Bw hj _ hcp a ha)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatCsd :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CompatCsd := by
  intro PH F Ω _ _ _ _ _ _ l _ ι n hn r π hr hreg hd ha
  have P := PH.toClassicalTheorems
  rcases hn.eq_or_lt with rfl | hn
  · obtain ⟨R, hc, hs, H⟩ := rank_one (Ω := Ω) P ι hreg
    exact of_model P hc hs H hr ha
  · obtain ⟨R, hc, hs, Haw, Hab⟩ := P.ss F Ω l ι n hn π hd (P.litN.aut.coh F n (by omega) π hreg)
    refine of_model P hc hs (fun w σ hσ A h rc hrc => ⟨fun hw => Haw w hw A h rc hrc σ hσ, fun O _ _ _ Bw hj => ?_⟩) hr ha
    have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
    exact ⟨h1.1, h1.2 σ hσ rc hrc⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
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
    change InfinitePlace.Completion.ringEquivRealOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    simp
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

theorem UpperTheory.V.Af.twi :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.Twi := by
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

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
section
theorem UpperTheory.V.Af.satK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.SatK := by
  intro P K _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := locCompC P K n π w
  exact sat_of_isotypic (satLoc P) π.finPart hπ w hw σ (h σ hσ)
end

