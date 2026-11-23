module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwAway
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem det_rank_one_rep {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
  ext g
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
private theorem tw_eq {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l)) (μ : Γ →* (Qbar l)ˣ) :
    Af.tw R μ = Formalism.MainNotions.SumRepresentations.At.twGL R (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
  rw [det_rank_one_rep]
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
theorem UpperTheory.V.Z.Desc.W.twist_away_statement : _root_.UpperTheory.V.Z.Desc.W.TwAwayAlt := by
  intro P K Ω _ _ _ _ _ _ l _ ι n R hR art κ m μ hart hμ hL w hw τ τ' hG he A h rc hrc h1
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  obtain ⟨a, ha, ε, HL⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  have e : rc (algNorm τ') = (rc (algNorm τ)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [algNorm, algNorm, HL.nu_eq, HL.nu_eq, GlobalTheory.NuShift.lpChar_lpTw, ← HL.twist _ _ _ hG, GlobalTheory.LocGL.IrrGL.tw_of]
    exact congrArg (fun x => (rc x).lpTw _) (IrrGL.of_eq_of.2 he)
  rw [e, HL.one _ hc.1]
  have hcR := Units.continuous_val.comp hR
  have hct : Continuous fun g => ((Af.tw R μ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    simp only [Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul hcR
  have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
    fun g => rfl
  have h3 := isWDOf_wdOf (h := h) (r := Af.tw R μ) hw ι hct
  have h4 := wdOf_twGL_det K Ω A w h l hw ι n R _ hcR (continuous_rank_one_rep hμ)
  rw [← tw_eq, h1.wdOf_eq hw,
    wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (κ.loc w).comp a) fun _ => ha.smooth hc.1) rfl fun g => by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [Subsingleton.elim i 0]
    simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h4
  rw [h4] at h3
  exact h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base
namespace UpperTheory.V.Sd.Tw
section
variable {Ω : Type} [Field Ω]
private theorem not_lt_of_coprime (A : ValuationSubring Ω) {q n : ℕ} (hq : A.valuation (q : Ω) < 1) (h : q.Coprime n) :
    ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : Ω) = (a : Ω) * q + (b : Ω) * n := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 a _ hq) (h1 b _ hn)
  rw [← e, map_one] at this
  exact lt_irrefl _ this
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem cls_frob {A : ValuationSubring Ω} {q N : ℕ} [NeZero N] (hq : A.valuation (q : Ω) < 1) (h : q.Coprime N)
    {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : Chr.cls ℚ Ω N t = ZMod.unitOfCoprime q h := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 t _ fun ζ hζ => ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  refine eq_of_pow_eq_one A (not_lt_of_coprime A hq h) ?_ ?_
    (ht.2 ζ (valuation_eq_one_of_pow_eq_one A (NeZero.ne N) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
private theorem cyc_frob {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {q : ℕ} (hp : q.Prime) (hq : A.valuation (q : Ω) < 1)
    (h : q.Coprime l) {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) = q := by
  haveI : Fact q.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω q A).1 fun hA => ((places ℚ Ω q A).2.1 hA).2 hq
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun hm =>
    not_lt_of_coprime A hq h (((places ℚ Ω l A).2.2.1 v hv).2 hm)
  have e : ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp fun n => cycZ_toZModPow_eq hl hv ht.2 n
  change ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = _
  rw [e, map_natCast]
private theorem continuous_cyc (l : ℕ) [Fact l.Prime] :
    Continuous fun t : G ℚ Ω => ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) :=
  ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))
variable (K : Type) [Field K] [NumberField K] [Algebra K Ω]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_notMem [_root_.NumberField.IsTotallyComplex K] {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]
private theorem exists_chi [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) (N : ℕ) [NeZero N] (hN : N = (discr K).natAbs) :
    (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω ∧ ∃ χ : (ZMod N)ˣ →* ℂˣ, χ ^ 2 = 1 ∧
      ∀ t : G ℚ Ω, t ∉ galOf ℚ K Ω → χ (Chr.cls ℚ Ω N t) = -1 := by
  classical
  have hker : (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω := fun s hs => quadMu K Ω hK s fun ζ hζ => by
    rw [← hN] at hζ
    rw [Chr.cls_spec N s ζ hζ, MonoidHom.mem_ker.1 hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
  let δ : G ℚ Ω →* ℂˣ := MonoidHom.mk' (fun s => if s ∈ galOf ℚ K Ω then 1 else -1) fun a b => by
    by_cases ha : a ∈ galOf ℚ K Ω <;> by_cases hb : b ∈ galOf ℚ K Ω <;>
      simp [Subgroup.mul_mem_iff_of_index_two hi, ha, hb]
  have hδ : (Chr.cls ℚ Ω N).ker ≤ δ.ker := fun s hs => if_pos (hker hs)
  have hs := (Chr.clsOnto Ω N).1
  have e : ∀ t, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩ (Chr.cls ℚ Ω N t) = δ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  refine ⟨hker, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩, MonoidHom.ext fun u => ?_, fun t ht => (e t).trans (if_neg ht)⟩
  obtain ⟨t, rfl⟩ := hs u
  rw [MonoidHom.pow_apply, e]
  change (if t ∈ galOf ℚ K Ω then (1 : ℂˣ) else -1) ^ 2 = 1
  split_ifs <;> simp
private theorem ver_of_frob [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] (κ : G K Ω →* (Qbar l)ˣ)
    (hκ : Continuous κ) (T : ℕ) (hT : T ≠ 0)
    (H : ∀ (q : ℕ) (A : ValuationSubring Ω) (t : G ℚ Ω) (s : G K Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 →
      IsFrob (F := ℚ) A q t → t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t →
      (κ s : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1)
    (s : G K Ω) (t : G ℚ Ω) (ht : t ∉ galOf ℚ K Ω) (hs : galEmb ℚ K Ω s = t * t) : κ s = -(cycBar ℚ Ω l t)⁻¹ := by
  obtain ⟨hemb, hopen, hi⟩ := galEmbTop ℚ K Ω
  have hsq : ∀ t : G ℚ Ω, ∃ s, galEmb ℚ K Ω s = t * t := fun t => by
    have := Subgroup.mul_self_mem_of_index_two (hi.trans hK) t
    rw [← range_galEmb] at this
    exact this
  choose g hg using hsq
  have hgc : Continuous g := hemb.continuous_iff.2 ((continuous_id.mul continuous_id).congr fun t => (hg t).symm)
  have hcl : IsClosed {t : G ℚ Ω | (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1} :=
    isClosed_eq ((Units.continuous_val.comp (hκ.comp hgc)).mul (continuous_cyc l)) continuous_const
  have key : (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1 := by
    by_contra hne
    obtain ⟨q, A, φ, hq, hqT, hA, hφ, h1, h2⟩ := ML.chebQ Ω _
      (hcl.isOpen_compl.inter ((galOf ℚ K Ω).isClosed_of_isOpen hopen).isOpen_compl) ⟨t, hne, ht⟩ T hT
    exact h1 (H q A φ (g φ) hq hqT hA hφ h2 (hg φ))
  rw [hemb.injective ((hg t).trans hs.symm)] at key
  rw [← mul_left_inj (cycBar ℚ Ω l t), neg_mul, inv_mul_cancel]
  exact Units.ext key
end
end UpperTheory.V.Sd.Tw
open UpperTheory.V.Sd.Tw in
theorem UpperTheory.V.Sd.twist_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Twist := by
  intro hP K Ω _ _ _ _ _ _ _ hK l hl hl2 hld ι c hc
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  set N := (discr K).natAbs with hN
  have hN3 : 3 ≤ N := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [Int.abs_eq_natAbs] at this
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hker, χ, hχ2, hχ⟩ := exists_chi (Ω := Ω) K hK N hN
  have hχ1 : χ (-1) = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.2.2.1 c hc]
    exact hχ c (cc_notMem K hc)
  obtain ⟨Y, a, τ, hYa, ha1, ha0, hYu, ⟨m, hm0, hml, hm⟩, hYv⟩ := hecke K hK l hl.out hl2 hld N hN3 χ hχ2 hχ1
  obtain ⟨art, hart⟩ : ∃ art : Ideles K →* Gab K Ω, IsGlobalArtin art := hP.litN.aut.art K Ω
  obtain ⟨κ, hκ, hL⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hYa)
  have hNd : ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → (N : 𝓞 K) ∉ v.asIdeal := fun v hv h => by
    apply hv
    rcases Int.natAbs_eq (discr K) with e | e
    · rw [e, Int.cast_natCast]
      exact h
    · rw [e, Int.cast_neg, Int.cast_natCast]
      exact neg_mem h
  have hnat : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℤ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn h => by
    have := (hw (n : 𝓞 K)).2 h
    exact hn (by simpa using this)
  have hnat' : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℕ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn => by
    simpa using hnat A w hw n (by simpa using hn)
  have hver := ver_of_frob K hK κ hκ (l * N) (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) fun q A t s hq hqT hA ht htK hs => by
    have hc' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqT
    have hql := hc'.coprime_mul_right_right
    have hqN := hc'.coprime_mul_left_right
    have hAN := not_lt_of_coprime A hA hqN
    obtain ⟨w, hw, hwq, hfr⟩ := inert K Ω hK q hq A hA (((Chr.clsFacts ℚ Ω N).2.2.2.2 A hAN).trans hker) t ht htK
    rw [hL.frob_unr hart (Or.inl (hnat' A w hw l (not_lt_of_coprime A hA hql))) (hYu w (hnat' A w hw N hAN)) hw (hfr s hs),
      hYv q hqN w hwq, ← cls_frob hA hqN ht, hχ t htK, cyc_frob hq hA hql ht]
    have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    simp [hq0]
  refine ⟨κ, hκ, ⟨art, Y, a, τ, hart, isAlgPos_of_isAlg hYa, hL, ha1, ha0, fun v hv => hYu v (hNd v hv)⟩,
    fun s s' h => ?_, hver, fun A hAl hAd s hs => ?_, m, hm0, hml, fun A hAl s hs => ?_⟩
  · have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
    have h1 : galEmb ℚ K Ω s * c ∉ galOf ℚ K Ω := fun h' =>
      cc_notMem K hc (((galOf ℚ K Ω).mul_mem_cancel_left (galEmb_mem ℚ K Ω s)).1 h')
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (cc_sq hc)
    have h3 : cycBar ℚ Ω l c = -1 := by
      have h4 : cycZ ℚ Ω l c = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm c.toRingEquiv from hc)
      change Units.map _ (cycZ ℚ Ω l c) = -1
      rw [h4]
      exact Units.ext (by simp)
    rw [← map_mul, hver (s * s') _ h1 (by rw [map_mul, h, h2]; simp only [mul_assoc]), map_mul, h3, mul_neg_one, inv_neg, neg_neg]
    rfl
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      exact (hL.unr_iff hart (Or.inl (hnat' A w hw l hAl)) hw).2 (hYu w (hNd w (hnat A w hw _ hAd))) s hs
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one, one_pow]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inl (hnat' A w hw l hAl)) hw _).1 ⟨s, hs, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, hm w x hx]
      simp
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAbove
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd
private theorem cont_diag {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} (hr : Continuous r) {H : Subgroup Γ} {κ : Fin n → ↥H →* (Qbar l)ˣ}
    (hf : IsFlagOn r H κ) (i : Fin n) : Continuous fun s => (κ i s : Qbar l) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s : ↥H => (g * r s * g⁻¹ : GL (Fin n) (Qbar l)) :=
    (continuous_const.mul (hr.comp continuous_subtype_val)).mul continuous_const
  exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (hg s).2 i
private theorem transport_rho {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {n : ℕ} (a : WDRep h W) (b : Basis (Fin n) ℂ W) (σ : ↥(Weil h))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : LinearMap.toMatrix b b (a.ρ σ) = X) :
    (a.transport b.equivFun).ρ σ = Matrix.toLin' X := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := b.equivFun.surjective v
  change b.equivFun (a.ρ σ (b.equivFun.symm (b.equivFun x))) = _
  rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, ← hX]
  exact (LinearMap.toMatrix_mulVec_repr b b (a.ρ σ) x).symm
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Af.weil_deligne_above_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAbove := by
  rintro - F Ω _ _ _ _ _ l _ - ι n M hM m r hr w A h O _ _ _ Bw hj κ ⟨χ, hχ, hfl, hI⟩ hp hor
  have hκc := cont_diag hr hfl
  obtain ⟨L, ρ, κL, χL, hV, e, htri, hκ, hχL⟩ := UpperTheory.galois_representation_model_over_finite_extension F Ω l ι n r w A h O Bw hj κ χ
    (fun i => UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ (hχ i)) hfl hp
  obtain ⟨-, hcyc, hK⟩ := UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj
  obtain ⟨K', hK'⟩ := hK M hM
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype
  let ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ := fun i => κ i * ε ^ (-m i)
  let μ : ↥(Weil h) → Fin n → ℂ := fun σ i => ((normV w : ℕ) : ℂ) ^ (m i * deg σ) * ι (ψ i (inc σ) : Qbar l)
  have hεc : Continuous fun s => (ε s : Qbar l) := by
    have h0 : Continuous fun g : GQ l => (((Loc.PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
      obtain ⟨hc, -, hq⟩ := Loc.cycFacts l l
      simp only [hq]
      have h0 : Continuous fun g : GQ l => ((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) := Units.continuous_val.comp hc
      exact continuous_subtype_val.comp h0
    exact ((continuous_algebraMap ℚ_[l] (Om l)).comp (h0.comp (continuous_subtype_val.comp Bw.e_cont))).congr
      fun s => hcyc L s
  have hψc : ∀ i, Continuous fun s => (ψ i s : Qbar l) := fun i => by
    refine ((hκc i).mul (hεc.zpow₀ (-m i) fun s => Or.inl (Units.ne_zero _))).congr fun s => ?_
    simp [ψ]
  haveI := hV.finite
  have T := UpperTheory.weilDeligne_triangularizable F Ω l ι w A h O Bw hj L n _ ρ κL μ htri (fun i hi σ y => by
    refine (UpperTheory.cyclotomicWeilChar_properties F Ω l ι w A h O Bw hj L (κL i) (χL i) (m i) ?_ ⟨K', fun g hg => ?_⟩ (fun g hg => ?_) hi σ y).trans ?_
    · refine ((hκc i).comp Bw.e_symm_cont).congr fun g => ?_
      rw [Function.comp_apply, ← hκ, MulEquiv.apply_symm_apply]
    · obtain ⟨s, rfl⟩ := Bw.e.surjective g
      refine Units.ext (Subtype.ext ?_)
      rw [hχL, hχ i s (hK' s hg)]
      rfl
    · obtain ⟨s, rfl⟩ := GlobalTheory.PstLaws.exists_ine_of_fix Bw h hj g hg
      refine Units.ext (Subtype.ext ?_)
      have h1 := congrArg Units.val (hI i (inc (ineIncl h s)) s.2)
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, ← hκ, ← hχL, ← hcyc L] at h1
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      exact h1.trans (by congr 1)
    · congr 3
      have h1 : (ψ i (inc σ) : Qbar l) = (κ i (inc σ) : Qbar l) * (cycBar F Ω l (inc σ) : Qbar l) ^ (-m i) := by
        simp [ψ, ε]
      rw [h1, ← hκ, ← hcyc L, Units.val_mul, Units.val_zpow_eq_zpow_val, MulMemClass.coe_mul]
      congr 1) hV
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hN : wdN (Loc.PP l) ι ρ = 0 := by
    rcases hor with hne | ⟨O', _, _, _, Bw', hj', hpc⟩
    · by_contra h0
      obtain ⟨i, j, hij⟩ := UpperTheory.weilDeligne_monodromy_upperTriangular ℂ _ _ n _ _ _ μ (wdRho_wdN (Loc.PP l) ι Bw h hj ρ) T h0
      obtain ⟨ha, h1⟩ := UpperTheory.continuous_character_compact_unit_values F Ω l ι w A h (hj.mem_placesOver h) (ψ i * (ψ j)⁻¹) (1 + m j - m i)
        (by
          refine ((hψc i).mul ((hψc j).inv₀ fun s => Units.ne_zero _)).congr fun s => ?_
          simp) (fun σ => by
          have h2 := hij σ
          have h3 : ι (ψ j (inc σ) : Qbar l) ≠ 0 := (map_ne_zero ι).mpr (Units.ne_zero _)
          have h4 : ((normV w : ℕ) : ℂ) ^ (m i * deg σ) ≠ 0 := zpow_ne_zero _ hq
          change ι ((ψ i (inc σ) * (ψ j (inc σ))⁻¹ : (Qbar l)ˣ) : Qbar l) = _
          rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, sub_mul, add_mul, one_mul, zpow_sub₀ hq,
            zpow_add₀ hq, mul_inv_eq_iff_eq_mul₀ h3, div_mul_eq_mul_div, eq_div_iff h4, mul_comm, mul_assoc]
          exact h2)
      refine hne i j ?_
      have h5 : ψ i = ψ j := mul_inv_eq_one.mp h1
      have h6 : -m j = 1 + -m i := by omega
      simp only [ψ] at h5
      rw [h6, zpow_add, zpow_one, ← mul_assoc] at h5
      exact mul_right_cancel h5
    · have hc : Continuous fun g : ↥(Dec (F := F) A) =>
          ((r.comp (Dec (F := F) A).subtype g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
        Units.continuous_val.comp (hr.comp continuous_subtype_val)
      have hp' := GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding l _ _ (Loc.tiedP l) F Ω A O O' Bw Bw' hj hj' n _ hc hp
      have h1 := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw' h hj' (Loc.PP l) ι _ hp').2 hpc
      rw [← GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding l _ _ (Loc.tiedP l) ι F Ω A w O O' Bw Bw' h hj hj' n _ hc hp hp', e] at h1
      exact (mono0_wdPst ι Bw h hj hV).1 h1
  obtain ⟨b₀, hb₀⟩ := T
  obtain ⟨b, hb⟩ := UpperTheory.tridiagonal_weil_deligne _ ↥(Ine (F := F) A) n ((wdRho (Loc.PP l) ι Bw h hj ρ).comp (ineIncl h))
    (fun s => μ (ineIncl h s)) (isSmooth_wdRho (Loc.PP l) ι Bw h hj ρ).finite_range
    ⟨b₀, fun s => hb₀ (some (ineIncl h s))⟩
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), (wdRep (Loc.PP l) ι Bw h hj ρ).transport b.equivFun,
    fun i s hs => ?_, ?_, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [e, wdPst_of_isPst ι Bw h hj hV]
    exact (WD.sound (WDRep.iso_transport _ _)).symm
  · simp [WDRep.transport, hN]
  · have h1 : μ (ineIncl h s) = fun i => ι (χ i s : Qbar l) := funext fun i => by
      have h2 := hI i (inc (ineIncl h s)) s.2
      have h3 : ψ i (inc (ineIncl h s)) = χ i s := by
        have h6 : κ i (inc (ineIncl h s)) = cycBar F Ω l s ^ m i * χ i s := h2
        have h7 : ε (inc (ineIncl h s)) = cycBar F Ω l s := rfl
        simp only [ψ, MonoidHom.mul_apply, MonoidHom.zpow_apply]
        rw [h6, h7, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      simp [μ, h3]
    have h4 := (hb s).trans (congrArg Matrix.diagonal h1)
    have h5 : LinearMap.toMatrix b b ((wdRep (Loc.PP l) ι Bw h hj ρ).ρ (ineIncl h s)) =
        Matrix.diagonal fun i => ι (χ i s : Qbar l) :=
      (congrArg (LinearMap.toMatrix b b) (wdRep_ineIncl (Loc.PP l) ι Bw h hj ρ s)).trans h4
    exact transport_rho (wdRep (Loc.PP l) ι Bw h hj ρ) b (ineIncl h s) _ h5
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAway
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ
theorem UpperTheory.V.Af.weil_deligne_away_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWeylC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh
theorem UpperTheory.V.Af.weyl_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WeylC := by
  intro _ E _ _ _ n
  refine ⟨((n + 1) ^ 2) ^ (n * n * Fintype.card (E →+* ℂ)), n * n * Fintype.card (E →+* ℂ), fun m hm H hH => ?_⟩
  have hb := fun i => abs_le.1 (hH i)
  let ν : Fin n → ℕ := fun k => ((k : ℕ) + 1 + H - m k.rev : ℤ).toNat
  have hν : ∀ k, (ν k : ℤ) = (k : ℕ) + 1 + H - m k.rev := fun k => Int.toNat_of_nonneg (by have := hb k.rev; omega)
  have hanti : Antitone ν := by
    cases n with
    | zero => exact fun i => i.elim0
    | succ n =>
      refine Fin.antitone_iff_succ_le.2 fun i => ?_
      have h1 := hν i.succ
      have h2 := hν i.castSucc
      have h3 : m i.castSucc.rev < m i.succ.rev := hm (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
  have hle : ∀ k, ν k ≤ n + 2 * H := fun k => by
    have h1 := hν k
    have h2 := hb k.rev
    have h3 := k.2
    omega
  obtain ⟨P, hP, hd, hw⟩ := UpperTheory.V.Weyl.existsScalar n ν hanti _ hle
  obtain ⟨Ξ, h1, h2⟩ := UpperTheory.V.WeylC.exists_tens (E := E) P hP _ hw (n + H)
  refine ⟨Ξ, fun τ => (UpperTheory.V.WeylC.algInfChar_iff _ _ _).2 ⟨by simp [UpperTheory.V.Af.infOf], fun u => ?_⟩, ?_⟩
  · rw [h2, UpperTheory.V.Af.infOf, Multiset.map_map, Multiset.map_map]
    congr 1
    refine (Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_)
    have h3 : ((ν k : ℕ) : ℂ) = (k : ℕ) + 1 + H - m k.rev := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (hν k)
    simp only [Function.comp_apply, Fin.revPerm_apply, h3]
    push_cast
    ring
  · refine h1.trans ((Nat.pow_le_pow_left hd _).trans ?_)
    rw [← pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * n * H), Nat.zero_le H, Nat.zero_le n]) _
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSuppProd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TNZ.Grp
theorem step_suppProd_alt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.Step_suppProd_alt :=
  _root_.UpperTheory.TNZ.Grp.step_spTop_alt G UpperTheory.TNZ.step_spLat (step_spUniq G) (_root_.UpperTheory.TNZ.Grp.step_spCount_alt G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) _root_.UpperTheory.TNZ.Grp.step_spOrd_alt (_root_.UpperTheory.TNZ.Grp.step_spPiSub_alt G) (_root_.UpperTheory.TNZ.Grp.step_spSupp_alt G) _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt
    UpperTheory.TNZ.step_tensorVec
end UpperTheory.TNZ.Grp
end
end

