module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AlgPosOfExpo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.UpCycOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AlgPosOfExpo
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Ws UpperTheory.V.Cu UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix

private theorem algPos_of_expo (ω : HChar ℚ) (h : ∀ v, ∃ n : ℤ, TR.expo ω v = n) : ∃ a, IsAlgPos ω a := by
  obtain ⟨n, hn⟩ := h default
  refine ⟨fun _ => n, fun k hk => ?_⟩
  letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩
  have hk0 : (0 : ℝ) < ((k : ℚ) : ℝ) := hk (Rat.castHom ℝ)
  let diagR : ℚ →+* TR.Rinf ℚ := (TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ))
  have hv : ∀ v, diagR (k : ℚ) v = ((k : ℚ) : ℝ) := fun v =>
    eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp diagR) (k : ℚ)
  have e : Units.map diagR.toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ) :=
    Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)
  have hdiag : infDiag k = TR.infId ℚ (Units.map diagR.toMonoidHom k) := by
    have h : ((infDiag k : Ideles ℚ) : AdeleRing (𝓞 ℚ) ℚ) = (algebraMap ℚ (InfiniteAdeleRing ℚ) k, 1) := by
      unfold infDiag
      rw [MonoidHom.finsetProd_apply, Fintype.prod_unique, MonoidHom.comp_apply]
      refine Prod.ext (funext fun w => ?_) rfl
      have hw : w = default := Subsingleton.elim _ _
      subst w
      exact ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self ℚ default (atInf default k)
    apply Units.ext
    rw [h]
    refine Prod.ext ?_ ?_
    · change _ = 1 - TR.infEq ℚ 1 + TR.infEq ℚ ((TR.infEq ℚ).symm (algebraMap ℚ (InfiniteAdeleRing ℚ) k))
      simp
    · change (1 : Af ℚ) = 1 - 0 + 0
      simp
  have e2 := TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)
  rw [← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0] at e2
  rw [HChar.inf, MonoidHom.comp_apply, hdiag, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]
  exact e2
private theorem det_sat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = ((x * y : ℂˣ) : ℂ) * q := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C]
  simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_apply]
  rw [Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]
private theorem det_alg (P : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (ha : IsAutR ι ρ) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp ρ) := by
  obtain ⟨π, hreg, hatt⟩ := ha
  obtain ⟨ω, hω, hint⟩ := _root_.central_character_of_regular_cusp P.toClassicalTheorems π hreg (hatt.2.mono fun w ⟨B, hB, _⟩ => ⟨B, hB⟩)
  obtain ⟨a, hal⟩ := algPos_of_expo ω hint
  obtain ⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι hal
  have hch : IsCharOf ι ω μ := ⟨hμ, art, a, hart, hal, hL⟩
  obtain ⟨hcc, χ, art', a', h'⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l)
    ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩
  have H := (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).2.1
  have h1 : Af.IsAlgChar ι (cycBar ℚ Ω l) := ⟨χ, hcc, art', a', h'⟩
  have h2 := (H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    have hp : l.Prime := Fact.out
    have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
    exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have key : (fun s : G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) =
      fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l) := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and hl))
      (Units.continuous_val.comp (hc.comp continuous_inv)).matrix_det
      (Units.continuous_val.comp ((hμ.mul hcc.inv).comp continuous_inv)) ?_
    intro v hv _ A hA σ hσ
    obtain ⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩ := not_not.1 hv
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have hcyc : ι (((cycBar ℚ Ω l)⁻¹ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV v : ℂ) := by
      have hval : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob h4 hA hσ, map_natCast, map_natCast]
      rw [MonoidHom.inv_apply, map_inv, inv_inv, hval, map_natCast]
    apply ι.injective
    rw [MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, hcyc,
      ← hω v x y hB, ← det_sat _ _ _ _ e2]
    exact ι.toRingHom.map_det _
  have e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹ := MonoidHom.ext fun s => Units.ext (by
    have := congrFun key s⁻¹
    simp only [inv_inv] at this
    exact this)
  rw [e]
  exact h2
private theorem conj_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem conj_off {Ω : Type} [Field Ω] [CharZero Ω] (K' : IntermediateField ℚ Ω) (hK : IsTotallyComplex K') {c : G ℚ Ω}
    (hc : IsConjEl c) : c ∉ K'.fixingSubgroup := by
  intro h
  obtain ⟨j, hj⟩ := hc
  refine InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω))))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  exact (hj x).symm.trans (congrArg j (h x))
private theorem pair_plane {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem kap_anti {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {K' : IntermediateField ℚ Ω} [NumberField K'] {g0 : G ℚ Ω} {m : ℕ} {c₁ : Coef l} {κ : G K' Ω →* (Qbar l)ˣ}
    {τ : G ℚ Ω →* Sd.S3.M2 c₁.O} {s} (hτ : TauDat ι K' g0 m c₁ τ s κ) {c : G ℚ Ω} (hc : c ∉ K'.fixingSubgroup) {g g' : G K' Ω}
    (h : resQ K' g' = c * resQ K' g * c⁻¹) : (κ g : Qbar l) * κ g' = 1 := by
  have hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 := fun x => by
    have h := congrFun (congrFun (hτ.form x) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hg : resQ K' g ∈ K'.fixingSubgroup := fun y => g.commutes y
  have e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g) := by
    rw [h, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hg' : resQ K' g' ∈ K'.fixingSubgroup := fun y => g'.commutes y
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 0) 1
  have f1 := hf c
  have f2 := hf (resQ K' g)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2
  have key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1 := by
    generalize τ (resQ K' g) 0 0 = a at *
    generalize τ (resQ K' g) 0 1 = b at *
    generalize τ (resQ K' g') 0 0 = a' at *
    generalize τ (resQ K' g') 0 1 = b' at *
    generalize τ c 0 0 = p at *
    generalize τ c 0 1 = q at *
    linear_combination (a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1
  rw [hτ.val g, hτ.val g']
  exact_mod_cast congrArg (fun z : c₁.O => (z : Qbar l)) key
theorem UpperTheory.V.Cu.polOf4_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Cu.PolOf4 := by
  intro P Ω _ _ _ l _ ι K' _ _ hK ρ hρ ha g0 m c₁ κ τ s hτ
  obtain ⟨c, hc⟩ := conj_ex Ω
  let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J * ρ c⁻¹, det_alg P ι ρ hρ ha,
    fun a b h h' => auSign _ a b h h', hc, fun g g' h => ?_⟩
  have h' : resQ K' g' = c * resQ K' g * c⁻¹ := h
  have hk := kap_anti hτ (conj_off K' hK hc) h'
  have e : ρ c⁻¹ * ρ (resQ K' g') = ρ (resQ K' g) * ρ c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (ρ c⁻¹).val * (ρ (resQ K' g')).val = (ρ (resQ K' g)).val * (ρ c⁻¹).val := congrArg Units.val e
  have hp : (ρ (resQ K' g)).valᵀ * J.val * (ρ (resQ K' g)).val = (ρ (resQ K' g)).val.det • J.val := pair_plane _
  have hd : (((Matrix.GeneralLinearGroup.det.comp ρ).comp (resG ℚ K' Ω) g : (Qbar l)ˣ) : Qbar l) = (ρ (resQ K' g)).val.det := rfl
  rw [hd, tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul, ← Matrix.smul_mul, ← hp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk, one_smul]
  simp only [Matrix.mul_assoc, e']
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuKap
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (ι : PadicAlgCl l ≃+* ℂ), Af.IsAlgChar ι (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := by
  intro hP Ω _ _ _ l _ c D T c' h K ι
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ (auCont c' K.κ K.κ_cont) fun w hw => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
    rwa [e] at h1
  obtain ⟨a, b, k, hk, -, H⟩ := K.cyc A hl
  refine ⟨A, hA, a, k, hk, fun s hs => ?_⟩
  rw [← (auChi T.L Ω c').1]
  have h2 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom) (H s hs).1
  rw [map_pow, map_mul, map_zpow, map_one] at h2
  exact h2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Af.IsAlgChar ι (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) := by
  intro hP Ω _ _ _ l hl c D h ι
  have hc : AdicCont (maximalIdeal c.O) fun g => (D.th g : c.O) := (GradeZeroInterpolatingElement.facts D h).2.2.2.2.2.2.2.2.2.2.1 0
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP ℚ Ω l ι).1 _ (auCont c D.th hc) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  obtain ⟨m, hm, hx⟩ := h.xi_ord
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => hl.out.ne_one (by simpa [e] using hm)
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h.psi_open
  have hn : 0 < D.ψ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  refine ⟨A, hA, (D.e : ℤ) + 1, (l - 1) * m * D.ψ.ker.index, by positivity, fun s _ => ?_⟩
  have h1 : D.om s ^ (l - 1) = 1 := DFunLike.congr_fun h.om_pow s
  have h2 : D.ξ s ^ m = 1 := DFunLike.congr_fun hx s
  have h3 : D.ψ s ^ D.ψ.ker.index = 1 := by
    rw [← map_pow]
    exact D.ψ.ker.pow_index_mem s
  have e : D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1)) = (D.om s)⁻¹ * D.ξ s * D.ψ s := by
    have e0 : D.th s = chiO ℚ Ω l c.O s * (D.om s)⁻¹ * D.ξ s * (chiO ℚ Ω l c.O s ^ (D.e : ℤ) * D.ψ s) := rfl
    rw [e0, zpow_neg, mul_inv_eq_iff_eq_mul, zpow_add_one]
    ac_rfl
  have e2 : (D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1))) ^ ((l - 1) * m * D.ψ.ker.index) = 1 := by
    rw [e, mul_pow, mul_pow, inv_pow, pow_mul' (D.ψ s), h3, pow_mul (D.ξ s), pow_mul' (D.ξ s), h2, pow_mul (D.om s),
      pow_mul (D.om s), h1]
    simp
  rw [← (auChi ℚ Ω c).1]
  have := congrArg (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) e2
  rw [map_pow, map_mul, map_zpow, map_one] at this
  exact this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpCyc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
open UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Bc.upCyc_of_alt (hA : _root_.UpperTheory.V.Af.Hypotheses') (cyc : UpperTheory.V.Z.Bc.CycC) : UpperTheory.V.Sd.UpCyc := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hp n hn r hr ⟨π, hreg, hatt⟩ hirr
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have key : (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨
      ∃ P : CuspSub E n, (∀ τ m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧ WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := by
    rcases (cyc F E hp inferInstance n hn).1 _ _ (Or.inl ⟨inferInstance, π, rfl, rfl⟩)
      (fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, hreg τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
    · exact Or.inl h1
    · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
      · exact Or.inr ⟨P, hi, hw⟩
      · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
        exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))
  rcases key with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hA F Ω l ι n r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ n r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ n _).2.1 hirr, ?_⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGPolMix
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped Matrix
private theorem alg_closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) :
    IsAlgClosure k₀ Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
private theorem conj_el_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] : ∃ c : G k₀ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  let c : Ω ≃ₐ[ℚ] Ω := τ.restrictNormal Ω
  have hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x) := fun x => AlgEquiv.restrictNormal_commutes τ Ω x
  have hfix : ∀ y : k₀, c (y : Ω) = y := fun y => by
    apply (algebraMap Ω ℂ).injective
    rw [hc]
    let φ : k₀ →+* ℂ := (algebraMap Ω ℂ).comp (algebraMap k₀ Ω)
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y
  refine ⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩
private theorem pair_two {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing_two {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair_two _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.PolMix := by
  intro H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm
  obtain ⟨m, hm0, hm⟩ := hm
  haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s) := fun s =>
    DFunLike.congr_fun hd.det s
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hd.cont
  have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, k, m, hm0, fun s _ => ?_⟩
    have hx : x (resQ k₀ s) ^ m = 1 := by
      have := DFunLike.congr_fun hm (resQ k₀ s)
      simpa using this
    rw [MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]
  have hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r) := by
    intro c c' hc hc'
    have hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a) := fun ⟨j, hj⟩ => ⟨j, hj⟩
    have hcj : IsConj (resQ k₀ c) (resQ k₀ c') := UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc',
      isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]
  obtain ⟨c, hc⟩ := conj_el_ex Ω k₀
  obtain ⟨P, hP⟩ := pairing_two r c
  exact ⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaModularIdealMap
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Ws.H5 in
theorem UpperTheory.V.Ws.hida_modular_ideal_map :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (n : ℕ) (φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ' → J₀.map φ' = J := by
  intro _ Ω _ _ _ l _ c D T _ _ c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ'
  subst hJ
  have hl : ((l : ℕ) : B.B) ∈ maximalIdeal B.B := by
    haveI := (UpperTheory.V.Base.dvrFacts l c'.O).2.2.1
    have h1 : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have h2 := map_nonunit (algebraMap c'.O B.B) _ (map_nonunit (algebraMap ℤ_[l] c'.O) _ h1)
    simpa using h2
  have stab : ∀ γ : K.V.frame.G₀ →* B.Bˣ, TwCh K.V.frame γ → ∃ τ : B.B →ₐ[c'.O] B.B,
      TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ ∧ ∀ b ∈ J₀, τ b ∈ J₀ := fun γ hγ => by
    obtain ⟨τ, hτ⟩ := twMapEx B (AlgHom.id c'.O B.B) γ hγ
    exact ⟨τ, hτ, fun b hb => closedJ _ J₀ _ (twJN B J₀ hM.dense hM.twist hl γ hγ τ hτ b hb)⟩
  have key : ∀ (γ : K.V.frame.G₀ →* c'.Oˣ), TwCh K.V.frame γ → ∀ f f' : B.B →ₐ[c'.O] X.B,
      TwMap B (f : B.B →+* X.B) (f' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) γ) → J₀.map f' ≤ J₀.map f := by
    intro γ hγ f f' hf
    obtain ⟨τ, hτ, hτJ⟩ := stab _ ((twChOps _ γ hγ).2.2 B.B (algebraMap c'.O B.B) inferInstance)
    have h1 := hτ.comp (f : B.B →+* X.B)
    have h2 : W.pushCh (f : B.B →+* X.B) (W.pushCh (algebraMap c'.O B.B) γ) = W.pushCh (algebraMap c'.O X.B) γ :=
      MonoidHom.ext fun g => Units.ext (f.commutes _)
    rw [h2, RingHom.comp_id] at h1
    have h3 : f' = f.comp τ := twMapUniq B _ _ f' (f.comp τ) hf h1
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h3]
    exact Ideal.mem_map_of_mem _ (hτJ b hb)
  obtain ⟨β₀, hβ, hβ'⟩ := descend K
  have hn := (twChOps _ β₀ hβ).1 n
  have hT := phiTw K X B β₀ hβ' n φ φ' hφ hφ'
  refine le_antisymm (key _ hn φ φ' hT) (key _ (twChOps _ _ hn).2.1 φ' φ ?_)
  have hu : ∀ g, algebraMap c'.O X.B (((β₀ ^ n)⁻¹ g : c'.Oˣ) : c'.O) * algebraMap c'.O X.B (((β₀ ^ n) g : c'.Oˣ) : c'.O) = 1 :=
    fun g => by rw [← map_mul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, map_one]
  refine ⟨fun g i hi => ?_, fun v i g => ?_⟩
  · rw [hT.1 g i hi, ← mul_assoc, ← mul_pow]
    erw [hu g]
    rw [one_pow, one_mul]
  · rw [hT.2 v i g, mul_assoc, mul_comm (_ : X.B) ((W.pushCh _ (β₀ ^ n)⁻¹ _ : X.Bˣ) : X.B)]
    erw [hu]
    rw [mul_one]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWOfOne
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.ofOne0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → Third → Across → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ), IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K Ω)) → IsAutomorphicOverImagQuad ι r := by
  intro hP hT hA K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r θ hθ hd hirr haut hc K' _ _ _ inst _ tow hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨K'', _, _, _, _, _, hK'', h1, h2⟩ := hT K K' Ω hK hK' l n r hirr hirr'
  have h3 := hA K K'' Ω hK hK'' l ι n hn r θ hc hθ hd h1 haut
  rw [inf_comm] at h2
  have h4 := hA K'' K' Ω hK'' hK' l ι n hn r θ hc hθ hd h2 h3
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP K' Ω l ι n _).2.1.1 h4
end
end

