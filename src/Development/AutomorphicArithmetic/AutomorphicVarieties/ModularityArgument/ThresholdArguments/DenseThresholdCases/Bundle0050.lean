module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRCharEq
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [local instance] UpperTheory.V.QbarInst.charZero UpperTheory.V.QbarInst.torsionFree UpperTheory.V.QbarInst.algClosure
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
noncomputable section
namespace UpperTheory.V.Br.CharacterEquality
private theorem normV_inj : Function.Injective fun w : Pl ℚ => normV w := fun v w h =>
  HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])
private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : Pl ℚ, normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : Pl ℚ := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp
private theorem tr_det {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.trace = a ∧ ι A.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (AddMonoidAlgebra.coeff · 0) h
  have h1 := congrArg (AddMonoidAlgebra.coeff · 1) h
  simp at h0 h1
  exact ⟨h1, h0⟩
private theorem two_det {K : Type} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    2 * A.det = A.trace ^ 2 - (A * A).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring
private theorem exists_rep (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar 2 ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 2 ≤ k) {χ : DirichletCharacter ℂ N}
    (g : Eigenform k N χ) : ∃ r : G ℚ (AlgebraicClosure ℚ) →* GL (Fin 2) (Qbar 2), Continuous r ∧
      ∀ᶠ w : Pl ℚ in Filter.cofinite, ∀ A : ValuationSubring (AlgebraicClosure ℚ), IsPlaceOver A w →
        ∀ σ : G ℚ (AlgebraicClosure ℚ), IsFrob A (normV w) σ →
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace = g.a (normV w) ∧
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det = χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) := by
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N hk χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, -, -, hsat⟩ := _root_.UpperTheory.V.Sd.holRep_alt P ℚ k hk _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems ℚ (AlgebraicClosure ℚ) 2 ι 2 one_le_two π χ' hreg hpol
  refine ⟨r, hG.cont, ?_⟩
  filter_upwards [hatt.2, normV_inj.tendsto_cofinite.eventually (Set.finite_le_nat N).eventually_cofinite_notMem]
    with w ⟨B₁, hB₁, hF⟩ hw A hA σ hσ
  have hq : ¬ normV w ∣ N := fun h => hw (Nat.le_of_dvd (NeZero.pos N) h)
  obtain ⟨B₂, hB₂, e⟩ := hsat w (Nat.factorization_eq_zero_of_not_dvd hq)
  obtain rfl := hB₁.unique hB₂
  rw [← (hval w hq).2]
  exact tr_det ι (((hF A hA).2 σ hσ).trans e)
end UpperTheory.V.Br.CharacterEquality
open UpperTheory.V.Br.CharacterEquality in
theorem UpperTheory.V.Br.charEq_sv_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Br.CharEq := by
  intro P k N M _ _ hk χ ψ g h he
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨r, hr, hF⟩ := exists_rep P ι hk g
  obtain ⟨r', hr', hF'⟩ := exists_rep P ι hk h
  have htr : (fun s => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace) =
      fun s => (r' s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hF.and hF').and (normV_inj.tendsto_cofinite.eventually he)))
      (Units.continuous_val.comp (hr.comp continuous_inv)).matrix_trace
      (Units.continuous_val.comp (hr'.comp continuous_inv)).matrix_trace ?_
    intro v hv _ B hB σ hσ
    obtain ⟨⟨h1, h2⟩, h3⟩ := not_not.1 hv
    exact ι.injective (by rw [(h1 B hB σ hσ).1, (h2 B hB σ hσ).1, h3 (places v).1])
  refine Filter.eventually_cofinite.2
    (((Filter.eventually_cofinite.1 (hF.and hF')).image fun w => normV w).subset fun p hp => ?_)
  obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
  obtain ⟨w, rfl⟩ := normV_surj hp
  refine ⟨w, fun ⟨h1, h2⟩ => hne ?_, rfl⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure ℚ) w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have e1 := (h1 A hA σ hσ).2
  have e2 := (h2 A hA σ hσ).2
  have t1 := congrFun htr σ
  have t2 := congrFun htr (σ * σ)
  simp only [mul_inv_rev, map_mul, Units.val_mul] at t1 t2
  have hd : (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det = (r' σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det :=
    mul_left_cancel₀ two_ne_zero (by rw [two_det, two_det, t1, t2])
  rw [hd, e2] at e1
  exact (mul_right_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)) e1).symm
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVREGOrd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
namespace UpperTheory.V.Sd.EG
section Norm
variable {l : ℕ} [hl : Fact l.Prime]
end Norm
private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]
section Gal
variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega
theorem exists_ordinary_form_trace_near_one_add_cyc (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {ψ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = ψ) :
    ∃ c π r, OrdForm ι ψ⁻¹ (1 - (k : ℤ)) c (fun _ => ![0, 1 - (k : ℤ)]) (fun _ => 1) π r ∧
      ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + (cycBar ℚ Ω l ^ (k - 1) * ψ) s)‖ < 1 := by
  classical
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N (by omega) χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩ := _root_.UpperTheory.V.Sd.holRep_alt P ℚ k (by omega) _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems ℚ Ω l ι 2 one_le_two π χ' hreg hpol
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc
  have hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N := fun w => by
    simp [hc, Nat.factorization_eq_zero_iff, normV_prime w, (normV_prime w).ne_one, NeZero.ne N]
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hG.cont.comp continuous_inv)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))
  have hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧
      (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    refine ((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter
      (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨⟨B₁, hB₁, hF⟩, hq⟩ := hw
    have hqN : ¬ normV w ∣ N := fun h => hq (h.mul_left _)
    obtain ⟨B₂, hB₂, e⟩ := hsat w ((hc0 w).2 hqN)
    obtain rfl := hB₁.unique hB₂
    obtain ⟨h2, h3⟩ := tr_det ι _ (((hF A hA).2 σ hσ).trans e)
    have hAq := (over_iff hA _).2 dvd_rfl
    have h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]
      simp [mul_comm]
    have h4 := hg _ (normV_prime w)
    rw [map_sub, map_add (f := _), map_one, ← h1, ← h2] at h4
    exact ⟨h4, by rw [Set.mem_setOf_eq, h3, h1, (hval w hqN).2]⟩
  have hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hker : ψ⁻¹.ker = ψ.ker := by ext s; simp
  refine ⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_,
    fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1⟩
  · have h1 := (hall s⁻¹).2
    rw [inv_inv] at h1
    refine (Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]
    rfl
  · rw [hker, ← hm]
    exact dirG_open _
  · refine (fin_dvd hlN).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact ((mem_iff w l).1 h).mul_right _
    · rw [Set.mem_setOf_eq, hlev w h, Ne, hc0, not_not] at hw
      exact hw.mul_left _
  · rw [hker, ← hm]
    by_cases h : normV w ∣ N
    · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)
      rw [hlev w h1, hc0]
      exact iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])
    · refine iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_
      by_cases h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact Or.inr h1
      · exact Or.inl ((hlev w h1).trans ((hc0 w).2 h))
  · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw
    obtain ⟨v, h2, h3, -⟩ := hU w
    rw [show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw] at h3
    exact ⟨v, h2, h3⟩
  · rw [hlev w hwl] at hw ⊢
    refine ⟨_, hU w, norm_eq_one_of ?_⟩
    have h4 := hg _ (normV_prime w)
    rw [Ne, hc0, not_not] at hw
    rwa [χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw),
      zero_mul, add_zero, map_sub, map_one] at h4
  · have hq := (mem_iff_eq w hl.out).1 hw
    have hqN : ¬ normV w ∣ N := hq ▸ hN
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hqN)
    rw [(hval w hqN).2] at e
    have h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1 := by
      refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
      rw [← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]
    have h3 : ‖(normV w : Qbar l)‖ < 1 := by rw [hq]; exact norm_l
    have hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖ := by
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)
    have ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1 := by
      have := small_add (hg _ (normV_prime w)) (hs.trans h3)
      rw [← map_add (f := _)] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨lam, h5, h6⟩ := stab w ι π hB e ha hs
    refine ⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩
    · simp; omega
    · simp
    · simpa using h6
end Gal
end UpperTheory.V.Sd.EG
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedOf4P
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl
private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous
private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F
private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero
end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
open UpperTheory.V.Cu.RankFourTensorSourceAtPrime in
theorem UpperTheory.V.Cu.tower_is_initial_of_ok :
    UpperTheory.V.Cu.AlNe → UpperTheory.V.Cu.WtsOf4 → UpperTheory.V.Cu.IrrOf4 → UpperTheory.V.Cu.AutOf4 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
      (d : UpperTheory.V.Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → OffW d.ι d.K' d.ρ (UpperTheory.V.Cu.tenB d.ρ₁ d.τ) →
      T.IsSeedAlt d.ι ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))) := by
  intro hne hW hI hA Ω _ _ _ l _ d T hT hok hrw
  have hi := hI Ω l d T hT hok
  obtain ⟨π, h1, h2⟩ := hA Ω l d T hT hok hi
  obtain ⟨U, j, hU, hj⟩ := d.tw.wt
  have hm := d.tau.pos
  have hk := d.big
  let φ : G ℚ Ω →* (Qbar l)ˣ := (toB d.δ)⁻¹ ^ 2 * cycBar ℚ Ω l ^ j
  have hle : U ≤ φ.ker := fun g hg => by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hg)
    rw [map_pow, map_zpow] at this
    have e : toB d.δ g ^ 2 = cycBar ℚ Ω l g ^ j := this.trans (congrArg (· ^ j) (toB_chi d.c g))
    show (toB d.δ g)⁻¹ ^ 2 * cycBar ℚ Ω l g ^ j = 1
    rw [← e, inv_pow, inv_mul_cancel]
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : Finite (G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle hU)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨hi, _, ((toB d.δ).comp (resQ T.L))⁻¹, π, -j, φ.ker.index, fun i => ?_,
    hW Ω l d T U j hU hj, ((cont_delta d).comp (cont_res T.L)).inv, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,
    ⟨(d.k : ℤ) - 1 + d.m, by simp <;> ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' h1 (autOf4W hne Ω l d T hT hok hi hrw π h1 h2), h2⟩
  · fin_cases i
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
    · exact ⟨(d.k : ℤ) - 1 - 2 * d.m, by omega, by simp <;> ring⟩
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
  · have := φ.ker.pow_index_mem (resQ T.L s)
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [neg_neg]
    exact this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAwayW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V
private theorem split_of_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {p : Polynomial K} (a b : K'ˣ)
    (h : p.map e.toRingHom = (Polynomial.X - Polynomial.C (a : K')) * (Polynomial.X - Polynomial.C (b : K'))) :
    ∃ a' b' : Kˣ, e a' = a ∧ e b' = b ∧
      p = (Polynomial.X - Polynomial.C (a' : K)) * (Polynomial.X - Polynomial.C (b' : K)) := by
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom a, Units.map e.symm.toRingHom.toMonoidHom b, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [h]
    simp
private theorem roots3 {K : Type} [Field K] {p : Polynomial K} {a b c : K}
    (h : p = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c)) :
    p.IsRoot a ∧ p.IsRoot b ∧ p.IsRoot c := by
  subst h
  simp
private theorem link_false {l : ℕ} [Fact l.Prime] {x : Matrix.GeneralLinearGroup (Fin 3) (Qbar l)} {Q : ℕ} (hn : NoLink x Q) (c : Qbar l) (h0 : c ≠ 0)
    (r0 : x.val.charpoly.IsRoot c)
    (r1 : x.val.charpoly.IsRoot 1)
    (r2 : x.val.charpoly.IsRoot c⁻¹)
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hQ : c ^ j = Q ∨ c ^ j * Q = 1) : False := by
  rcases hj with rfl | rfl <;> rcases hQ with e | e
  · exact hn _ _ r0 r1 1 le_rfl (by simpa using e)
  · exact hn _ _ r1 r0 1 le_rfl (by
      simp only [pow_one] at e ⊢
      rw [mul_comm (Q : Qbar l), e])
  · exact hn _ _ r0 r2 1 le_rfl (by
      rw [pow_one, pow_one, ← e]
      field_simp)
  · exact hn _ _ r2 r0 1 le_rfl (by
      rw [pow_one, pow_one]
      exact inv_eq_of_mul_eq_one_right (by linear_combination e))
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime]
private theorem adjoint_inertia_image_finite (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin 2) (Qbar l)}
    {y : WD h} (hx : IsWDOf ι r y) (hy : y.mono0) : (ad0 r '' (Ine (F := L) A : Set (G L Ω))).Finite := by
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  have hN0 : N = 0 := (hN.weilDeligneParam_monodromy_eq_zero_iff hl ht ι).1 (hw ▸ hy)
  subst hN0
  obtain ⟨-, U, hU, H⟩ := hN
  have hu : ∀ σ ∈ U, ad0 r (σ : G L Ω) = 1 := fun σ hσ => by
    have h1 : r (σ : G L Ω) = 1 := Units.ext (by rw [H σ hσ]; simp)
    apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]
    simp
  haveI := compactSpace_Ine (E := L) A
  let f := (ad0 r).comp (Ine (F := L) A).subtype
  haveI : Finite (Ine (F := L) A ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (H₁ := U) (fun x hx => hu x hx) hU)
  haveI : Finite f.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv
  refine (Set.toFinite (f.range : Set (GL (Fin 3) (Qbar l)))).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩
end
end UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V in
theorem UpperTheory.V.Z.Sym.W.away_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.AwayWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι r hr hU w hl τ hg hT
  obtain ⟨ψ, hψ, ⟨e⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.principal_series_of_statement_w P.litN L 2 w τ hT
  refine ⟨ψ, hψ, ⟨e⟩, ?_⟩
  intro j hj ε hε hlk
  obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN h
  have gd : Gd (rc (algNorm τ)) := Gu.plainGd L Ω A w h rc hrc 2 τ hT
  have hx : IsWDOf ι r (rc (algNorm τ)) := ((hg A h rc hrc).1 hl).isWDOf gd
  obtain ⟨a, ha, -⟩ := id hrc
  obtain ⟨s, j', hj', hs, hn⟩ := hU w hl A h (adjoint_inertia_image_finite hl hx gd.2)
  have hact : ActsAs A (normV w) s j' 0 := by
    simp only [ActsAs, pow_zero, pow_one]
    exact hs
  let S : Weil h := ⟨s, j', 0, hact⟩
  have hd : deg S = (j' : ℤ) := by simpa using deg_eq (σ := S) hact
  have hcp := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P L Ω l ι 2 r w hl A h a ha τ hg hT ψ hψ
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective) S
  rw [psPol, Fin.prod_univ_two] at hcp
  obtain ⟨a', b', ea, eb, hab⟩ := split_of_map ι _ _ hcp
  have hc := (ad0Facts l (G L Ω) r).2.2.2.2.1 s a' b' hab
  obtain ⟨r0, r1, r2⟩ := roots3 hc
  have hci : ((b' / a' : (Qbar l)ˣ) : Qbar l) = (((a' / b' : (Qbar l)ˣ) : Qbar l))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val, inv_div]
  rw [hci] at r2
  refine link_false hn _ (Units.ne_zero _) r0 r1 r2 hj ?_
  have hc' : ι ((a' / b' : (Qbar l)ˣ) : Qbar l) = ((ψ 0 (a S) / ψ 1 (a S) : ℂˣ) : ℂ) := by
    rw [Units.val_div_eq_div_val, map_div₀, ea, eb, ← Units.val_div_eq_div_val, mul_div_mul_right_eq_div]
  have hv : (ψ 0 (a S) / ψ 1 (a S)) ^ j = absPow (w.adicCompletion L) (ε : ℂ) (a S) := by
    rw [← hlk]
    rfl
  have hz : ι (((a' / b' : (Qbar l)ˣ) : Qbar l) ^ j) = ((absPow (w.adicCompletion L) (ε : ℂ) (a S) : ℂˣ) : ℂ) := by
    rw [map_pow, hc', ← Units.val_pow_eq_pow_val, hv]
  rcases hε with rfl | rfl
  · left
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (1 : ℝ) S
    rw [hd] at h1
    rw [hz, map_natCast]
    simpa using h1
  · right
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (-1 : ℝ) S
    rw [hd] at h1
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
    rw [map_mul, hz, map_natCast, map_one]
    have h2 : ((absPow (w.adicCompletion L) (((-1 : ℤ) : ℂ)) (a S) : ℂˣ) : ℂ) = (((normV w : ℕ) : ℂ)⁻¹) ^ j' := by
      simpa [Complex.cpow_neg_one] using h1
    rw [h2]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
end
end
end

