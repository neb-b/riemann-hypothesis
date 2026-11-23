module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSameOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.DefiniteBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem satLink_of (P : _root_.UpperTheory.V.Af.Hypotheses') : SatLink := by
  intro E _ _ _ a π
  refine ⟨fun w σ hσ B => (_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ π.finPart ((_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w
    ⟨σ, hi σ hσ⟩
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
private theorem algSat_inj {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) {B B' : Multiset ℂˣ}
    (h : ((algSat n (normV w) B).map fun b => X - C b).prod = ((algSat n (normV w) B').map fun b => X - C b).prod) :
    B = B' := by
  have h3 := congrArg Polynomial.roots h
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have h4 := Multiset.map_injective
    (mul_right_injective₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq (((n : ℝ) - 1) / 2)).ne')) (a₁ := B.map Units.val)
    (a₂ := B'.map Units.val) (by simpa [algSat, Multiset.map_map] using h3)
  exact Multiset.map_injective Units.val_injective h4
private theorem eq_of_split {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} [IsCMField L]
    (hE : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal)
    (r : G L Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (f : G L Ω → (Qbar l)[X])
    (hf : ∀ j, Continuous fun g => (f g).coeff j)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, IsSplitAt w → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ σ : G L Ω, IsFrob A (normV w) σ → (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f σ) (g : G L Ω) :
    (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f g := by
  have contCoeff : ∀ i : ℕ, Continuous fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i := fun i => by
    have h : (fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i) =
        fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ (Qbar l) (Fin n)).coeff i) := by
      funext M
      exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id _) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  ext i
  have h1 : Continuous fun g : G L Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (contCoeff i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
  refine congrFun (Continuous.ext_on hD h1 (hf i) ?_) g
  rintro σ ⟨v, hv, hd, A, hA, hσ⟩
  have h := not_not.1 hv (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hE v) hd) A hA σ hσ
  simp only [h]
private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]
private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
theorem UpperTheory.V.Z.Desc.W.same_of_statement :
    _root_.UpperTheory.V.Z.Desc.W.SameOfAlt := by
  intro Pr hBc hTw hSum hSp hOne E Ω _ _ _ _ _ _ hE l _ ι n hn π r hc hatt U hU hsat
  have hLink := satLink_of Pr
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hBc E hE n hn U hU
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E n hn U hU τ
    exact (UpperTheory.speh_parameter_strings n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  obtain ⟨f, hfc, hf⟩ := hSum E Ω l ι n c a d P m (fun i => (hP.pos i).1) hP.csd hP.inf hint
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hall := eq_of_split hE r hc f hfc (by
    filter_upwards [hsat, hatt.2, hev] with w h1 ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩ hs A hA s hs'
    obtain ⟨τ, b', h2, h3, h4⟩ := h1 hs
    obtain rfl := hb.unique h4
    obtain rfl := hSp Pr.litN E n c a d hsum w (ρ · w) (σ · w) hP.pos (fun i => (hS i w).2.2) S
      (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)) τ
      (UpperTheory.building_component_uniqueness E n U hU w hs _ _ _ _ h2 (hsplit w hs)) b h3
    exact Polynomial.map_injective ι.toRingHom ι.injective (((hF A hA).2 s hs').trans (hf w hw S hS' A hA s hs').symm))
  have hπ : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧ (CG.mk π).HasSat w (satTot w d S) := by
    filter_upwards [hatt.2, hev] with w ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨s, hs⟩ := exists_isFrob hA
    have h1 := (hF A hA).2 s hs
    rw [hall s, hf w hw S hS' A hA s hs] at h1
    exact ⟨S, hS', algSat_inj w n h1 ▸ hb⟩
  obtain ⟨rfl, hd⟩ := hOne Pr.litN.aut.js.1 hTw E n c hn a d P π hP.pos hπ
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hsum
  obtain rfl : a = fun _ => n := funext fun i => by rw [Subsingleton.elim i 0, hn']
  obtain rfl : π = P 0 := CuspSub.ext (strongMultOneC E n π (P 0) (by
    filter_upwards [hπ] with w ⟨S, h1, h2⟩
    exact ⟨S 0, satTot_one w S ▸ h2, h1 0⟩))
  refine ⟨fun w hw τ hτ => ?_, fun φ => ?_⟩
  · refine Z.Desc.irrComp E n U hsum (P 0) w (ρ 0 w) (σ 0 w) (hP.loc 0 w) (hS 0 w).2.2 ?_ τ hτ
    have e : (σ · w) = fun _ => σ 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have key : ∀ s s' : Fin 1 → SmIrr (GL (Fin (1 * n)) (w.adicCompletion E)), s = s' →
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hsum w s) →
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hsum w s') := by
      rintro s _ rfl h
      exact h
    exact key _ _ e (hsplit w hw)
  · obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E n hn U hU φ
    have e := hP.weight φ lam hl
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact ⟨lam, hl, e ▸ hP.inf 0 φ⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfDualC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix
private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm
private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))
private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm
private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))
private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)
private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    {c : G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
theorem UpperTheory.V.Af.self_dual_complex_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SelfDualC := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ χ μ hμ c P hc hP
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk F n hn π _ ?_
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have h2 := (conjSrc_injective (IsCMField.complexConj F).toRingEquiv).tendsto_cofinite.eventually hπ.2
  filter_upwards [Bc.normGal F Ω l ι χ μ hμ, hπ.2, h2, hl] with w ⟨hu, he⟩ ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩ hw
  exact ⟨hu, B, B', hB, hB', frob_dual hc hP hw hF hF' he⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfDualR
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host Neutral.B1
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open scoped Matrix
private theorem roots_stable {k : Type} [Field k] {n : ℕ} (f : k →+* ℂ) (M P : GL (Fin n) k) (t : kˣ)
    (h : (M : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) =
      (t : k) • (P : Matrix (Fin n) (Fin n) k)) (B : Multiset ℂ)
    (hB : (M : Matrix (Fin n) (Fin n) k).charpoly.map f = (B.map fun b => X - C b).prod) :
    B.map (fun b => f t * b⁻¹) = B := by
  set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ
  have hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0 := fun U => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero
  have h' : Nᵀ * Q * N = f t • Q := by
    have := congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [hQ]
  rw [← Matrix.charpoly_map, ← hN] at hB
  have hc : B.card = n := by
    have := congrArg natDegree hB
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod := fun x => by
    have := congrArg (eval x) hB
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.smul_one_eq_diagonal] using this
  have e0 : N.det = B.prod := by
    have := ev 0
    simp only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this
    rw [Multiset.prod_map_neg, hc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by simp)) this
  have hb : ∀ b ∈ B, b ≠ 0 := fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))
  have key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod := by
    intro x hx
    have e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) =
        (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q) := by
      rw [mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]
      abel
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      ev, ev, e0, Fintype.card_fin] at e2
    have e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod =
        (-x) ^ n * (B.map fun b => f t / x - b).prod := by
      rw [← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]
      refine congrArg _ (Multiset.map_congr rfl fun b h => ?_)
      have := hb b h
      simp only [Function.comp_apply]
      field_simp
      ring
    refine mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_
    rw [← hQ]
    linear_combination Q.det * e3 - e2
  have hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)
    have := key x hx
    simpa [eval_multiset_prod, Multiset.map_map] using this
  have := congrArg roots hp
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this
private theorem sat_stable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    (hr : DualTw r θ) {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {χ : HChar F} {a : (F →+* ℂ) → ℤ}
    (hχ : IsLAdicOf art ι χ a (θ * cycBar F Ω l ^ ((n : ℤ) - 1))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hu : χ.UnrAt w) {B : Multiset ℂˣ}
    (hB : FrobEig ι r w (algSat n (normV w) B)) : (B.map (·⁻¹)).map (· * χ.val w) = B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  obtain ⟨P, hP⟩ := hr
  have h1 := roots_stable ι.toRingHom _ P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 := hχ.frob_unr ha (Or.inl hw) hu hA hσ
  have h3 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hw hA hσ]
    simp
  have hq : (0 : ℝ) < normV w := by
    have : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h : 0 < normV w := by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using (zero_lt_one.trans this)
    exact_mod_cast h
  set c : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hq, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]
    simp
  have h4 : ι ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c * c * (χ.val w : ℂˣ) := by
    have h5 := congrArg ι h2
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, h3, map_mul, map_zpow₀,
      map_natCast, map_inv₀, ι.apply_symm_apply, ← hcc] at h5
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, h5, inv_mul_cancel₀ (Units.ne_zero _)]
  refine Multiset.map_injective (f := fun α : ℂˣ => c * (α : ℂ))
    (fun x y e => Units.ext (mul_left_cancel₀ hc0 e)) ?_
  have h6 : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    change Multiset.map _ (B.bind fun a : ℂˣ => ({(a : ℂ)} : Multiset ℂ)) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [h6] at h1
  refine Eq.trans ?_ h1
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  change c * _ = ι _ * (c * _)⁻¹
  rw [h4]
  simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
theorem UpperTheory.V.Af.self_dual_real_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SelfDualR := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ θ χ hr hχ
  have hd : π.IsSelfDualBy χ := by
    obtain ⟨-, art, a, ha, -, h2⟩ := hχ
    refine _root_.UpperTheory.satake_polarization_real_of_printed_results H.toClassicalTheorems F n hn π χ ?_
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    have hu : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, χ.UnrAt v := by
      exact Filter.eventually_cofinite.mpr (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1
    filter_upwards [hπ.2, hl, hu] with w ⟨S, hS, hE⟩ hw hu
    refine ⟨hu, S, hS, ?_⟩
    conv_rhs => rw [← sat_stable hr ha h2 hw hu hE]
    simp [Multiset.map_map]
  refine ⟨hd, fun hs => ⟨UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel F Ω l ι χ _ hχ fun c c' hc hc' => ?_, hd⟩⟩
  simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, hs c c' hc hc', UpperTheory.cyclotomic_char_conj_invariant F Ω l c hc,
    UpperTheory.cyclotomic_char_conj_invariant F Ω l c' hc']
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfTwGal
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
private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]
theorem UpperTheory.V.Sd.self_twist_galois_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.SelfTwGal := by
  intro P F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := P.litN.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (tendsto_under' (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normV_under (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s
end
end

