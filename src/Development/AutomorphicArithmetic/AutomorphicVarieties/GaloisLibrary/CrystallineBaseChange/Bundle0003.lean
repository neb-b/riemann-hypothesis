module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have normV_abs {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [normV_abs, normV_abs]
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

theorem UpperTheory.V.Br.bcAtt0 :
    UpperTheory.V.Br.BcAtt0 := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π P hbc
  refine ⟨fun hreg => (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun hatt hss => ⟨hss, ?_⟩⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hbc.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · filter_upwards [hbc.unr, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
    obtain ⟨B, hB, hP⟩ := h1 (w.under (𝓞 F)) rfl _ (normV_under (K := F) w)
    obtain ⟨B', hB', hF⟩ := h2
    obtain rfl := TR.CuspSub.HasSat.unique hB hB'
    refine ⟨_, hP, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
    rw [← algSat_pow, ← normV_under] at h3
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.V.Br.intP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, ⟨χ, hpol⟩, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (UpperTheory.V.Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelRes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PlaceOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open Filter Topology

private theorem lt_one_of_tendsto {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ] [Valued R Γ] {x : R}
    (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) : (Valued.v x : Γ) < 1 := by
  by_contra hx
  have hx' : 1 ≤ (Valued.v x : Γ) := not_lt.1 hx
  have ho : {y : R | (Valued.v y : Γ) < 1} ∈ 𝓝 (0 : R) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨1, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding] at hy
    simpa using hy
  obtain ⟨n, hn⟩ := (h.eventually ho).exists
  rw [map_pow] at hn
  exact absurd hn (not_lt.2 (one_le_pow₀ hx'))

theorem UpperTheory.V.Br.placeOf :
    UpperTheory.V.Br.PlaceOf := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ v w i hi hx
  have hle : v.asIdeal ≤ (w.under (𝓞 F)).asIdeal := by
    intro y hy
    have h1 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) < 1 := by
      have h3 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) =
        v.valuation F (y : F) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      rw [h3]
      exact (v.valuation_lt_one_iff_mem y).2 hy
    have h2 : Tendsto (fun n : ℕ => (algebraMap F (v.adicCompletion F) (y : F)) ^ n) atTop (𝓝 0) :=
      Valued.tendsto_zero_pow_of_v_lt_one h1
    have h4 : Tendsto (fun n : ℕ => (i (algebraMap F (v.adicCompletion F) (y : F))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      rw [map_zero] at this
      refine this.congr fun n => ?_
      simp
    have h5 := lt_one_of_tendsto (Γ := WithZero (Multiplicative ℤ)) h4
    rw [hx] at h5
    have h6 : (Valued.v (algebraMap K (w.adicCompletion K) (algebraMap F K y)) : WithZero (Multiplicative ℤ)) =
        w.valuation K (algebraMap F K y) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h6] at h5
    exact (w.valuation_lt_one_iff_mem (K := K) (algebraMap (𝓞 F) (𝓞 K) y)).1 h5
  have hv : w.under (𝓞 F) = v :=
    HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hle).symm
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  refine ⟨hv, A, fun y => ?_, hA, fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, hi, hx⟩
  rw [← hv, IsScalarTower.algebraMap_apply F K Ω]
  exact hA (algebraMap (𝓞 F) (𝓞 K) y)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RecInv
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Br.recInv :
    UpperTheory.V.Br.RecInv := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' rc rc' hrc hrc' hy
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.matrix_map P.cont)
    · exact (Units.continuous_coe_inv.matrix_map P.cont)
  have hs : Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom) := by
    intro g
    refine ⟨Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom g, ?_⟩
    ext a b
    simp
  let τ : SmIrr (GL (Fin n) (v.adicCompletion F)) :=
    { V := σ'.V
      ρ := σ'.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.toRingHom)
      smooth := fun x => (σ'.smooth x).preimage hc
      irred := GlobalTheory.WDTransport.isIrreducible_comp σ'.ρ _ hs σ'.irred }
  have h1 : rc (algNorm σ) = rc (algNorm τ) :=
    Cq.recTransport hL F K Ω A v w h h' j i P n τ σ' (LinearEquiv.refl ℂ _) (fun _ _ => rfl) rc rc' hrc hrc' _ hy
  obtain ⟨_, _, _, -, HL⟩ := hrc
  have h2 := congrArg (fun x => IrrGL.nu x (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))) (HL.bij.1 h1)
  simp only [algNorm, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h2
  refine ⟨φ.toLinearEquiv, fun g x => ?_⟩
  exact LinearMap.congr_fun (φ.isIntertwining' g) x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.selfIso :
    UpperTheory.V.Br.SelfIso := by
  intro H F _ _ _ a ha π η h2 h
  have hd : ∀ z, TR.dchi η z = 0 := fun z => by
    have e := TR.dchi_mul η η z
    rw [← pow_two, h2, TR.dchi_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  obtain ⟨S, hS⟩ : π.Iso (π.twist η) := H F a ha _ _ (by
    filter_upwards [h] with w ⟨hu, B, hB, hE⟩
    exact ⟨B, hB, hE ▸ hB.twist hu⟩)
  have key : ∀ o φ, (S.trans (π.toTwist η).symm) (π.op o φ) =
      ((TR.opMul η o : ℂˣ) : ℂ) • π.op o ((S.trans (π.toTwist η).symm) φ) +
        TR.opAdd η o • (S.trans (π.toTwist η).symm) φ := fun o φ => by
    apply (π.toTwist η).injective
    rw [← TR.CuspSub.op_toTwist]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hS]
  refine ⟨S.trans (π.toTwist η).symm, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  all_goals rw [key]; simp [TR.opMul, TR.opAdd, hd]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WdAway
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Br.wdAway :
    UpperTheory.V.Br.WdAway := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι A v w h h' i hP hl hl' n r x y hx hy
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv F Ω A v h K Ω A w h' _ _ i hP
  have hd1 : ∀ σ, deg (c.symm σ) = deg σ := fun σ => by
    rw [← hdegc, MulEquiv.apply_symm_apply]
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have key : ∀ σ : Weil h', ((c.symm σ : Weil h) : G F Ω) = Bc.res F Ω K (σ : G K Ω) := fun σ =>
    AlgEquiv.ext fun z => (hc (c.symm σ) σ).mpr (c.apply_symm_apply σ) z
  have hres : Continuous (Bc.res F Ω K : G K Ω →* G F Ω) := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro U' hU'
    obtain ⟨U, hU, hU1, H⟩ := GlobalTheory.WeilTransport.conj_nhds K Ω F Ω (RingEquiv.refl Ω) U' hU'
    exact Filter.mem_map.mpr (Filter.mem_of_superset (hU.mem_nhds hU1) fun σ hσ => H σ hσ _ fun z => rfl)
  have hmem : ∀ σ : Ine (F := K) A, Bc.res F Ω K (σ : G K Ω) ∈ Ine (F := F) A := fun σ => by
    have h1 : ((c.symm (ineIncl h' σ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, hd1, deg_ineIncl]
    rwa [key] at h1
  let d : Ine (F := K) A →* Ine (F := F) A :=
    ((Bc.res F Ω K).comp (Ine (F := K) A).subtype).codRestrict _ hmem
  have hdc : Continuous d := (hres.comp continuous_subtype_val).subtype_mk _
  have hds : Function.Surjective d := fun τ => by
    have h1 : ((c (ineIncl h τ) : Weil h') : G K Ω) ∈ Ine (F := K) A := by
      rw [← deg_eq_zero_iff, hdegc, deg_ineIncl]
    refine ⟨⟨_, h1⟩, Subtype.ext ?_⟩
    have h2 := key (c (ineIncl h τ))
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx
  have hφ' : deg (c φ) = 1 := by rw [hdegc, hφ]
  have hine : ∀ g : Weil h', d (inePart hφ' g) = inePart hφ (c.symm g) := fun g => by
    refine Subtype.ext ?_
    have h2 := key (((c φ) ^ deg g)⁻¹ * g)
    rw [map_mul, map_inv, map_zpow, MulEquiv.symm_apply_apply, ← hd1] at h2
    refine Eq.trans ?_ h2.symm
    rw [hd1]; rfl
  have hmat : ∀ g : Weil h', wdMat (t.comp d) hφ' (r.comp (Bc.res F Ω K)) N g =
      wdMat t hφ r N (c.symm g) := fun g => by
    rw [wdMat, wdMat, key, ← hine]; rfl
  let b := GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 a
  have hb : IsWDOf ι (r.comp (Bc.res F Ω K)) (WD.mk b) := by
    refine ⟨t.comp d, ⟨ht.1.comp hdc, ht.2.comp hds⟩, c φ, hφ', N, b, ?_, ?_, rfl⟩
    · obtain ⟨h1, U, hU, H⟩ := hN
      exact ⟨h1, U.comap d, hU.preimage hdc, fun σ hσ => H (d σ) hσ⟩
    · refine ⟨ha.1, fun σ => ?_⟩
      simp only [hmat]
      exact ha.2 (c.symm σ)
  rw [hy.unique hl' hb]
  refine ⟨n, a, b, rfl, rfl, rfl, fun σ σ' hσ => ?_⟩
  rw [← (hc σ σ').mp hσ]
  exact congrArg a.ρ (c.symm_apply_apply σ).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WeakEx
section
open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
end

