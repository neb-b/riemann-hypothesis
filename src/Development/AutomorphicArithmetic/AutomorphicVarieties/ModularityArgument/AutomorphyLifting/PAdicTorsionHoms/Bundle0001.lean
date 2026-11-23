module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SatNumInj
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

private theorem satNum_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  have e : (do let a ← B; pure (a : ℂ)) = B.map fun a : ℂˣ => (a : ℂ) := Multiset.bind_singleton _ _
  unfold algSat
  erw [e]
  rw [Multiset.map_map]
  rfl

private theorem satNum_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have hq : ((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [← Real.rpow_natCast (q : ℝ) f, ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm,
      Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  rw [satNum_eq, satNum_eq, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, mul_pow, Nat.cast_pow, hq, Complex.ofReal_pow]

private theorem satNum_inj (n q : ℕ) (hq : q ≠ 0) {B B' : Multiset ℂˣ} (h : algSat n q B = algSat n q B') : B = B' := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'
  rw [satNum_eq, satNum_eq] at h
  exact Multiset.map_injective (fun a b e => Units.ext (mul_left_cancel₀ hc e)) h

private theorem frobEig_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e

theorem UpperTheory.V.Z.Win.attBC :
    AttBC := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π P hπ hP
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) (L := L) (A := Ω)⟩
  obtain ⟨-, hπ⟩ := hπ
  obtain ⟨-, hP⟩ := hP
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually hπ, hP] with w hw hw' f hf
  obtain ⟨B, hB, hF⟩ := hw
  obtain ⟨B', hB', hF'⟩ := hw'
  have h1 : FrobEig ι (r.comp (resG K L Ω)) w (algSat n (normV w) (B.map (· ^ f))) := by
    rw [hf, satNum_pow]
    exact (UpperTheory.frobenius_power_compatibility K L Ω l ι w f hf).1 n r _ hF
  have hq : normV w ≠ 0 := by
    rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  have e := satNum_inj n _ hq (frobEig_eq hF' h1)
  exact ⟨B, hB, e ▸ hB'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.ThruTr
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.V.Z.Win

private theorem norm_through {A B B' C : Type} [Field A] [Field B] [Field B'] [Field C] [Algebra A B] [Algebra A B'] [Algebra A C]
    [Algebra B C] [Algebra B' C] [IsScalarTower A B C] [IsScalarTower A B' C] [FiniteDimensional A B] [FiniteDimensional B C]
    [FiniteDimensional A B'] [FiniteDimensional B' C] (hb : Function.Bijective (algebraMap A B')) (x : C) :
    algebraMap A B' (Algebra.norm A (Algebra.norm B x)) = Algebra.norm B' x := by
  obtain ⟨a, ha⟩ := hb.2 (Algebra.norm B' x)
  have h1 : Module.finrank A B' = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId A B') hb).toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [Algebra.norm_norm, ← Algebra.norm_norm (S := B') (R := A), ← ha, Algebra.norm_algebraMap, h1, pow_one]

private theorem tower {F E M : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field M] [NumberField M]
    [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower (v.adicCompletion F) (w.adicCompletion E) (u.adicCompletion M) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change completionMap v u x = completionMap w u (completionMap v w x)
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on x
    (isClosed_eq (continuous_completionMap v u) ((continuous_completionMap w u).comp (continuous_completionMap v w))) fun k => ?_
  rw [completionMap_algebraMap, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (w.adicCompletion E),
    completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (u.adicCompletion M),
    IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]

private theorem exists_char {F E E' M : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field E'] [NumberField E']
    [Field M] [NumberField M] [Algebra F E] [Algebra F E'] [Algebra F M] [Algebra E M] [Algebra E' M]
    [IsScalarTower F E M] [IsScalarTower F E' M] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (w' : HeightOneSpectrum (𝓞 E')) (hw'v : w'.asIdeal.LiesOver v.asIdeal) (U : HeightOneSpectrum (𝓞 M)) (hU : U.asIdeal.LiesOver w.asIdeal) (hU' : U.asIdeal.LiesOver w'.asIdeal)
    (i : v.adicCompletion F ≃+* w'.adicCompletion E') (hi : IsCompl i)
    (χ' : (w'.adicCompletion E')ˣ →* ℂˣ) (hχ' : IsSmoothChar χ') :
    ∃ χ : (w.adicCompletion E)ˣ →* ℂˣ, IsSmoothChar χ ∧
      χ.comp (nm (⟨U, hU⟩ : PlacesOver M w)) = χ'.comp (nm (⟨U, hU'⟩ : PlacesOver M w')) := by
  haveI hUv : U.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans U.asIdeal w'.asIdeal v.asIdeal
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot U.asIdeal w.asIdeal v.asIdeal
  haveI := tower v w U
  haveI := tower v w' U
  haveI f1 : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := GroundTheory.Global.finite_adicCompletion v w
  haveI f2 : FiniteDimensional (w.adicCompletion E) (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w U
  haveI f3 : FiniteDimensional (v.adicCompletion F) (w'.adicCompletion E') := GroundTheory.Global.finite_adicCompletion v w'
  haveI f4 : FiniteDimensional (w'.adicCompletion E') (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w' U
  have hmap : ∀ a, algebraMap (v.adicCompletion F) (w'.adicCompletion E') a = i a := by
    intro a
    change completionMap v w' a = i a
    refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on a
      (isClosed_eq (continuous_completionMap v w') hi.1) fun k => ?_
    rw [completionMap_algebraMap, hi.2, IsScalarTower.algebraMap_apply F E' (w'.adicCompletion E')]
  have hb : Function.Bijective (algebraMap (v.adicCompletion F) (w'.adicCompletion E')) := by
    have : (algebraMap (v.adicCompletion F) (w'.adicCompletion E') : _ → _) = i := funext hmap
    rw [this]
    exact i.bijective
  let j : (v.adicCompletion F)ˣ →* (w'.adicCompletion E')ˣ :=
    Units.map ((i : v.adicCompletion F →+* w'.adicCompletion E') : v.adicCompletion F →* w'.adicCompletion E')
  have hj : Continuous j := Continuous.units_map _ hi.1
  have hc : Continuous (algebraMap (v.adicCompletion F) (w.adicCompletion E)) := continuous_completionMap v w
  refine ⟨(χ'.comp j).comp (nm (⟨w, hwv⟩ : PlacesOver E v)), GlobalTheory.LBC.Inh.isSmoothChar_comp_norm hc (hχ'.comp j hj), ?_⟩
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply]
  refine congrArg χ' (Units.ext ?_)
  change i (Algebra.norm (v.adicCompletion F) (Algebra.norm (w.adicCompletion E) (x : U.adicCompletion M))) =
    Algebra.norm (w'.adicCompletion E') (x : U.adicCompletion M)
  rw [← hmap]
  exact norm_through hb _

end UpperTheory.V.Z.Win

theorem UpperTheory.V.Z.Win.thruTr :
    ThruTr := by
  intro F E E' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n Q w w' u u' huu i hi hT
  obtain ⟨U, hU⟩ := u
  obtain ⟨U', hU'⟩ := u'
  obtain rfl : U = U' := huu
  intro s hs ζ hζ hm
  obtain ⟨χ', hχ', hun⟩ := hT s hs ζ hζ hm
  obtain ⟨χ, hχ, e⟩ := exists_char _ w w' inferInstance U hU hU' i hi χ' hχ'
  exact ⟨χ, hχ, by rw [e]; exact hun⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

theorem UpperTheory.V.Z.Win.winPt :
    Z.Gam.SuppFacts → ImaginaryQuadraticEtaCharacter.WinOf → WinPt := by
  intro _ hW K _ _ _ n hn π
  obtain ⟨t, ht⟩ := hW K n hn π
  refine ⟨t, fun v h => ?_⟩
  have e := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).1 h
  exact ht v e.1 e.2
end

