module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull

namespace UpperTheory.V.Af

private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)

private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩

end UpperTheory.V.Af

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem frob_of_galRep (P : Hypotheses₂) {χ : HChar (maximalRealSubfield K)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι R wt HT) (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ)
    (hB : (CG.mk π).HasSat w B) : FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R H.cont w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H.away w hw A h rc hrc σ hσ

private theorem exists_sign (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) :
    ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have h2 : χ.locInf v (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun u => (h u v).trans (Units.ext (by simpa using e))⟩
  · exact ⟨1, fun u => (h u v).trans (Units.ext (by simpa using e))⟩

end UpperTheory.V.Af

open UpperTheory.V.Af in
theorem UpperTheory.V.Af.galoisExistence_from_published :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.ExC := by
  intro P K Ω _ _ _ _ _ _ l _ ι n hn π χ hreg hsign hd
  obtain ⟨m, hm⟩ := exists_sign χ hsign
  have hN : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (χ * quadChar K ^ (m + n)) :=
    ⟨fun v => by
      change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
      rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
      simp, hN ▸ hd⟩
  obtain ⟨R, wt, HT, H⟩ := P.litN.aut.gal K Ω l ι n hn π _ hreg hpol
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B :=
    ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
      let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
      ⟨σ, hi σ hσ⟩
  refine ⟨_, R, wt, HT, hN, H, ⟨H.ss, (hsat.and (eventually_not_mem K l)).mono ?_⟩, fun r hr ha => ?_⟩
  · rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, frob_of_galRep P H w hw B hB⟩
  · refine ExLib.isGalRepOf_of_iso H ha.1
      (isoOfFrob P K Ω l ι n R r H.cont hr H.ss ha.1 ((ha.2.and (eventually_not_mem K l)).mono ?_))
    rintro w ⟨⟨B, h1, h2⟩, hw⟩
    exact ⟨_, frob_of_galRep P H w hw B h1, h2⟩

theorem UpperTheory.V.Af.exC :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.ExC := fun PH => UpperTheory.V.Af.galoisExistence_from_published PH.toClassicalTheorems

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp

theorem UpperTheory.V.Af.intK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, hdual, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hdual⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem galRepOfR_iso (P : Hypotheses₂) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {π : TR.CuspSub F n}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRepOfR π ι r wt HT)
    (hs : IsSSRep r') (hi : RepIso r r') : IsGalRepOfR π ι r' wt HT := by
  obtain ⟨p, hp⟩ := id hi
  refine ⟨continuous_of_iso H.cont hi, hs, fun w hw A h rc hrc σ hσ => ?_, fun w hw A h => ?_, H.weights, H.weights_sym,
    fun Q AI hT w A h O _ _ _ Bw hj => ?_⟩
  · exact (H.away w hw A h rc hrc σ hσ).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right]
  · obtain ⟨x, h1, h2⟩ := H.pure w hw A h
    exact ⟨x, h1.of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := H.above Q AI hT w A h O Bw hj
    have hc : ∀ g : ↥(Dec (F := F) A), r'.comp (Dec (F := F) A).subtype g =
        p * r.comp (Dec (F := F) A).subtype g * p⁻¹ := fun g => hp g
    obtain ⟨k1, k2, -, k4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l Q F Ω O _ Bw n _ _ p hc
    refine ⟨k1 h1, fun τ LL' τ' hτ => k4 τ _ (h2 τ LL' τ' hτ), fun σ hσ hI => ⟨isSstAt_conj Q Bw p hc (h3 σ hσ hI).1,
      fun rc hrc => ?_⟩, fun σ hσ hS => k2 (h4 σ hσ hS)⟩
    obtain ⟨T⟩ := hT
    exact (GlobalTheory.PstConj.main F Ω l ι n Q AI ⟨T⟩ w A h O Bw hj _ _ p hc
      (P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val)) h1)).2.trans
      ((h3 σ hσ hI).2 rc hrc)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.realExistence_from_published :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.ExR := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := P.galR F Ω l ι n hn π χ hreg hpol
  have key : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι r w (algSat n (normV w) B) := fun w hw B hB => by
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
    exact satFrob P F Ω l ι n r H.cont w hw σ B (((satLoc P F n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc σ hσ
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRepOfR_iso P H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (satLoc P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine isoOfFrob P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩

theorem UpperTheory.V.Af.exR :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.ExR := fun PH => UpperTheory.V.Af.realExistence_from_published PH.toClassicalTheorems

end
end

