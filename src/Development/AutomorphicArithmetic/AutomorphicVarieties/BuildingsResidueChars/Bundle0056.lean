module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0050
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053
public import Mathlib.NumberTheory.PrimesCongruentOne
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.IntegralDomain

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_restriction_of_local_component_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : Plc E) (j : GLw n w →* UA E n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) → (∀ x ∈ locU n w, x = j (cLoc w x)) → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → IsoSum ((RU E n).comp j) σ τ := by
  intro E _ _ _ n π hπ w j hj1 hj2 hj3 τ hc
  obtain ⟨hirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j) :=
    ⟨f.codRestrict _ hfm, fun g => LinearMap.ext fun v => Subtype.ext (by
      have h := hf ⟨j g, hj1 g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hj2] at h
      exact h)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (GLw n w) Ψ.V τ.V τ.V Ψ.rep j τ.ρ τ.ρ
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨cLoc w (r g).1, fun y => by
      rw [← hj3 _ (r g).2]
      exact hr g ⟨j y, hj1 y⟩⟩) F hF0).1
  intro φ hφ
  have hmem : φ ∈ (⨆ i : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j),
      LinearMap.range i.toLinearMap).map π.subtype := by
    rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
  rw [Submodule.map_iSup] at hmem
  refine SetLike.le_def.1 (iSup_le fun i => ?_) hmem
  refine le_iSup_of_le ⟨π.subtype ∘ₗ i.toLinearMap, fun g v =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g v), ?_⟩ ?_
  · rintro _ ⟨v, rfl⟩
    exact (i.toLinearMap v).2
  · exact (LinearMap.range_comp _ _).ge
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactOfUnderEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

open GlobalTheory.SplitPts

variable {L : Type} [Field L] [NumberField L]

private theorem ic_mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h

variable [IsCMField L] {n : ℕ}

private theorem ic_sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc

private theorem ic_cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl

end

theorem UpperTheory.mem_maximalCompact_of_under_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n) (w w' : Plc E), w'.under (𝓞 (Lp E)) = w.under (𝓞 (Lp E)) → cLoc w x ∈ KO (w.adicCompletion E) (Fin n) → cLoc w' x ∈ KO (w'.adicCompletion E) (Fin n) := by
  intro E _ _ _ n x w w' h hx
  rcases ic_sameOver h with rfl | rfl
  · exact hx
  · rw [ic_cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.2 j i)))
    · exact (ic_mem_O _).2 (((conjLoc_spec (GlobalTheory.SplitPts.conjE E) w').2.2 _).trans_le ((ic_mem_O _).1 (hx.1 j i)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormCharacterOfFrobeniusCompatibility
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
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

theorem UpperTheory.norm_character_of_frobenius_compatibility :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.Sol.CharFrob → UpperTheory.V.Af.Sol.NormChar := by
  intro P hC K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι η hη
  rcases hη with rfl | hN
  · exact ⟨1, rfl, Filter.Eventually.of_forall fun v => charEig_one ι v⟩
  obtain ⟨art, ha⟩ := P.litN.aut.art K Ω
  have hm : 0 < Module.finrank K M := Module.finrank_pos
  have hA : IsAlgPos η 0 := isAlgPos_zero_of_orderDvd (χ := η) hm hN.2.1
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι hA
  have hE := hC K Ω l ι η δ ⟨hδc, art, 0, ha, hA, hL⟩
  refine ⟨δ, ?_, hE.mono fun v hv => hv.2⟩
  have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, CharEig ι (δ.comp (res K Ω M)) w 1 := by
    filter_upwards [hN.2.2, (tendsto_under' (K := K) (K' := M)).eventually hE] with w h1 h2
    have hf := normV_under (K := K) w
    have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ hf).2 δ _ h2.2
    rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res K Ω M s)) (f' := fun _ => 1)
    (hδc.comp (continuous_restrictScalarsHom K M Ω)) continuous_const fun v hv _ A hA σ hσ => by
      have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
      rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
      exact h
  exact MonoidHom.ext fun s => congrFun key s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeBaseChangeAttached
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem exists_not_mem_asIdeal_pow_of_ne_zero (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)) : ∃ f : ℕ, normV w = normV (HeightOneSpectrum.under (𝓞 K) w) ^ f := by
  refine ⟨(w.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal, ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.asIdeal.under (𝓞 K)) (Ideal.IsPrime.under _ _) (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

private theorem tendsto_under_cofinite' (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] : Filter.Tendsto (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)
  refine Set.Finite.to_subtype (Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hfin.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h))
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨x.isPrime, ⟨rfl⟩⟩

private theorem algSat_pow_map_pow (n q f : ℕ) (B : Multiset ℂˣ) : algSat n (q ^ f) (Multiset.map (fun x => x ^ f) B) = Multiset.map (fun x => x ^ f) (algSat n q B) := by
  unfold algSat
  simp only [Multiset.bind_map, Multiset.map_map, Function.comp_def, Multiset.bind_singleton, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (by positivity)]

theorem UpperTheory.satake_base_change_attached :
    UpperTheory.V.Af.Sol.AttBc := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat sat' huniq hbc hatt hss
  refine ⟨hss, ?_⟩
  have hT := UpperTheory.frobenius_power_compatibility K M Ω l ι
  filter_upwards [hbc, (tendsto_under_cofinite' K M).eventually hatt.2] with w hw hv
  obtain ⟨f, hf⟩ := exists_not_mem_asIdeal_pow_of_ne_zero K M w
  obtain ⟨B, hB, hE⟩ := hv
  obtain ⟨B0, hB0, hB0'⟩ := hw f hf
  obtain rfl := huniq _ _ _ hB hB0
  refine ⟨_, hB0', ?_⟩
  have h2 := (hT w f hf).1 n r _ hE
  rw [hf, algSat_pow_map_pow]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.satake_galois_compatibility_of_hecke_eigensystem :
    HypothesesH → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeInvariantOfFrobConjOfEigenvalueBasic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic :
    UpperTheory.V.Af.Sol.FrobConj → UpperTheory.V.Af.Sol.EigBasic → UpperTheory.V.Af.Sol.InvSat := by
  intro hFC hEB K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat' hatt
  have hbad := Filter.eventually_cofinite.1 hatt.2
  have himg := hbad.image (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
  have hev := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M) himg.compl_mem_cofinite
  filter_upwards [hev] with w hw w' hw'
  have good : ∀ u : HeightOneSpectrum (𝓞 M), u.under (𝓞 K) = w.under (𝓞 K) →
      ∃ B, sat' u B ∧ FrobEig ι (r.comp (resG K M Ω)) u (algSat n (normV u) B) := by
    intro u hu
    by_contra hn
    exact hw ⟨u, hn, hu⟩
  obtain ⟨B, hB, hE⟩ := good w rfl
  obtain ⟨B', hB', hE'⟩ := good w' hw'
  obtain ⟨hN, hT⟩ := hFC K M Ω l ι n r w w' hw'
  have h1 := hT _ hE
  rw [← hN] at h1
  have hBB : B = B' := (hEB M Ω l ι w').2.2 n _ B B' h1 hE'
  exact ⟨B, hB, hBB ▸ hB'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

private theorem theta_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {P : CuspSub E a} (h : P.IsCsd) :
    (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  obtain ⟨T, hT⟩ := h
  let L := (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V
  refine ⟨L.symm.trans T, fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := L.surjective φ
  have e : (GlobalTheory.ThetaPull.thetaSub P).op o (L φ) = L (P.op (thetaOp o) φ) :=
    Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
  rw [e]
  exact (congrArg T (L.symm_apply_apply _)).trans
    ((hT o φ).trans (congrArg (P.op o) (congrArg T (L.symm_apply_apply φ)).symm))

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (Bc.cPl w) = normV w := by
  change Nat.card (𝓞 E ⧸ (Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

private theorem qPow_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (s : ℝ) :
    (qPow (Bc.cPl w) s)⁻¹ = qPow w (-s) := by
  have e : qPow (Bc.cPl w) s = qPow w s := Units.ext (by rw [coe_qPow, coe_qPow, normV_cPl])
  rw [e, inv_eq_iff_mul_eq_one, ← qPow_add, add_neg_cancel, qPow_zero]

theorem UpperTheory.satake_parameters_complex_conjugate :
    SatConj := by
  intro E _ _ _ w
  refine ⟨fun a P hP B hB => ?_, fun c d S => ?_⟩
  · have e : CG.mk (GlobalTheory.ThetaPull.thetaSub P) = CG.mk P := Quotient.sound (theta_iso hP)
    exact e ▸ UpperTheory.theta_satake_parameters_inverse E a P w B hB
  · unfold satTot
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Multiset.coe_mapAddMonoidHom (fun x : ℂˣ => x⁻¹), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply, mul_inv, qPow_cPl, Fin.revPerm_apply, Fin.val_rev]
    congr 2
    rw [Nat.cast_sub k.2]
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakePolarizationOfCuspidalTransfer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]

private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]

theorem UpperTheory.satakePolarization_of_cuspidalTransfer :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.Sol.PolSatR := by
  intro H F _ _ _ n hn π ψ h
  obtain ⟨π₁, h₁, -⟩ := UpperTheory.exists_contragredient_cuspSub F n π
  obtain ⟨B, hl, hr', hf, hc, hX⟩ := H.gkR F n π
  refine isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)
  filter_upwards [h] with w ⟨hu, S, hS, hE⟩
  refine ⟨S, hS, ?_⟩
  have e : (S.map (·⁻¹)).map (· * ψ.val w) = S := by
    rw [hE, Multiset.map_map]
    simp
  exact e ▸ (hasSat_invT h₁ hS).twist hu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem irr_nontrivial {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) : Nontrivial (Fin n → k) := by
  obtain ⟨hne, -, -⟩ := hirr
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  exact hne (Subsingleton.elim _ _)

private theorem smul_one_inj {k : Type} [Field k] {n : ℕ} [Nontrivial (Fin n → k)] (a b : k)
    (h : a • (1 : Matrix (Fin n) (Fin n) k) = b • 1) : a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.mulVec v) h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  exact smul_left_injective k hv h2

private theorem schur_scalar {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : GL (Fin n) k) (hg : ∀ s, r s * g = g * r s) :
    ∃ c : kˣ, (g : Matrix (Fin n) (Fin n) k) = (c : k) • 1 :=
  _root_.UpperTheory.Reformulated.B.Qi17.schur_scalar r hirr g hg

theorem UpperTheory.schur_extension :
    UpperTheory.V.Af.Sol.SchurExt := by
  intro Γ Γ' k _ _ _ _ n r r₁ φ hN hirr hiso
  obtain ⟨g, hg⟩ := hiso
  have hnt := irr_nontrivial _ hirr
  simp only [MonoidHom.comp_apply] at hg
  have hcomm : ∀ s t, (r.comp φ) t * (r s * (g * r₁ s * g⁻¹)⁻¹) =
      (r s * (g * r₁ s * g⁻¹)⁻¹) * (r.comp φ) t := by
    intro s t
    obtain ⟨u, hu⟩ := hN.conj_mem' (φ t) ⟨t, rfl⟩ s
    have h1 := hg u
    rw [hu] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : r (φ t) * r s = r s * ((r s)⁻¹ * r (φ t) * r s) := by group
    rw [MonoidHom.comp_apply, ← mul_assoc, h2, h1, hg t]
    group
  choose c hc using fun s => schur_scalar _ hirr _ (hcomm s)
  have hr : ∀ s, (r s : Matrix (Fin n) (Fin n) k) =
      (c s : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro s
    have h1 : r s = (r s * (g * r₁ s * g⁻¹)⁻¹) * (g * r₁ s * g⁻¹) := by group
    rw [h1, Units.val_mul, hc s, Matrix.smul_mul, Matrix.one_mul]
  have huniq : ∀ s (a : kˣ), (r s : Matrix (Fin n) (Fin n) k) =
      (a : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) → c s = a := by
    intro s a ha
    apply Units.ext
    apply smul_one_inj (n := n)
    rw [← hc s, Units.val_mul, ha, Matrix.smul_mul, Units.mul_inv]
  have hmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply huniq
    have h1 : g * r₁ (s * t) * g⁻¹ = (g * r₁ s * g⁻¹) * (g * r₁ t * g⁻¹) := by
      rw [map_mul]; group
    rw [map_mul r, Units.val_mul, hr s, hr t, h1, Units.val_mul (g * r₁ s * g⁻¹), Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Units.val_mul (c s)]
  refine ⟨MonoidHom.mk' c hmul, ?_, g, ?_⟩
  · ext t
    have : c (φ t) = 1 := huniq _ _ (by rw [← hg t]; simp)
    simp [this]
  · intro s
    apply Units.ext
    rw [hr s]
    simp only [Units.val_mul, tw_val, MonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_cyclic_subextension_over_rat :
    UpperTheory.V.Af.Sol.CycQ := by
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 3)
  obtain ⟨q, hq, -, hqp⟩ := Nat.exists_prime_gt_modEq_one 0 hp.ne_zero
  haveI := Fact.mk hq
  have hpdvd : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hqp.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {q} ℚ (CyclotomicField q ℚ)
  have hcardG : Nat.card Gal(CyclotomicField q ℚ/ℚ) = q - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ),
      Nat.totient_prime hq]
  haveI : IsCyclic Gal(CyclotomicField q ℚ/ℚ) :=
    isCyclic_of_surjective (IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
      (Polynomial.cyclotomic.irreducible_rat hq.pos)).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(CyclotomicField q ℚ/ℚ))
  have hH : Nat.card (Subgroup.zpowers (g ^ p)) = (q - 1) / p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero (by rw [hg, hcardG]; exact hpdvd), hg, hcardG]
  have hfin : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) = p := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ))
    rw [IntermediateField.finrank_fixedField_eq_card, hH,
      IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ), Nat.totient_prime hq] at h1
    obtain ⟨m, hm⟩ := hpdvd
    have hq2 := hq.two_le
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at h1
    exact Nat.eq_of_mul_eq_mul_right hmpos h1
  haveI : IsAbelianGalois ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) :=
    IsAbelianGalois.tower_bot ℚ _ (CyclotomicField q ℚ)
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers (g ^ p)), inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · classical
    rw [NumberField.isTotallyReal_iff]
    have hodd := InfinitePlace.nrRealPlaces_pos_of_odd_finrank
      (K := IntermediateField.fixedField (Subgroup.zpowers (g ^ p)))
      (by rw [hfin]; exact hp.odd_of_ne_two (by omega))
    obtain ⟨w0, hw0⟩ : ∃ w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))),
        w.IsReal := by
      by_contra hne
      push_neg at hne
      have : IsEmpty {w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) //
          w.IsReal} := ⟨fun w => hne w.1 w.2⟩
      simp [InfinitePlace.nrRealPlaces] at hodd
    intro w
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w0) (w' := w)
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isReal_smul_iff.mpr hw0
  · rw [hfin]; exact hp
  · rw [hfin]; omega
end

