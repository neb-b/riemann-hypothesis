module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
section
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.csdOf :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CsdOf := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((UpperTheory.V.Af.autBridge hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := UpperTheory.V.Af.selfDualC hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem assemble (H : HypothesesH) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique) (hRec : RecTot)
    (hFrob : FrobTot) (hPol : PolOfFrob) (hLink : SatLink) (hConj : SatConj) (hIrr : IrrCase) : GalUnitary := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ :=
    GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw) E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hF : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) → FrobEig ι r w (algSat n (normV w) (satTot w d S)) := fun w hw S hS =>
    hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS i)) (hpar w)
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  refine ⟨r, _, hr.cont, hr.ss, fun w hw hu A hA => ?_, hr.ht, fun τ lam hl => ?_, fun w hw τ hτ => ?_, ?_, fun hirr => ?_⟩
  · choose S hSat using fun i => (satLoc H.toClassicalTheorems E (a i) w (ρ i w)).1 (by
      obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
        (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d hsum P ρ m σ hP hS hsplit w hu i (ρ i w) (hP.loc i w))
      exact ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩)
    exact (hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w) A hA).1
  · rw [← (hStr n c d (m · (ι.toRingHom.comp τ)) lam (hP.weight _ lam hl)).2]
    simp only [← hw₀]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Multiset.coe_mapAddMonoidHom, map_sum]
  · exact (locGlob_iff ι r w τ).2 ((hpar w).congr (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hw _ _ _ _ hτ (hsplit w hw))))
  · refine hPol E Ω l ι n r hr.cont hr.ss ?_
    filter_upwards [hev, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually hev]
      with w ⟨hw, _⟩ ⟨hw', S, hS'⟩
    refine ⟨satTot (Bc.cPl w) d S, ?_, hF _ hw' S hS'⟩
    rw [← (hConj E w).2 c d S]
    exact hF w hw _ fun i => (hConj E w).1 _ (P i) (hP.csd i) _ (hS' i)
  · refine hIrr E Ω l ι n hn π hπ c a d hsum P ρ m hP (hi hirr).1 (fun i => (hi₁ i ((hi hirr).2 i)).1) r hr.ss ?_
    filter_upwards [hev] with w ⟨hw, S, hS'⟩
    exact ⟨S, hS', hF w hw S hS'⟩

theorem UpperTheory.V.Af.galUnitary :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.GalUnitary := fun H =>
  assemble H (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.twistedDual_frobenius_compatibility (isoOfFrob H.toClassicalTheorems))
    (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H) UpperTheory.satake_parameters_complex_conjugate (UpperTheory.irreducible_case H)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GelfandKazhdanReal
section
open NumberField GlobalTheory.CuspRep UpperTheory.V

open GroundTheory.Automorphic in
private theorem lieMatch : UpperTheory.V.Af.Gk.LieMatch := by
  intro F _ _ _ a
  refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ =>
    congrArg Subtype.val (UpperTheory.V.Af.CuspFin.uAction_lieEq X φ)⟩
  rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
  rfl

theorem UpperTheory.V.Af.gelfandKazhdanReal :
    UpperTheory.V.Published.StrongMultOneReal → UpperTheory.V.Published.GelfandKazhdanReal :=
  Gk.gelfandKazhdan_of Gk.conjSub Gk.satConj Gk.satAE Gk.unitTwist Gk.pairOfTwist Gk.pairZero
    (Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) lieMatch)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

end Conj

private theorem infOf_of_weights {n : ℕ} (m : Fin n → ℤ) (μ : Multiset ℂ)
    (h : (Finset.univ.val.map fun i => -m i).map (fun n : ℤ => (n : ℂ)) = μ.map fun z => ((n : ℂ) - 1) / 2 - z) :
    μ = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id', Int.cast_neg, sub_neg_eq_add] at h2
  exact h2.symm

private theorem exists_over (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ¬ IsUnit (l : 𝓞 F) := fun hu => by
    have h := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h
    exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (l : 𝓞 F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨P, hP.isPrime, fun h0 => hl (by rw [h0] at hmem; exact hmem)⟩, hmem⟩

end UpperTheory.V.Af
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Af.NewformAutomorphy

private theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩

private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

end UpperTheory.V.Af.NewformAutomorphy

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
section
open UpperTheory.V.Af.Smo in
theorem UpperTheory.V.Af.strongMultOneReal :
    UpperTheory.V.Published.StrongMultOneReal := by
  have hTwistRed : TwistRed := twistRed
  have hCentLoc : CentLoc := centLoc
  have hAwayInd : AwayInd := awayInd
  have hDenseAway : DenseAway := denseAway
  have hCentEq : CentEq := centEq hCentLoc hAwayInd hDenseAway
  have hPsiLoc : PsiLoc := psiLoc
  have hLevelS : LevelS := levelS
  have hSetUp : SetUp := setUp hPsiLoc hLevelS
  have hEigOfSat : EigOfSat := eigOfSat
  have hCenSame : CenSame := cenSame hCentEq hSetUp hEigOfSat
  have hWhBasic : WhBasic := whBasic
  have hChartCont : ChartCont := chartCont
  have hSeedConv : SeedConv := seedConv hChartCont
  have hSeed : Seed := seed hWhBasic hSeedConv
  have hColConj : ColConj := colConj
  have hRowStep : RowStep := rowStep
  have hSchOfClosed : SchOfClosed := schOfClosed
  have hSchTensor : SchTensor := schTensor hSchOfClosed
  have hSchTw : SchTw := schTw hSchTensor
  have hPftDeriv : PftDeriv := pftDeriv
  have hPftMul : PftMul := pftMul
  have hPftSch : PftSch := pftSch_of hSchOfClosed hPftDeriv hPftMul
  have hBetaSch : BetaSch := betaSch hPftSch
  have hBetaInt : BetaInt := betaInt
  have hArchStep : ArchStep := archStep hSchTw hPftSch hBetaSch hBetaInt
  have hLinChange : LinChange := linChange
  have hArchKir : ArchKir := archKir hColConj hRowStep hArchStep hLinChange
  have hAvgChar : AvgChar := avgChar
  have hLocDual : LocDual := locDual
  have hLocStep : LocStep := locStep hAvgChar hLocDual
  have hLocKir : LocKir := locKir hColConj hRowStep hLocStep
  have hEmbY : EmbY := embY
  have hFinKir : FinKir := finKir hLocKir hPsiLoc hEmbY
  have hPsiInf : PsiInf := psiInf
  have hKillP : KillP := killP hArchKir hFinKir hEmbY hPsiInf hChartCont
  have hSphDict : SphDict := sphDict
  have hTjSet : TjSet := tjSet hSphDict
  have hSphZero : SphZero := sphZero hSphDict hTjSet hCentLoc
  have hSphAll : SphAll := sphAll hAwayInd hSphZero hEmbY
  have hInjP : InjP := injP
  have hEigMap : EigMap := eigMap hChartCont
  have hVanish : Vanish := vanish hSphAll hInjP hDenseAway hWhBasic hEigMap
  have hWhLin : WhLin := whLin
  have hConvCont : ConvCont := convCont hChartCont
  have hConvFub : ConvFub := convFub hChartCont
  have hConvNice : ConvNice := convNice hConvCont hConvFub
  have hPair : Pair := pair hSeed hSetUp hKillP hVanish hWhBasic hWhLin hConvNice hEigOfSat hEigMap
  have hInnerZero : InnerZero := innerZero
  have hOrthTr : OrthTr := orthTr
  have hOrthStep : OrthStep := orthStep hChartCont
  have hOrthConv : OrthConv := orthConv hOrthStep hConvCont
  exact smo_of UpperTheory.V.Af.Gk.unitTwist hTwistRed hCenSame hPair hInnerZero hOrthTr hOrthConv
end

