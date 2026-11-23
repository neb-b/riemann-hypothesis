module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.Bundle0001
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.SuppOfTypeOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IneInclOntoUnits
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0238

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PDrDesc
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.drDesc :
    DRDesc := by
  intro E Ω _ _ _ _ _ _ l _ ι n π r hr w hall P AI hT A hA O _ _ _ Bw hj
  obtain ⟨X, PM, u, h', hinf, hcl⟩ := hall A hA
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E X.K Ω A w u hA h' l P AI hT n r hr O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : X.K →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap X.K Ω))
  have hτL : τL.comp (algebraMap E X.K) = τ := by
    ext x
    show φ (Bw'.j (algebraMap X.K Ω (algebraMap E X.K x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E X.K Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hinf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E X.K Ω A w u hA h' l P AI hT n r hr O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfLifts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infLifts :
    InfStep → InfLifts := by
  intro hS E Ω _ _ _ _ _ _ n hn π Y hY
  induction hY with
  | refl =>
    intro τ
    exact congrArg (CG.mk π).infChar (RingHom.comp_id τ).symm
  | @tail Y Z _ hs ih =>
    intro τ
    obtain ⟨alg, tow, hG, hP, hW⟩ := hs
    have hcomp : (algebraMap Y.K Z.K).comp (algebraMap E Y.K) = algebraMap E Z.K := by
      ext x
      apply (algebraMap Z.K Ω).injective
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply Y.K Z.K Ω,
        ← IsScalarTower.algebraMap_apply E Y.K Ω, ← IsScalarTower.algebraMap_apply E Z.K Ω]
    rw [hS Y.K Z.K hP n hn Y.π Z.π hW τ, ih (τ.comp (algebraMap Y.K Z.K)), RingHom.comp_assoc, hcomp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PMixedOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

namespace UpperTheory.Gal.ToralGalois.R2

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : ρ.Equiv σ) {H : Subgroup G} (h : fixed ρ H ≠ ⊥) : fixed σ H ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toIntertwiningMap v, GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_, fun e => h0 ?_⟩
  · rw [← φ.toIntertwiningMap.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hv g hg]
  · exact φ.toLinearEquiv.injective (e.trans (map_zero φ.toLinearEquiv).symm)

private theorem pairwise_of_map {α β : Type*} (f : α → β) {r : β → β → Prop} (hr : Symmetric r) (t : Multiset α)
    (h : (t.map f).Pairwise r) : t.Pairwise fun a b => r (f a) (f b) := by
  induction t using Quot.inductionOn with
  | h l =>
    have h' : Multiset.Pairwise r ((l.map f : List β) : Multiset β) := h
    haveI : Std.Symm r := ⟨fun _ _ e => hr e⟩
    rw [Multiset.pairwise_coe_iff_pairwise, List.pairwise_map] at h'
    exact ⟨l, rfl, h'⟩

private theorem apart_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : Multiset (IrrGL (k := k))} (c : ℂ)
    (h : ((s.map fun y => y.nu c).filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z) :
    (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z := by
  rw [Multiset.filter_map] at h
  have hsym : Symmetric fun y z : IrrGL (k := k) => ¬ y.Inert z :=
    fun y z hyz e => hyz (IrrGL.inert_equivalence.symm e)
  obtain ⟨l, hl, hp⟩ := pairwise_of_map (t := s.filter fun y => 2 ≤ y.1) (fun y => y.nu c) hsym (by convert h using 3; exact Iff.rfl)
  refine ⟨l, hl, hp.imp fun {y z} hyz e => hyz ?_⟩
  exact IrrGL.inert_equivalence.trans (IrrGL.inert_equivalence.symm (IrrGL.inert_nu y c))
      (IrrGL.inert_equivalence.trans e (IrrGL.inert_nu z c))

end UpperTheory.Gal.ToralGalois.R2

open GlobalTheory.PlainMono in
theorem UpperTheory.Gal.ToralGalois.R2.mixedOf :
    MixedOf := by
  intro E Ω _ _ _ _ _ _ n π w σ hσ hfix hap A h rc hrc hm
  obtain ⟨a, ha, L⟩ := hrc
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hnu : ∀ (z : IrrGL (k := w.adicCompletion E)) (s : ℂ), IsGeneric z.rep → IsGeneric (z.nu s).rep :=
    fun z s hz => (isGeneric_congr (IrrGL.twEquiv z _ _)).1 ((isGeneric_twist_iff _).2 hz)
  have hgτ : IsGeneric (algNorm σ).rep :=
    hnu _ _ ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 hg)
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ := GlobalTheory.genericUnlinkedGL_outright (w.adicCompletion E) (algNorm σ).1 _
    (algNorm σ).rep (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr hgτ
  have hIsL : IsL ((List.ofFn Δ : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))
      (algNorm σ).rep :=
    ⟨c, y, hd, ⟨Δ, ⟨Fin.univ_val_map Δ, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self (algNorm σ).2.rep.irr).of_equiv (.refl _) e⟩
  have hm' := hm
  rw [L.langlands (List.ofFn Δ) (algNorm σ) hIsL, segSum] at hm'
  have hlen : ∀ i, (Δ i).len = 1 := by
    intro i
    have hmi := GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm' _
      (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    by_contra hne
    have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
      rw [← L.nu]; exact L.cusp _ ((Δ i).isCusp_first.nu _)
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by have := (Δ i).len_pos; omega) hmi
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred)
  obtain ⟨s, hs⟩ : ∃ s, HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep s :=
    ⟨_, GlobalTheory.LocGL.hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ h𝔪⟩
  have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hms := GlobalTheory.LocGL.ZelevinskyExpansion.msupp_eq_of_isL (algNorm σ).2.rep.irr hIsL hs'
  have mem : ∀ u ∈ s, ∃ i, (Δ i).first = u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    intro u hu
    have hu' : u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ∈ msupp ((List.ofFn Δ : List (Segment (w.adicCompletion E))) :
        Multiset (Segment (w.adicCompletion E))) := by
      rw [hms]; exact Multiset.mem_map_of_mem _ hu
    rw [msupp, Multiset.mem_bind] at hu'
    obtain ⟨D, hD, hu''⟩ := hu'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hD)
    rw [Segment.mem_ms, Segment.mem_carrier] at hu''
    obtain ⟨m, hm1, e'⟩ := hu''
    have : m = 0 := by have := hlen i; omega
    subst this
    exact ⟨i, by simpa using e'⟩
  refine ⟨fixed_ne_bot (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hfix, s, hs, ?_, apart_of_nu _ (hap _ hs')⟩
  intro y1 hy1 z1 hz1 hyz
  obtain ⟨i, hi⟩ := mem y1 hy1
  obtain ⟨j, hj⟩ := mem z1 hz1
  have key : (Δ i).first = (Δ j).first.nu 1 := by
    rw [hi, hj, hyz, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  have hne := ne_nu_one L (Δ j).isCusp_first
  by_cases hij : i = j
  · subst hij; exact hne key
  · refine hun j i (Ne.symm hij) ?_
    rw [eq_single_of_len (hlen j), eq_single_of_len (hlen i)]
    exact linked_single _ _ hne key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PRecChars
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.recChars :
    UpperTheory.Gal.InertialTypesAlt.SuppIne → RecChars := by
  intro hSI M Ω _ _ _ _ _ A u h n T ξ hξ hsup
  haveI : CharZero (u.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  have hsupx : HasSupport (IrrGL.of T.ρ T.smooth T.irred).rep (chars ξ hξ) :=
    hsup.of_equiv (IrrGL.equivOf T.ρ T.smooth T.irred)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (u.adicCompletion M) (IrrGL.of T.ρ T.smooth T.irred) n ξ
    (fun j => ξ j * absPow _ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    hξ (fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (fun _ => rfl)
  refine ⟨fun hun => ⟨_, hnu.1.1 hsupx, fun y hy => ?_, hnu.2.1 hun⟩, fun rc hrc a ha t => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have hSI' := hSI M Ω A u h rc hrc _ _ hsupx t
    obtain ⟨a₀, ha₀, L⟩ := hrc
    obtain rfl : a₀ = a := (UpperTheory.Zero.LLC.artEx M Ω A u h).unique ha₀ ha
    have e : algNorm T = (IrrGL.of T.ρ T.smooth T.irred).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := rfl
    have h1 : ∀ j, (rc (IrrGL.ofChar (ξ j) (hξ j))).inePol (t : G M Ω) = X - C ((ξ j (a₀ (ineIncl h t)) : ℂˣ) : ℂ) := by
      intro j
      rw [WD.inePol_of_mem_Ine _ t.2, L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp
    rw [← WD.inePol_of_mem_Ine _ t.2, e, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hSI', chars,
      Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => h1 j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PToTor
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2 GlobalTheory.UnitaryBC UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem split_of_padic {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g ∧ IsSplitAt w := by
  have hq : normV w = g := DiscreteGroups.sglob.DzType.normV_eq_of_padic w g i hi
  refine ⟨hq, GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w ?_ ?_⟩
  · have hp : (Ideal.absNorm w.asIdeal).Prime := by
      have : Ideal.absNorm w.asIdeal = g := by
        simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq
      rw [this]
      exact Fact.out
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  · have hmem : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      apply DiscreteGroups.sglob.DzType.mem_of_val_lt_one w
      have := DiscreteGroups.sglob.DzType.val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
      rw [map_natCast] at this
      rw [DiscreteGroups.sglob.DzType.alg_natCast]
      exact this
    have hsq := DiscreteGroups.sglob.DzType.g_not_mem_sq w g i hi
    have hl : g.Prime := Fact.out
    have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hl
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {((g : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span]; simp
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) ≤ w.asIdeal := by
      rw [hmap, Ideal.span_le]; simpa using hmem
    have := w.isPrime
    have : w.asIdeal.LiesOver (Ideal.span {(g : ℤ)}) :=
      ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
    have hb : Ideal.span {(g : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(g : ℤ)}) w.asIdeal hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact hsq (by simpa using hne)

private theorem dvd_of_support {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k)))
    (hs : HasSupport ρ s) (y : IrrGL (k := k)) (hy : y ∈ s) : y.1 ∣ N.factorial := by
  have h1 : 0 < y.1 := (hs.isCusp hy).1
  have h2 := hs.sum_fst
  have h3 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ hy)
  rw [h2, Fintype.card_fin] at h3
  exact Nat.dvd_factorial h1 h3

theorem UpperTheory.Gal.ToralGalois.R2.toTor :
    UpperTheory.Gal.InertialTypesAlt.SuppBC → UpperTheory.Gal.NearKilling.UnrField → UpperTheory.Gal.NearKilling.AllLift → UpperTheory.Gal.NearKilling.IneNorm → InfLifts → RecChars → UpperTheory.Zero.LLC.RecTExists → ToTor := by
  intro hSupp hUnr hLift hIne hInf hChars hRec E Ω _ _ _ _ _ _ l _ ι n hn π χ hs r hr w σ hσ hQ hM A h rc hrc
  obtain ⟨p, hp, i, hi⟩ := hQ
  haveI := hp
  obtain ⟨hq, hsp⟩ := split_of_padic w p i hi
  have hf : 0 < n.factorial := Nat.factorial_pos n
  have hSfin : {u : HeightOneSpectrum (𝓞 E) | ¬ ∃ B, (CG.mk π).HasSat u B}.Finite := by
    have h := Filter.eventually_cofinite.1
      (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E n π)
    simpa only [CG.hasSat_mk] using h
  obtain ⟨Xf, hXT, hXw, -⟩ := hUnr E Ω w hsp _ hf _ hSfin
  obtain ⟨P, χ', hPL, hPs, hPr⟩ := hLift E Ω l n hn π χ hs _ (fun u hu => not_not.1 hu) Xf hXT
  obtain ⟨w', h', -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E Xf.K Ω A w h
  haveI : w'.asIdeal.LiesOver w.asIdeal := ⟨(GlobalTheory.AboveL.comap_eq_of_placeOver h h').symm⟩
  have hXfix := (hXw A h).1
  have hnorm := (hXw A h).2 w' h'
  obtain ⟨σ', hσ', -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL Xf.K n P w'
  obtain ⟨art, hart⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  obtain ⟨art', hart'⟩ := GlobalTheory.localArtinExists_holds Xf.K Ω A w' h'
  obtain ⟨g, hg1, -⟩ := hIne E Xf.K Ω A w w' h h' hXfix art art' hart hart'
  obtain ⟨ξ, hξ, hT, hU⟩ := hSupp E Ω n hn π { K := Xf.K, π := P } hPL A w w' h h' p i hi hXfix σ σ' hσ hσ' hM.1 n.factorial
    (by rw [hnorm, hq]) (fun s hs y hy => dvd_of_support _ s hs y hy)
  obtain ⟨-, hTS, hTP⟩ := id hT
  obtain ⟨rc', hrc'⟩ := hRec Xf.K Ω A w' h'
  have hCh := hChars Xf.K Ω A w' h' n σ' ξ hξ hTS
  have hB : ∀ s : ↥(Ine (F := E) A), (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).inePol (s : G E Ω) =
      ∏ j, (X - C ((ξ j (art' (ineIncl h' (g s))) : ℂˣ) : ℂ)) := fun s => by
    have := hTP rc hrc art' hart' (g s)
    rwa [show AlgEquiv.restrictScalars E ((g s : ↥(Ine (F := Xf.K) A)) : G Xf.K Ω) = (s : G E Ω) from hg1 s] at this
  refine ⟨Xf, P, χ', w', h', σ', rc', hPs, hPr ι r hr, hInf E Ω n hn π { K := Xf.K, π := P } hPL, hσ', hCh.1 (hU hM), hrc',
    fun t => ⟨g t, fun z => ?_, ?_⟩⟩
  · exact (DFunLike.congr_fun (hg1 t) z).symm
  · rw [hCh.2 rc' hrc' art' hart' (g t)]
    obtain ⟨a₀, ha₀, L⟩ := hrc
    have e1 : (rc (algNorm σ)).charPol (ineIncl h t) = (rc (algNorm σ)).inePol (t : G E Ω) :=
      (WD.inePol_of_mem_Ine _ t.2).symm
    have e2 : algNorm σ = (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - ((n : ℕ) : ℝ)) / 2 : ℝ) : ℂ) := rfl
    rw [e1, e2, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hB t]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.R2g
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.r2g :
    MixedOf → ToTor → DRDesc → UpperTheory.Zero.LLC.RecTExists → GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := by
  intro hMix hTor hDR hRec hR1 E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hfix hcase A h rc hrc hm0
  rcases hcase with hpt | ⟨hQ, hap⟩
  · obtain ⟨haway, habove⟩ := hR1 E Ω l ι n hn π χ hπ r hr w σ hσ hpt
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · obtain ⟨hm, he⟩ := haway hl A h
      exact ⟨hm, fun t => by rw [he rc hrc]⟩
    · obtain ⟨hd, hb⟩ := habove hl
      refine ⟨hd, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hb Q AI hT A h O Bw hj
      exact ⟨h1, h2, fun t => h3 rc hrc _⟩
  · have hmix := hMix E Ω n π w σ hσ hfix hap A h rc hrc hm0
    obtain ⟨X, P, χ', u, h', T, rc', hP, hW, hinf, hTc, hPT, hrc', hine⟩ :=
      hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A h rc hrc
    obtain ⟨haway, habove⟩ := hR1 X.K Ω l ι n hn P χ' hP (resTo X.K r) hW u T hTc hPT
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∉ u.asIdeal := by
        intro hm
        apply hl
        rw [← h]
        rw [← h'] at hm
        simpa using hm
      obtain ⟨hm', he⟩ := haway hl' A h'
      have hres := GlobalTheory.AboveL.wdOf_restricts E X.K Ω A w u h h' l ι n r hl hl' hr.1
      obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
      refine ⟨hmono.mp hm', fun t => ?_⟩
      obtain ⟨t', hz, hc⟩ := hine t
      rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), he rc' hrc', hc]
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∈ u.asIdeal := by
        rw [← h] at hl
        rw [← h']
        simpa using hl
      obtain ⟨-, hb⟩ := habove hl'
      refine ⟨?_, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      · refine hDR E Ω l ι n π r hr.1 w fun A' hA' => ?_
        obtain ⟨rc₁, hrc₁⟩ := hRec E Ω A' w hA'
        obtain ⟨X₁, P₁, χ₁, u₁, h₁, T₁, rc₁', hP₁, hW₁, hinf₁, hTc₁, hPT₁, -, -⟩ :=
          hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A' hA' rc₁ hrc₁
        have hl₁ : ((l : ℕ) : 𝓞 X₁.K) ∈ u₁.asIdeal := by
          rw [← hA'] at hl
          rw [← h₁]
          simpa using hl
        exact ⟨X₁, P₁, u₁, h₁, hinf₁,
          ((hR1 X₁.K Ω l ι n hn P₁ χ₁ hP₁ (resTo X₁.K r) hW₁ u₁ T₁ hTc₁ hPT₁).2 hl₁).1⟩
      · obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := X.K) Bw hj Bw.LL
        have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
        have hp₀ := (hb Q AI hT A h' _ Bw₀ hj₀).1
        have hpst : IsPstAt Q Bw (r.comp (Dec (F := E) A).subtype) :=
          GlobalTheory.AboveLRes.isPstAt_of_resTo E X.K Ω A l Q AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
        obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
          GlobalTheory.AboveLRes.wdAt_resTo E X.K Ω A w u h h' l ι Q AI hT n r O Bw hj hpst
        obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
        obtain ⟨-, hm', hc'⟩ := hb Q AI hT A h' O' Bw' hj'
        refine ⟨hpst, hmono.mp hm', fun t => ?_⟩
        obtain ⟨t', hz, hc⟩ := hine t
        rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), hc' rc' hrc', hc]
end

