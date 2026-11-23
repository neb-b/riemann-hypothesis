module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

theorem gsEquiv_toGS' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∃ e : GS (AlgebraicClosure ℚ) S ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) S,
      ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S),
        ((e (toGS (AlgebraicClosure ℚ) S σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          σ (y : AlgebraicClosure ℚ) := by
  have : IsGalois K (AlgebraicClosure ℚ) := IsAlgClosure.isGalois K (AlgebraicClosure ℚ)
  let E := maxUnramifiedOutside K (AlgebraicClosure ℚ) S
  let φ : G K (AlgebraicClosure ℚ) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)
  have hker : φ.ker = NS (AlgebraicClosure ℚ) S := by
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.NS_eq_fixingSubgroup K (AlgebraicClosure ℚ) S]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS (AlgebraicClosure ℚ) S ≃* Gal(E/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G K (AlgebraicClosure ℚ)) := inferInstance
  have : CompactSpace (GS (AlgebraicClosure ℚ) S) := Quotient.compactSpace
  refine ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq },
    fun σ y => ?_⟩
  exact AlgEquiv.restrictNormal_commutes σ E y

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem localCmp' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

def PerfectQZ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] : Prop :=
  Finite X ∧ Finite Y ∧ ∃ P : X →+ Y →+ QZ, Function.Bijective P ∧ Function.Bijective P.flip

theorem perfectQZ_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (h : PerfectQZ X Y) :
    PerfectQZ Y X := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have e : P.flip.flip = P := by ext; rfl
  exact ⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩

theorem perfectQZ_of_addEquiv {X Y X' Y' : Type} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (eX : X ≃+ X') (eY : Y ≃+ Y') (h : PerfectQZ X' Y') :
    PerfectQZ X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  have bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  refine ⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv,
    (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) =
        (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX := by
      funext x; ext y; rfl
    rw [e]
    exact bY.comp (h1.comp eX.bijective)
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip =
        (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY := by
      funext y; ext x; rfl
    rw [e]
    exact bX.comp (h2.comp eY.bijective)

theorem perfectPair_of_perfectQZ {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectQZ X Y) :
    PerfectPair (R := ZMod n) X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have torX : ∀ x : X, n • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have torY : ∀ y : Y, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hP : ∀ x y, n • P x y = 0 := fun x y => by rw [← map_nsmul, torY, map_zero]
  let Q : X →+ (Y →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n
      map_zero' := by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ]
      map_add' := fun x x' => by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ] }
  have hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y := fun x y =>
    zmodToQZ_zmodOfQZ (P x) (hP x) y
  refine ⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩,
    ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩
  · ext y; rw [← hQ, ← hQ, hxx]
  · obtain ⟨x, hx⟩ := h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩
    rw [hQ, hx]; rfl
  · ext x
    have := congrArg (fun f => zmodToQZ n (f x)) hyy
    exact (hQ x y).symm.trans (this.trans (hQ x y'))
  · obtain ⟨y, hy⟩ := h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩
    show zmodToQZ n (Q.toZModLinearMap n x y) = _
    rw [hQ]
    exact DFunLike.congr_fun hy x

def ShaDictFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) ∧
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2))

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem perfectQZ_of_found {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (h : ∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Y ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (X ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) : PerfectQZ X Y := by
  obtain ⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := poitouTate_sha_gs (K := K') (N := N) S' ιs hS hK A hA
  exact perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)

end FoundSide

set_option maxHeartbeats 1000000 in
theorem shaCmpFS_of_dict (h : ShaDictFS) : ShaCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hh := h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1),
    perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 ρ (locFam S Av) (continuous_locFam S Av)) hh.2)⟩

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH1_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH1 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
      refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
      have e := hm (χ g)
      simp only [Submodule.coe_subtype] at e ⊢
      change z.1 (ψ (χ g)) = rho (ψ (χ g)) m - m at e
      rw [h1] at e
      exact e
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨z.1 ∘ χ, z.2.1.comp hχ, fun g h => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h)
        simp only [Function.comp_apply, map_mul]
        rw [e]
        change z.1 (χ g) + rho (ψ (χ g)) (z.1 (χ h)) = _
        rw [h1]
      · rw [resH1, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext h
        change z.1 (χ (ψ h)) = z.1 h
        rw [h2]

theorem resCmp1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      ∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeTwoZero
section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_two_zero {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H2 rho ≃+ cohomology A 2)
    (hE : ∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
      (∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (ev (s 0), ev (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x)
    (E' : ↥(H0 rho') ≃+ cohomology B 0)
    (hE' : ∀ (z : ↥(H0 rho')) (x : cocycles B 0),
      (∀ s, cochainOf B (cocycleι B 0 x) s = eB z.1) → E' z = cohomologyπ B 0 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z2 rho)) (m : ↥(H0 rho')) :
    jp (cupProductH2H0 rho rho' rhoP b hb hbe (Submodule.Quotient.mk z) m) =
      - J (cupPairing μ (rfl : 2 + 0 = 2) (E (Submodule.Quotient.mk z)) (E' m)) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho'.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc B 0 (fun _ => eB m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho'.comp ev.toMonoidHom) B eB heB 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eB)
  have hmB : ∀ σ, B.ρ σ (eB m.1) = eB m.1 := fun σ => by
    rw [← heB]
    exact congrArg eB (hm σ)
  have hEz : E (Submodule.Quotient.mk z) = cohomologyπ A 2 x2 := hE z x2 (fun s => hx2 s)
  have hEm : E' m = cohomologyπ B 0 x0 := hE' m x0 (fun s => congrFun hx0 s)
  rw [hEz, hEm, cupPairing_cohomologyπ]
  refine hJ (cupCocycleZ2H0 rho rho' rhoP b hb hbe z m) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun j : Fin 0 => s ⟨2 + j, by omega⟩) = eB m.1 from
    congrFun hx0 _]
  rw [hmB]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun i : Fin 2 => s ⟨i, by omega⟩) =
    eA (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

end PositivityTheory.Lit1.PTN
end
end

