module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0006
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCohCharPf
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0003
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0007
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0003
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0004
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.DegreeTwoCohomologyComparisonLeft
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 2000000 in
theorem degree_two_cohomology_comparison_left (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A]
    [∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))] [IsDiscreteRep (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)] (hρ' : ContAction (twDual μ ρ)) :
    ∃ (E : H2 (twDual μ ρ) ≃+ cohomology (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2)
      (Ev : ∀ v : S, H2 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
      (∀ v x, Ev v (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) v 2 (E x)) ∧
      (∀ (z : ↥(Z2 (twDual μ ρ))) (x : cocycles (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2),
        (∀ s, cochainOf (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) (cocycleι (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2 x) s = d.eD (z.1 (d.e.symm (s 0), d.e.symm (s 1)))) → E (Submodule.Quotient.mk z) = cohomologyπ (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2 x) ∧
      (∀ (v : S) (z : ↥(Z2 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
        (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eD (z.1 (d.ev v (s 0), d.ev v (s 1)))) → Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 2 x) :=
  resCmpChar2' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev (twDual μ ρ) hρ' (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsDataEx
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem foundData_nonempty (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) :
    Nonempty (FoundData Kf S l r ζ Av μ M ρ) := by
  obtain ⟨e, he⟩ := gsEquiv_toGS' Kf.1 (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  obtain ⟨ιs, ev, hc, hι, hev⟩ := localCmp2' Kf.1 S Av hAv e he
  obtain ⟨A, hA, eM, hM⟩ := repCmp e ρ hρ
  obtain ⟨eD, hD, hDζ⟩ := dualCmp' Kf S hr ζ hζ hS e he μ hμ ρ A eM hM
  exact ⟨⟨e, he, ιs, ev, hc, hev, hι, A, hA, eM, hM, eD, hD, hDζ⟩⟩

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSideA
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion PositivityTheory.LocalTateOrthogonality.Gcoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Roots

variable {Kf : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime]

def rvF (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
    ZMod (l ^ r) →+ gsRoots S (l ^ r) :=
  ZMod.lift (l ^ r) ⟨zmultiplesHom (gsRoots S (l ^ r))
    (Additive.ofMul u : Additive (rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))), by
    have h := nsmul_gsRoots S (l ^ r) (Additive.ofMul u : Additive (rootsOfUnity (l ^ r)
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)))
    rw [← natCast_zsmul] at h
    exact (zmultiplesHom_apply _ _ _).trans h⟩

theorem rvF_eq (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (a : ZMod (l ^ r)) : rvF S u a = Additive.ofMul (u ^ a.val) := by
  have ha : a = ((a.val : ℤ) : ZMod (l ^ r)) := by simp
  conv_lhs => rw [ha]
  rw [rvF, ZMod.lift_coe]
  erw [zmultiplesHom_apply, natCast_zsmul]

theorem rvF_coe (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (a : ZMod (l ^ r)) :
    ((((Additive.toMul (rvF S u a) : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
      AlgebraicClosure ℚ) = ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) ^ a.val := by
  rw [rvF_eq]
  change (((((u ^ a.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
    (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :
    AlgebraicClosure ℚ)) = _
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]

end Roots

section Cochains

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem d_comp_homF (rho : Representation R G M) (A : Rep.{0} k G) (e : M →+ A.V)
    (he : ∀ g m, e (rho g m) = A.ρ g (e m)) (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  funext s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [inhomogeneousCochains.d_hom_apply, dn_app, map_add (f := _), map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]

end Cochains

theorem urChar_mulF {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+)
    (σ τ : Gal(Ω/K)) : urChar K Ω N (σ * τ) = urChar K Ω N σ + urChar K Ω N τ := by
  simp only [urChar, map_mul, toAdd_mul, map_add (f := _)]

theorem urChar_isLocallyConstant {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+) :
    IsLocallyConstant (urChar K Ω N) := by
  have h : urChar K Ω N = fun σ => unramifiedCoord K σ N := rfl
  rw [h, IsLocallyConstant.iff_continuous]
  exact continuous_unramifiedCoord N

theorem zmod_eq_of_pow_eq {L : Type} [CommRing L] [IsDomain L] {N : ℕ} [NeZero N] {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) {a : ℕ} {b : ZMod N} (h : ζ ^ a = ζ ^ b.val) : (a : ZMod N) = b := by
  have hmod : ζ ^ a = ζ ^ (a % N) := by
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [hmod] at h
  have h2 := hζ.pow_inj (Nat.mod_lt _ (NeZero.pos N)) (ZMod.val_lt b) h
  rw [← ZMod.natCast_mod, h2, ZMod.natCast_zmod_val]

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalTlPush
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN.TL

attribute [local instance 2000] Rep.hV2

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem inv_push (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (B : Rep.{0} ℤ G) [IsDiscreteRep B]
    [IsDiscreteRep (uliftIntToIntRep A)] (μ : uliftIntToIntRep A ⟶ B) (inv : cohomology B 2 →+ QZ)
    (x : cocycles A 2) :
    (inv.comp ((cohomologyMap μ 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv A 2).toAddMonoidHom)) (cohomologyπ A 2 x) =
      inv (cohomologyπ B 2 (HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cocyclesULiftInt A x))) := by
  show inv ((cohomologyMap μ 2).hom (cohomologyULiftIntAddEquiv A 2 (cohomologyπ A 2 x))) = _
  rw [cohomologyULiftIntAddEquiv_cohomologyπ']
  exact congrArg inv (cohomologyMap_cohomologyπ μ (cocyclesULiftInt A x))

theorem cochain_push (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (B : Rep.{0} ℤ G) [IsDiscreteRep B]
    [IsDiscreteRep (uliftIntToIntRep A)] (μ : uliftIntToIntRep A ⟶ B) (x : cocycles A 2)
    (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 (HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cocyclesULiftInt A x))) s =
      μ.hom (cochainOf A (cocycleι A 2 x) s) := by
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]

end Generic

section Local

variable {Kf : FiniteSubfield} [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
  {S : Set (HeightOneSpectrum (𝓞 Kf.1))} [Fintype S] {l r : ℕ} [Fact l.Prime]
  {ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)}
  {v : S} {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem ord_ne_zero_loc {ϖ : 𝓞 Kf.1} (hϖ : ord (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) = 1) :
    (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≠ 0 := by
  intro h
  rw [h, ord_zero] at hϖ
  exact zero_ne_one hϖ

theorem root_loc {ϖ : 𝓞 Kf.1} (hϖ0 : (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≠ 0) {y : AlgebraicClosure ℚ}
    (hy : y ^ (l ^ r) = algebraMap Kf.1 (AlgebraicClosure ℚ) (ϖ : Kf.1)) :
    (ιs v y) ^ ((⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ : ℕ+) : ℕ) =
      algebraMap ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ((Units.mk0 _ hϖ0 : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)ˣ) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) := by
  show (ιs v y) ^ (l ^ r) = _
  rw [← map_pow, hy, AlgHom.commutes, Units.val_mk0,
    IsScalarTower.algebraMap_apply Kf.1 ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))]
  rfl

theorem prim_loc {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    IsPrimitiveRoot (ιs v ζ) ((⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ : ℕ+) : ℕ) :=
  hζ.map_of_injective (ιs v).toRingHom.injective

set_option maxHeartbeats 1000000 in
theorem kummer_loc
    {ev : ((AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃ₐ[((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)] (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≃* Dec (F := Kf.1) A}
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    {ζ y : AlgebraicClosure ℚ} (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (g : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃ₐ[((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)] (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) : g (ιs v y) = ιs v ζ ^ (κ (ev g)).val * ιs v y := by
  have h1 := hev g y
  rw [hκ (ev g), map_mul, map_pow] at h1
  exact h1.symm

end Local


set_option maxHeartbeats 1000000 in
theorem found_side_inv' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (ϖ : 𝓞 Kf.1) (hϖ : ord (((ϖ : Kf.1) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) = 1)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap Kf.1 (AlgebraicClosure ℚ) (ϖ : Kf.1))
    (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (χ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hχ : ∀ σ, χ (ev σ) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
      ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ σ)
    (x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2)
    (hx0 : ∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)),
        ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x0) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          ζ ^ (κ (ev (s 0)) * χ (ev (s 1))).val) :
    gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x0) = - zmodToQZ (l ^ r) 1 := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs (l ^ r) v) (cohomologyπ _ 2 x0)).trans ?_
  refine (inv_push _ _ (rootsLocalMorZ S ιs (l ^ r) v) _ x0).trans ?_
  have hϖ0 := ord_ne_zero_loc (Kf := Kf) (v := v) hϖ
  have hY := root_loc (ιs := ιs) (v := v) (l := l) (r := r) hϖ0 hy
  have hζv := prim_loc (ιs := ιs) (v := v) hζ
  have hκv := kummer_loc (ιs := ιs) (v := v) (ev := ev) hev κ hκ
  have hHasse {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (N : ℕ+)
      (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) (Y : Ω) (hY : Y ^ (N : ℕ) = algebraMap K Ω ϖ)
      (ζ : Ω) (hζ : IsPrimitiveRoot ζ N) (κ : Gal(Ω/K) → ZMod (N : ℕ))
      (hκ : ∀ g : Gal(Ω/K), g Y = ζ ^ (κ g).val * Y)
      (c : cocycles (galUnitsZ K Ω) 2)
      (hc : ∀ s : Fin 2 → Gal(Ω/K), ((Additive.toMul (cochainOf _ (cocycleι _ 2 c) s) : Ωˣ) : Ω) =
        ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val) :
      brauerInvZOfIsSepClosure K Ω (cohomologyπ _ 2 c) = - zmodToQZ (N : ℕ) 1 := by
    classical
    have hN0 : (N : ℕ) ≠ 0 := N.ne_zero
    have hϖ0 : algebraMap K Ω (ϖ : K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K Ω).injective).2 ϖ.ne_zero
    have hY0 : Y ≠ 0 := by
      rintro rfl
      rw [zero_pow hN0] at hY
      exact hϖ0 hY.symm
    let ψ := urPsi (K := K) (Ω := Ω) N
    obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω ϖ)
    let Yu : Ωˣ := Units.mk0 Y hY0
    let bf : Gal(Ω/K) → (galUnitsZ K Ω).V := fun h =>
      Additive.ofMul (Yu ^ (urChar K Ω N h).val)
    have hbf_lc : IsLocallyConstant fun t : Fin 1 → Gal(Ω/K) => bf (t 0) := by
      have h1 : IsLocallyConstant (urChar K Ω N) :=
        (IsLocallyConstant.iff_continuous _).2 (continuous_urChar (K := K) (Ω := Ω) N)
      exact (h1.comp fun u => Additive.ofMul (Yu ^ u.val)).comp_continuous (continuous_apply 0)
    have hsum : cohomologyπ _ 2 c + cohomologyπ _ 2 w = 0 := by
      rw [← map_add (f := _)]
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.pi_succ_eq_zero_iff (galUnitsZ K Ω) 1 (c + w)).2
        ⟨fun t => bf (t 0), hbf_lc, ?_⟩
      have hd := PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (galUnitsZ K Ω).ρ (galUnitsZ K Ω) (AddEquiv.refl _)
        (fun _ _ => rfl) 1 (fun t => bf (t 0))
      simp only [AddEquiv.refl_apply] at hd
      rw [hd]
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_one, map_add (f := _), cochainOf_add, Pi.add_apply]
      have hwc' := hwc s
      have hc' := hc s
      let a0 := (urChar K Ω N (s 0)).val
      let a1 := (urChar K Ω N (s 1)).val
      let a01 := (urChar K Ω N (s 0 * s 1)).val
      let cc := charCocycle (charAdd ψ) (s 0, s 1)
      have hrel : ((N : ℕ) : ℤ) * cc = (a0 : ℤ) + a1 - a01 := charCocycle_urPsi N (s 0) (s 1)
      apply Additive.toMul.injective
      apply Units.ext
      rw [hwc']
      simp only [toMul_add, toMul_zsmul, Units.val_mul,
        Units.val_zpow_eq_zpow_val, bf]
      rw [hc', coe_unitsInvariant]
      have hL : ((Additive.toMul (((zRepOfMonoidEnd (galUnitsHom K Ω)) (s 0))
            (Additive.ofMul (Yu ^ (urChar K Ω N (s 1)).val)) -
            Additive.ofMul (Yu ^ (urChar K Ω N (s 0 * s 1)).val) +
            Additive.ofMul (Yu ^ (urChar K Ω N (s 0)).val)) : Ωˣ) : Ω) =
          (s 0) Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 := by
        show ((Additive.toMul ((Additive.ofMul (galUnitsHom K Ω (s 0) (Yu ^ a1)) : Additive Ωˣ) -
            Additive.ofMul (Yu ^ a01) + Additive.ofMul (Yu ^ a0)) : Ωˣ) : Ω) = _
        simp only [toMul_add, toMul_sub, toMul_ofMul, Units.val_mul,
          coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Yu, Units.val_mk0,
          map_pow, div_eq_mul_inv]
      refine Eq.trans hL ?_
      rw [hκ (s 0), mul_pow]
      have hYz : Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 = (algebraMap K Ω (ϖ : K)) ^ cc := by
        rw [← hY, show (Y ^ (N : ℕ)) ^ cc = Y ^ (((N : ℕ) : ℤ) * cc) by rw [zpow_mul, zpow_natCast],
          hrel, zpow_sub₀ hY0, zpow_add₀ hY0, zpow_natCast, zpow_natCast, zpow_natCast]
        ring
      have hζN : ζ ^ (N : ℕ) = 1 := hζ.pow_eq_one
      have hzk : (ζ ^ (κ (s 0)).val) ^ a1 = ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val := by
        rw [← pow_mul, ZMod.val_mul]
        conv_lhs => rw [← Nat.div_add_mod ((κ (s 0)).val * a1) (N : ℕ), pow_add, pow_mul, hζN,
          one_pow, one_mul]
      rw [← hzk, ← hYz]
      ring
    have hc0 : cohomologyπ _ 2 c = - cohomologyπ _ 2 w := eq_neg_of_add_eq_zero_left hsum
    rw [hc0, map_neg, hw]
    have hInv : brauerInvZOfIsSepClosure K Ω (galCupClass K Ω ψ ϖ) =
        zmodToQZ (N : ℕ) 1 := by
      obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
      let := algebraicValuativeRel K Ω
      let := algebraicTopology K Ω
      have := algebraicTopology_isValuativeTopology K Ω
      have := algebraicValuativeRel_valuativeExtension K Ω
      have hψ : ∀ g ∈ (unramifiedDegree K Ω).ker,
          (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) = 0 := by
        intro g hg
        show zmodToQZ (N : ℕ) (urChar K Ω N g) = 0
        rw [urChar_of_ker N (MonoidHom.mem_ker.1 hg), map_zero]
      have key := brauerInvZ_galCupClass_of_unramified (urPsi (K := K) (Ω := Ω) N) hψ hσ ϖ
      show brauerInvZ K Ω _ = _
      rw [key, hϖ, one_smul]
      show zmodToQZ (N : ℕ) (urChar K Ω N σ) = _
      rw [urChar_of_deg_one N hσ]
    exact congrArg Neg.neg hInv
  refine hHasse ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ (Units.mk0 _ hϖ0)
    (by rw [Units.val_mk0]; exact hϖ) (ιs v y) hY (ιs v ζ) hζv (fun σ => κ (ev σ)) hκv _ fun s => ?_
  rw [cochain_push]
  refine (rootsLocalMorZ_hom_apply S ιs (l ^ r) v _).trans ?_
  rw [hx0 s, map_pow]
  exact congrArg (fun m : ZMod (l ^ r) => ιs v ζ ^ m.val) (congrArg (κ (ev (s 0)) * ·) (hχ (s 1)))

end PositivityTheory.Lit1.PTN.TL
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

abbrev toFS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : FiniteSubfield :=
  ⟨K, inferInstance⟩

section
attribute [local instance 2000] Rep.hV2
theorem finite_dualRep' {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) [Finite D] [Finite A] :
    Finite (dualRep D A) := inferInstance
end

set_option maxHeartbeats 0 in
theorem shaDictFS : ShaDictFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := gsEquiv_toGS' K (S : Set (HeightOneSpectrum (𝓞 K)))
  obtain ⟨ιs, ev, hevc, hev⟩ := localCmp' K S Av hAv e he
  obtain ⟨A, hAd, eM, hM⟩ := repCmp e ρ hρ
  have hc' : ContAction (twDual μ ρ) :=
    GlobalTheory.CompanionTheory.GalDual.contAction_twDual K (AlgebraicClosure ℚ) l r M S Av μ ρ hρ hμ
  obtain ⟨eD, hD, -⟩ := dualCmp' (toFS K) S hr ζ hζ hS e he μ hμ ρ A eM hM
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), ((l ^ r : ℕ) : 𝓞 K) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex K :=
    hl.imp (fun h => ((Fact.out : l.Prime).odd_of_ne_two h).pow) id
  have hDZ : Nonempty (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r) ≃+ ZMod (l ^ r)) :=
    nonempty_addEquiv_gsRoots_of_mem (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) hSN
  haveI : Finite (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) := Finite.of_equiv _ hDZ.some.symm.toEquiv
  haveI hFA : Finite A := Finite.of_equiv M eM.toEquiv
  have htor : ∀ m : A, (l ^ r) • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := eM.surjective m
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul,
      map_zero]
  have htor1 : ∀ f : dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A, (l ^ r) • f = 0 :=
    nsmul_dualRep_eq_zero (fun d => nsmul_gsRoots (K := (toFS K)) _ _ d)
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) :=
    isDiscreteRep_dualRep _ _
  haveI hF1 : Finite (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) := finite_dualRep' _ _
  haveI hDDd : IsDiscreteRep (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) := isDiscreteRep_dualRep _ _
  obtain ⟨eB, hB⟩ := bidualCmp (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A (l ^ r) hDZ htor
  have hM'' : ∀ g m, (eM.trans eB) (ρ g m) = (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r))
      (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)).ρ (e g) ((eM.trans eB) m) := by
    intro g m
    simp only [AddEquiv.trans_apply, hM, hB]
  have X1 : Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).1
  have X2 : Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A)) (eM.trans eB) hM'').2
  have X3 : Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev ρ hρ A eM hM).1
  have X4 : Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) 2) :=
    (shaIso_of_rep K S Av e ιs ev hevc hev (twDual μ ρ) hc' (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A) eD hD).2
  refine ⟨⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, (dualRep (gsRoots (K := (toFS K)) (S : Set (HeightOneSpectrum (𝓞 K))) (l ^ r)) A), hDd, hF1, htor1, ?_, ?_⟩,
    ⟨(toFS K), (S : Set (HeightOneSpectrum (𝓞 K))), inferInstance, ιs, l ^ r, inferInstance, hSN, hK, A, hAd, hFA, htor, ?_, ?_⟩⟩
  · exact X1
  · exact X2
  · exact X3
  · exact X4

theorem shaCmpFS' : ShaCmpFS := shaCmpFS_of_dict shaDictFS

end PositivityTheory.Lit1.PTN
end
end

