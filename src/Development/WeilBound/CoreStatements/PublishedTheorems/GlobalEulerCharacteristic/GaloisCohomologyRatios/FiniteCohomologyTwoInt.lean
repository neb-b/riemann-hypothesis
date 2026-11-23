module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NatCardInvariantsEqOfAddEquiv
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

section Cards

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]

theorem finite_of_moduleFinite : Finite M := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact Module.finite_of_finite (ZMod ℓ)

variable [Finite M]

theorem finite_cohomology_two_int [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Finite (cohomology (intRep M) 2) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Finite (gsRoots S ℓ) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))))
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_forall_fixed (gsRoots S ℓ)
  have hcyc (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hV : V ≤ W₀)
      (C : Rep.{0} (ULift.{0} ℤ) V.toSubgroup) [IsDiscreteRep C] [Finite C] [IsAddCyclic C]
      (htriv : ∀ g c, C.ρ g c = c) (hC : ∀ c : C, ℓ • c = 0) (r : ℕ) (hr : r ≤ 2) :
      Finite (cohomology C r) := by
    obtain ⟨L, hKL, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S V
    let d := Nat.card C
    have hd0 : d ≠ 0 := Nat.card_pos.ne'
    have : NeZero d := ⟨hd0⟩
    have hdℓ : d ∣ ℓ := by
      obtain ⟨c, hc⟩ := IsAddCyclic.exists_generator (α := C)
      rw [show d = addOrderOf c from (addOrderOf_eq_card_of_forall_mem_zmultiples hc).symm]
      exact addOrderOf_dvd_of_nsmul_eq_zero (hC c)
    have hdS (v : HeightOneSpectrum (𝓞 K.1)) (hv : (d : 𝓞 K.1) ∈ v.asIdeal) : v ∈ S := by
      by_contra hvS
      obtain ⟨a, ha⟩ := hdℓ
      apply hℓS v hvS
      rw [ha, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ d
    have hζmem := mem_maxUnramifiedOutside_of_pow_eq_one S hd0
      (fun v hv h => hv (hdS v h)) hζ.pow_eq_one
    have hζ' : IsPrimitiveRoot (⟨ζ, hζmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) d :=
      IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
        Subtype.val_injective
    let μ := Rep.res (gsSubtype S hL) (gsRoots S d)
    have hμ (g : (gsOpenSubgroup S hL).toSubgroup) (x : μ) : μ.ρ g x = x := by
      let u := Additive.toMul (show Additive (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S)) from x)
      have hu : (u : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ ℓ = 1 := by
        obtain ⟨a, ha⟩ := hdℓ
        rw [ha, pow_mul, (mem_rootsOfUnity _ _).1 u.property, one_pow]
      have h := hW₀ g (hV g.property) (Additive.ofMul ⟨u, (mem_rootsOfUnity _ _).2 hu⟩)
      apply Additive.toMul.injective
      apply Subtype.val_injective
      exact congrArg (fun y : gsRoots S ℓ => (Additive.toMul y).val) h
    have hcard : Nat.card C = Nat.card μ := by
      change d = Nat.card (Additive (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S)))
      rw [Nat.card_congr Additive.toMul, hζ'.card_rootsOfUnity]
    have : IsAddCyclic μ :=
      inferInstanceAs (IsAddCyclic (Additive (rootsOfUnity d (maxUnramifiedOutside K.1 ℚ̄ S))))
    have : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
      (placesOver_finite (Set.toFinite S)).to_subtype
    have : Finite (cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) d) r) :=
      finite_cohomology_rootsOfUnity L (placesOver S) d hd0 (fun _ hw => mem_placesOver_of_natCast_mem hdS hw) r hr
    have : Finite (cohomology μ r) :=
      Finite.of_equiv _ (gsRootsOfUnityCohomologyIso S hL d r).toLinearEquiv.toEquiv
    exact finite_cohomology_of_addEquiv_of_trivial C μ htriv hμ (addEquivOfAddCyclicCardEq hcard) r
  let U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S) := ⊤
  let A := Rep.res U.toSubgroup.subtype (intRep M)
  have : Finite A := inferInstanceAs (Finite (intRep M))
  have : Finite (cohomology A 2) :=
    finite_cohomology_of_forall_trivial ℓ 2 W₀
      (fun V hV A _ _ htriv hA r hr =>
        finite_cohomology_of_trivial_of_cyclic ℓ r
          (fun C _ _ _ htrivC hC => hcyc V hV C htrivC hC r hr) A htriv hA)
      U A (nsmul_intRep M) 2 le_rfl
  exact finite_cohomology_of_res_top (intRep M) 2

theorem card_H2_integral_module [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Nat.card (cohomology (intRep M) 2) = ℓ ^ Module.finrank (ZMod ℓ) (cohomology M 2) := by
  haveI := finite_cohomology_two_int M hℓS
  haveI : Finite (cohomology M 2) := Finite.of_equiv _ (cohomologyIntEquiv M 2).symm.toEquiv
  rw [← Nat.card_congr (cohomologyIntEquiv M 2).toEquiv]
  exact natCard_eq_pow_finrank_zmod ℓ _

local instance discreteIntegralDual : IsDiscreteRep (dualRep (gsRoots S ℓ) (intRep M)) :=
  isDiscreteRep_dualRep (gsRoots S ℓ) (intRep M)

local instance discreteLocalIntegralDual
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S ℓ) (intRep M))) :=
  isDiscreteRep_res_dualRep_of_finite (gsRoots S ℓ) (intRep M) (gsFinFamily S ιs v)

local instance finiteZModDual : Finite (dualRep (gsRootsZMod S ℓ) M) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite (gsRoots S ℓ) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))))
  have : Finite (dualRep (gsRoots S ℓ) (intRep M)) := finite_dualRep (D := gsRoots S ℓ) (M := intRep M)
  exact Finite.of_equiv _ (dualIntEquiv (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ) M).toEquiv

theorem card_H0_dual_module :
    Nat.card (cohomology (dualRep (gsRoots S ℓ) (intRep M)) 0) =
      ℓ ^ Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine (Nat.card_congr (H0Iso (dualRep (gsRoots S ℓ) (intRep M))).toLinearEquiv.toEquiv).trans ?_
  exact (natCard_invariants_eq_of_addEquiv (dualRep (gsRoots S ℓ) (intRep M)).ρ
    (dualRep (gsRootsZMod S ℓ) M).ρ
    (dualIntEquiv (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ) M)
    (fun h f => dualIntEquiv_comm _ _ M h f)).trans (natCard_eq_pow_finrank_zmod ℓ _)

theorem card_H0_dual_local
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (v : S) :
    Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S ℓ) (intRep M))) 0) =
      ℓ ^ Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine (Nat.card_congr (H0Iso (Rep.res (gsFinFamily S ιs v).toMonoidHom
    (dualRep (gsRoots S ℓ) (intRep M)))).toLinearEquiv.toEquiv).trans ?_
  exact (natCard_invariants_eq_of_addEquiv
    (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S ℓ) (intRep M))).ρ
    ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)
    (dualIntEquiv (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ) M)
    (fun h f => dualIntEquiv_comm _ _ M _ f)).trans (natCard_eq_pow_finrank_zmod ℓ _)

theorem card_sha_int [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    Nat.card (ptSha (gsFinFamily S ιs) (intRep M) 2) =
      ℓ ^ Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) := by
  haveI := finite_cohomology_two_int M hℓS
  haveI : Finite (cohomology M 2) := Finite.of_equiv _ (cohomologyIntEquiv M 2).symm.toEquiv
  have e : (shaSubmodule (gsFinFamily S ιs) M 2) ≃ (ptSha (gsFinFamily S ιs) (intRep M) 2) :=
    (cohomologyIntEquiv M 2).toEquiv.subtypeEquiv fun x => by
      rw [mem_ptSha_iff_mem_shaSubmodule]
      exact (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff _ (intRepEquiv M) (fun _ _ => rfl) 2 x).symm
  exact (Nat.card_congr e).symm.trans (natCard_eq_pow_finrank_zmod ℓ _)

end Cards

end PositivityTheory.Lit1.GEN.X
