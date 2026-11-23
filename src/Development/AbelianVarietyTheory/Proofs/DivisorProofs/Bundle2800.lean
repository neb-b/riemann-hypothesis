module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianRingStalk
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TraitCen

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]

theorem isNoetherianRing_stalk (M : RatModel o' Ω) (x : M.Z) : IsNoetherianRing (M.Z.presheaf.stalk x) := by
  have : IsDedekindDomain o' := ArithBase.ded (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  infer_instance

theorem isDomain_stalk (M : RatModel o' Ω) (x : M.Z) : IsDomain (M.Z.presheaf.stalk x) :=
  (M.stalkHom_injective x).isDomain _

theorem charZero_stalk (M : RatModel o' Ω) (x : M.Z) : CharZero (M.Z.presheaf.stalk x) := by
  have : CharZero Ω := ArithBase.char (o := o')
  exact ⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩

theorem exists_cdvr (M : RatModel o' Ω) (U₀ : M.Z.Opens) (hU : (U₀ : Set M.Z).Nonempty) (x : M.Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ M.Z),
      a (closedPoint W) = x ∧ ∀ t, (jK W ≫ a) t ∈ U₀ := by
  let O := M.Z.presheaf.stalk x
  have : IsNoetherianRing O := isNoetherianRing_stalk M x
  have : IsDomain O := isDomain_stalk M x
  have : CharZero O := charZero_stalk M x

  have hη : genericPoint M.Z ∈ U₀ := by
    obtain ⟨z, hz⟩ := hU
    exact (genericPoint_specializes z).mem_open U₀.isOpen hz
  have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨q, hq⟩ := h1
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη)
    (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)
  have hf₀ : f₀ ≠ 0 := fun h => hqf (by simp [h])

  let κ := ResidueField (PowerSeries O)
  let p := ringChar κ
  let c : PowerSeries O := if p = 0 then 1 else (p : PowerSeries O)
  have hc0 : c ≠ 0 := by
    by_cases hp : p = 0
    · simp [c, hp]
    · simp only [c, hp, if_false]
      rw [← map_natCast (PowerSeries.C (R := O))]
      exact (map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)
  let f : PowerSeries O := PowerSeries.X * PowerSeries.C f₀ * c
  have hfm : f ∈ maximalIdeal (PowerSeries O) := by
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hf0 : f ∉ (⊥ : Ideal (PowerSeries O)) := by
    rw [Ideal.mem_bot]
    exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0
  let φ : PowerSeries O →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))
  obtain ⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩ :=
    GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ
  let ψ' : O →+* W := ψ.comp PowerSeries.C
  have hψloc : IsLocalHom ψ := ⟨fun a ha => isUnit_of_map_unit φ a (by
    have h := (ha.map (residue W)).map ιk
    rw [← hψ]
    exact h)⟩
  have hCloc : IsLocalHom (PowerSeries.C (R := O)) := ⟨fun a ha => by
    simpa using ha.map (PowerSeries.constantCoeff (R := O))⟩
  have hψ'loc : IsLocalHom ψ' := RingHom.isLocalHom_comp ψ _
  have hψ'f₀ : ψ' f₀ ≠ 0 := fun h => hψf (by
    simp only [f, map_mul]
    rw [show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])
  have hcz : CharZero W := by
    obtain ⟨q, hq⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W q with hqp | hq0
    · exfalso
      have hqW : (q : W) = 0 := CharP.cast_eq_zero W q
      have hqκ : (q : κ) = 0 := by
        have h := congrArg (ιk.comp (residue W)) hqW
        rw [map_natCast, map_zero] at h
        refine (map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_
        rw [map_natCast]
        exact h
      have : CharP κ q := (CharP.charP_iff_prime_eq_zero hqp).2 hqκ
      have hpq : p = q := ringChar.eq κ q
      have hp : p ≠ 0 := hpq ▸ hqp.ne_zero
      apply hψf
      have hc : c = (q : PowerSeries O) := by simp only [c, if_neg hp, hpq]
      show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0
      rw [hc, map_mul, map_natCast, hqW, mul_zero]
    · subst hq0
      exact CharP.charP_to_charZero W
  let a : Sp W ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩
  · have h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O := IsLocalRing.comap_closedPoint ψ'
    show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · have ht : (jK W) t = (⊥ : PrimeSpectrum W) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    have hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O)) := by
      show f₀ ∉ Ideal.comap ψ' ⊥
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact hψ'f₀
    have := hf hm
    simp only [a, Scheme.Hom.comp_apply, ht]
    exact this

theorem exists_trait_cen : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o']
    [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty →
    ∀ (X : Scheme.{0}) (u₀ : U₀.toScheme ⟶ X) (u : X ⟶ F.X) (x : M.Z), IsClosed ({x} : Set M.Z) →
      ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ u T ξ ∧ ξ (IsLocalRing.closedPoint T.V) = x := by
  intro g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := _root_.GlobalTheory.Poinc.traitExtSt g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [hy, Category.assoc]
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.Poinc.TraitCen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteD
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibreProper

theorem isProper_of_irreducible_of_isProper_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  intro O _ _ _ _ X f hirr hsep hlft hqc hx hfib
  obtain ⟨x₀, hx₀⟩ := hx
  have hne : Nonempty X := ⟨x₀⟩
  obtain ⟨Y, P, π, q, s, U, hπ, hUne, hiso, hproj, hq, hcomm⟩ :=
    GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver O X f hsep hlft hqc hne
  have hs : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
    infer_instance
  set C : Set Y := π ⁻¹' (U : Set X) with hC
  have hsurj : Function.Surjective (π ∣_ U) := fun y =>
    ⟨(inv (π ∣_ U)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩

  have hUsub : (U : Set X) ⊆ π '' C := by
    intro u hu
    obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
    refine ⟨v.1, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rwa [morphismRestrict_base_coe] at this

  have hUirr : IsIrreducible (U : Set X) :=
    ⟨hUne, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have hCirr : IsIrreducible C := by
    haveI : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace hUirr
    haveI : IrreducibleSpace (π ⁻¹ᵁ U).toScheme :=
      (Scheme.homeoOfIso (asIso (π ∣_ U))).irreducibleSpace_iff.2 (inferInstanceAs (IrreducibleSpace (U : Set X)))
    have h := (IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ U).toScheme).image (fun y => (π ⁻¹ᵁ U).ι y)
      ((π ⁻¹ᵁ U).ι.continuous.continuousOn)
    convert h using 1
    ext y
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩; exact v.2

  have hπT : π '' closure C = Set.univ := by
    have hcl : IsClosed (π '' closure C) := π.isClosedMap _ isClosed_closure
    have hd : Dense (U : Set X) := U.isOpen.dense hUne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hd.closure_eq]
    exact closure_minimal (hUsub.trans (Set.image_mono subset_closure)) hcl
  have hmeet : ∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O := by
    obtain ⟨y, hy, hyx⟩ : x₀ ∈ π '' closure C := hπT ▸ Set.mem_univ x₀
    refine ⟨y, hy, ?_⟩
    rw [hcomm, Scheme.Hom.comp_apply, hyx, hx₀]
  have hfib' : IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := by
    rw [hcomm, (Iso.eq_inv_comp (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) π)).2
      (pullbackRightPullbackFstIso_hom_snd (f := f) (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (f' := π))]
    infer_instance
  have hclosed := _root_.GlobalTheory.FibProperClosed.isClosed_image_closure O Y P q s C hs hq hfib' hCirr hmeet
  have huc : UniversallyClosed f :=
    _root_.GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed _ X Y P f π q s (closure C) inferInstance hq hcomm isClosed_closure hclosed hπT
  exact ⟨⟩

end GlobalTheory.FibreProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem isPullback_kernel_of_kernelPair {S : Scheme.{0}} {A H B : Over S} [GrpObj A] [GrpObj B] (i : H ⟶ A)
    [Mono i] (q : A ⟶ B) [IsMonHom q] (h : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    IsPullback i (toUnit H) q η[B] := by
  have hi : i ≫ q = 1 := by
    have := congrArg (fun u => lift (𝟙 H) (1 : H ⟶ A) ≫ u) h.w
    simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, _root_.mul_one,
      MonObj.one_comp] at this
    exact this
  refine ⟨⟨by rw [hi, Hom.one_def]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst 1 (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
      ≫ fst H A) (fun s => ?_) (fun s => toUnit_unique _ _) (fun s l h1 _ => ?_)⟩⟩
  · have h1 := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1
    rw [Category.assoc, h1]
  · have h1' := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1'
    rw [← cancel_mono i, Category.assoc, h1', h1]


open GlobalTheory.TorsionKernelModel in
theorem exists_model (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ A.left) (ψ : A₀ ⟶ B₀) (n : ℕ)
    (hφ : IsGrpPullback A₀ A (spMap (algebraMap R K)) φ) (hB : IsAbelianScheme B₀) [IsMonHom ψ] [IsFinite ψ.left]
    [Flat ψ.left] [Surjective ψ.left] (hn : 1 ≤ n)
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left), IsAbelianScheme B ∧
      IsGrpPullback B₀ B (spMap (algebraMap R K)) φB := by
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hA.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul _ A hA n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, q, hab, _, hq₁, hq₂, hq₃, hq⟩ := GlobalTheory.IwLevel.quotGlobal_holds _ A Ga io hA ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) (isPullback_kernel_of_kernelPair io q hq)
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  exact ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl⟩

theorem exists_obj {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (v : Sp V ⟶ Sp R) (s : Sp K ⟶ Sp R) (hs : s = spMap (algebraMap V K) ≫ v) (o : Obj b N s)
    (G : Over (Sp V)) [GrpObj G] (φ : o.A.left ⟶ G.left) (hG : IsAbelianScheme G)
    (h : IsGrpPullback o.A G (spMap (algebraMap V K)) φ) :
    ∃ o' : Obj b N v, Nonempty (ObjMap o o' (spMap (algebraMap V K))) := by
  obtain ⟨g, rfl⟩ : ∃ g : R →+* V, v = spMap g := ⟨(Spec.preimage v).hom, (Spec.map_preimage v).symm⟩
  have e : s = spMap ((algebraMap V K).comp g) := by
    rw [hs, ← Spec.map_comp]; rfl
  subst e
  exact GlobalTheory.HTObjExt.extends_obj p D R b N V K g o G φ hG h

theorem exists_isPIsog_extend_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N hN hNp c V _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨⟨k, hk⟩, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V (FractionRing V) o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  obtain ⟨o', ⟨m'⟩⟩ := exists_obj V (FractionRing V) v _ rfl o₀' B φB hB hφB
  have hopen : IsOpenImmersion (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V (FractionRing V)
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have hdom : IsDominant (spMap (algebraMap V (FractionRing V))) := inferInstance
  obtain ⟨ψ, hψ, hm⟩ := GlobalTheory.UPel.HT.ES.PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨k, hk, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V (FractionRing V))) _ v hopen hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2) (fun y => inferInstance) o o' o₀ o₀' m m' ψ₀ h
  exact ⟨o', m', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.ES.IsogDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleAdicReductions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lbIso_of_compatible_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  intro R _ _ I hI X hX Y β b hpb hβ A A' hA hA' c hc hcomp
  have hle : ∀ e (p : (LB.div A' A).ι), b e ⁻¹ᵁ (LB.div A' A).U p ≤
      (LB.div (A'.pull (b e)) (A.pull (b e))).U (fun _ => p.1, fun _ => p.2) :=
    fun e p x hx => ⟨Set.mem_iInter.2 fun _ => hx.1, Set.mem_iInter.2 fun _ => hx.2⟩
  let s : ∀ e (i : (LB.div A' A).ι), Γ((Y e).left, b e ⁻¹ᵁ (LB.div A' A).U i)ˣ :=
    fun e p => res (hle e p) ((c e).s (fun _ => p.1, fun _ => p.2))
  have hs : ∀ e (z : (Y e).left) (p : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      gm (𝟙 _) z _ (s e p) = gw (c e) (𝟙 _) z p.1 (fun _ => p.2) :=
    fun e z p h => gm_res (𝟙 (Y e).left) z (hle e p) (by simpa using h) _
  have hg : ∀ e (z : (Y e).left) (p p' : (LB.div A' A).ι), b e z ∈ (LB.div A' A).U p →
      b e z ∈ (LB.div A' A).U p' →
      gm (b e) z _ ((LB.div A' A).g p p') =
        gm (b e) z _ (A'.g p.1 p'.1) * (gm (b e) z _ (A.g p.2 p'.2))⁻¹ := by
    intro e z p p' h h'
    have hm : b e z ∈ (LB.div A' A).U p ⊓ (LB.div A' A).U p' := ⟨h, h'⟩
    show gm (b e) z _ (res _ (A'.g p.1 p'.1) * (res _ (A.g p.2 p'.2))⁻¹) = _
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ _ _ hm _)
      ((map_inv _ _).trans (congrArg _ (gm_res _ _ _ hm _))))
  have hpg : ∀ e (z : (Y e).left) (k k' : A.ι), b e z ∈ A.U k → b e z ∈ A.U k' →
      gm (𝟙 (Y e).left) z _ ((A.pull (b e)).g (fun _ => k) (fun _ => k')) =
        gm (b e) z _ (A.g k k') := by
    intro e z k k' hk hk'
    have hp : (𝟙 (Y e).left) z ∈ (A.pull (b e)).U (fun _ => k) ⊓ (A.pull (b e)).U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (b e) _ (A.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hp _).trans ((gm_pull (𝟙 _) (b e) z (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))
  refine (_root_.GlobalTheory.FormalAlg.exists_isGen_of_reductions R I hI X hX Y β b hpb hβ (LB.div A' A) (LB.isLB_div hA' hA) s ?_ ?_ :
    ∃ t : LB.Gen (LB.div A' A), t.IsGen)
  · intro e z p p' h h'
    rw [hs e z p h, hs e z p' h', hg e z p p' h h']
    have := (isGen_iff (c e)).1 (hc e) _ (𝟙 _) z p.1 p'.1 (fun _ => p.2) (fun _ => p'.2) h.1 h'.1
      (mem_pull.2 h.2) (mem_pull.2 h'.2)
    rw [this, hpg e z p.2 p'.2 h.2 h'.2, Category.id_comp]
  · intro e z p h
    have h1 : b (e + 1) (β e z) = b e z := by rw [← hβ e]; rfl
    have hz : β e z ∈ b (e + 1) ⁻¹ᵁ (LB.div A' A).U p := show b (e + 1) (β e z) ∈ _ from h1 ▸ h
    rw [show gm (β e) z _ (s (e + 1) p) = gw (c (e + 1)) (β e) z p.1 (fun _ => p.2) from
      gm_res _ z (hle (e + 1) p) hz _, hcomp e z p.2 p.1 h.2 h.1, hs e z p h]

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_indep_sec : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T,
    IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ)
    (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT N L r hr r' hr'
  haveI : IsNoetherian Y := hq.isNoetherian
  have step1 : ∀ (P : HermLB q) (t t' : P.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
      (ht' : genericPoint Y ∈ nonzeroLocus t'),
      recVal (T (e + 1) L) L P (isRatSec_ratOfSec t ht) = recVal (T (e + 1) L) L P (isRatSec_ratOfSec t' ht') := by
    intro P t t' ht ht'
    have hS := (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t) ⟨_, ht⟩).union
      (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t') ⟨_, ht'⟩)
    obtain ⟨A, s, u, hs, hu⟩ := _root_.GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus k Y q hq (L 0) _ (hS.insert (genericPoint Y))
    have hgs : genericPoint Y ∈ nonzeroLocus s := hs (Set.mem_insert _ _)
    have hgu : genericPoint Y ∈ nonzeroLocus u := hu (Set.mem_insert _ _)
    have cs : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cs' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have cu : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cu' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have r1 := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t s ht hgs cs
    have r1' := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t' s ht' hgs cs'
    have r2 := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT P A (Fin.tail L) t u ht hgu cu
    have r2' := _root_.GlobalTheory.MixHt.recVal_cons_recip hR k Y q hq e hd T hT P A (Fin.tail L) t' u ht' hgu cu'
    have a1 := _root_.GlobalTheory.MixHt.recVal_tens_cons hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t ht) (L 0) A (Fin.tail L)
    have a1' := _root_.GlobalTheory.MixHt.recVal_tens_cons hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t' ht') (L 0) A (Fin.tail L)
    rw [← Fin.cons_self_tail L]
    linarith
  obtain ⟨A, u, t, t', hu, ht, ht', hrel⟩ := _root_.GlobalTheory.MixHt.exists_common_denom k Y q hq N r r' hr hr'
  have v1 := _root_.GlobalTheory.MixHt.recVal_tens hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r hr _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t ht) fun i j hi hj => (hrel i j hi hj).1
  have v2 := _root_.GlobalTheory.MixHt.recVal_tens hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r' hr' _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t' ht') fun i j hi hj => (hrel i j hi hj).2
  have s1 := step1 (N.tens A) t t' ht ht'
  linarith

end GlobalTheory.MixHt
end

