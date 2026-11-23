module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

theorem nzFib_of_isLocSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  intro S G _ _ L δ σ i R _ ξ t hξ ht hσ r
  have hP := isGrpPullback_pullback G ξ
  obtain ⟨z, hz, hz'⟩ := hσ (ξ r)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hP.1 z r hz
  obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hk : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k := G.left.basicOpen_le _ hb
  have hle : (bL L ξ).L.U (fun _ => k.1) ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := by
    intro x hx
    refine ⟨mem_pull.1 hx, mem_pull.2 ?_⟩
    have e : G.hom (pullback.fst G.hom ξ x) = ξ (pullback.snd G.hom ξ x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    show G.hom (pullback.fst G.hom ξ x) ∈ δ.U i
    rw [e]
    exact hξ (Set.mem_univ _)
  have hy1 : y ∈ (bL L ξ).L.U (fun _ => k.1) := mem_pull.2 hk.1
  have hy2 := hle hy1
  have hb' : pullback.fst G.hom ξ y ∈ G.left.basicOpen (σ.f (k.1, fun _ => i)) := by
    have hm : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := ⟨hk, hy2⟩
    have e := congrArg G.left.basicOpen (σ.compat k (k.1, fun _ => i))
    rw [Scheme.basicOpen_mul] at e
    have e1 := G.left.basicOpen_res (σ.f k) (homOfLE (inf_le_left : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have e2 := G.left.basicOpen_res (σ.f (k.1, fun _ => i)) (homOfLE (inf_le_right : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have h1 := e1.ge ⟨hm, hb⟩
    have h2 := (e.le h1).2
    exact (e2.le h2).2
  refine ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k.1, ?_⟩⟩
  rw [ht (fun _ => k.1) hle]
  exact (Scheme.basicOpen_appLE (pullback.fst G.hom ξ) _ _ hle _).ge ⟨hy1, hb'⟩

end GlobalTheory.KeyVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPreimageAffineBaseChangeEqSumProducts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.BaseChangeSpan

theorem exists_sum_mul_of_closure {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T]
    (A : S →+* T) (B : S' →+* T) (h : Subring.closure (Set.range A ∪ Set.range B) = ⊤) (x : T) :
    ∃ (n : ℕ) (a : Fin n → S) (r : Fin n → S'), x = ∑ i, A (a i) * B (r i) := by
  have hx : x ∈ Subring.closure (Set.range A ∪ Set.range B) := h ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨1, fun _ => a, fun _ => 1, by simp⟩
    · exact ⟨1, fun _ => 1, fun _ => r, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n + m, Fin.append a b, Fin.append r t, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | neg y _ hy =>
    obtain ⟨n, a, r, rfl⟩ := hy
    exact ⟨n, fun i => -a i, r, by simp [Finset.sum_neg_distrib]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n * m, fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2,
      fun k => r (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2, ?_⟩
    rw [← finProdFinEquiv.sum_comp, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr (by simp) fun p _ => ?_
    simp only [Equiv.symm_apply_apply, map_mul]
    ring

end GlobalTheory.BaseChangeSpan

namespace GlobalTheory.BaseChangeSpan

theorem sections_preimage_affine_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  intro R R₁ _ _ ρ P p V hV x
  have sq : IsPullback (pullback.snd p (spMap ρ)) (pullback.fst p (spMap ρ)) (spMap ρ) p :=
    (IsPullback.of_hasPullback p (spMap ρ)).flip
  have hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  have hleG : (pullback.fst p (spMap ρ)) ⁻¹ᵁ V ≤
      (pullback.snd p (spMap ρ)) ⁻¹ᵁ ((spMap ρ) ⁻¹ᵁ ⊤) := by simp
  have po := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) hV hle hleG
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have htop : (⊤ : (Sp R₁).Opens) ≤ (spMap ρ) ⁻¹ᵁ ⊤ := by simp
  have hsub : Set.range ((pullback.snd p (spMap ρ)).appLE ((spMap ρ) ⁻¹ᵁ ⊤) _ hleG).hom ⊆
      Set.range (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom ((Sp R₁).presheaf.map (homOfLE htop).op y), ?_⟩
    rw [RingHom.comp_apply]
    change ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (pullback.snd p (spMap ρ)).appLE ⊤ _ le_top).hom ((Sp R₁).presheaf.map (homOfLE htop).op y) = _
    rw [Iso.hom_inv_id_assoc, ← CommRingCat.comp_apply]
    have h := Scheme.Hom.map_appLE (pullback.snd p (spMap ρ))
      (V := (pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top (homOfLE htop).op
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) y
  obtain ⟨n, a, r, hx⟩ := exists_sum_mul_of_closure ((pullback.fst p (spMap ρ)).app V).hom
    (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom)
    (by
      rw [eq_top_iff, ← hcl]
      exact Subring.closure_mono (Set.union_subset (hsub.trans Set.subset_union_right)
        Set.subset_union_left))
    x
  exact ⟨n, a, r, hx⟩

end GlobalTheory.BaseChangeSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDvrClosedFibreStalkUniformiser
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.GenFibre

theorem maximalIdeal_eq_span_of_isReduced {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) {a : R} (ha : a ≠ 0) (ha' : a ∈ maximalIdeal R)
    (hred : _root_.IsReduced (R ⧸ Ideal.span {a})) : maximalIdeal R = Ideal.span {a} := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 hR.le
  have hrad := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ha')
  rw [← hrad.radical, Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP, hPp⟩
  have hne : P ≠ ⊥ := fun h => ha (by
    have := hP (Ideal.mem_span_singleton_self a)
    rwa [h, Ideal.mem_bot] at this)
  exact (IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hne)).ge

theorem isReduced_quot_of_smooth {X B : Scheme.{0}} (π : X ⟶ B) [Smooth π] (y : X) :
    _root_.IsReduced (X.presheaf.stalk y ⧸
      (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  obtain ⟨b, z, rfl⟩ : ∃ (b : B) (z : π.fiber b), π.fiberι b z = y := ⟨π y, π.asFiber y, π.fiberι_asFiber y⟩
  have : Smooth (π.fiberToSpecResidueField b) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›
  have : IsReduced (π.fiber b) := GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)
  obtain ⟨e⟩ := GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber B X π b z
  exact isReduced_of_injective e.toRingHom e.injective

theorem unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H]
    [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T →
    ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} →
    GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField),
      GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  intro T _ _ _ H _ _ hH y hy hdim ϖ hϖ
  have hsm : Smooth H.hom := hH.smooth
  let S := (Sp T).presheaf.stalk (H.hom y)
  letI : Algebra T S := StructureSheaf.stalkAlgebra T (H.hom y)
  haveI : (H.hom y).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  haveI : IsLocalization.AtPrime S (H.hom y).asIdeal := StructureSheaf.IsLocalization.to_stalk T _
  have hb : (H.hom y).asIdeal = maximalIdeal T := by rw [hy]; rfl
  have hmS : maximalIdeal S = Ideal.span {algebraMap T S ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (H.hom y).asIdeal S, hb, hϖ, Ideal.map_span,
      Set.image_singleton]
  let O := H.left.presheaf.stalk y
  let a₀ : O := (H.hom.stalkMap y).hom (algebraMap T S ϖ)

  have hcst : cst H.hom ϖ = algebraMap O H.left.functionField a₀ := by
    have e₁ := algebraMap_germ (X := H.left) (x := y) (U := ⊤) trivial
      (H.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ))
    have e₂ := Scheme.Hom.germ_stalkMap_apply H.hom ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ)
    refine e₁.symm.trans ?_
    refine congrArg _ (e₂.symm.trans ?_)
    rfl

  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field T (by rw [hϖ, Ideal.span_singleton_eq_bot.2 rfl])
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors
  have hs0 : algebraMap T S ϖ ≠ 0 := fun h => hϖ0 ((IsLocalization.injective S
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))
  have ha₀ : a₀ ≠ 0 := by
    letI : Algebra S O := (H.hom.stalkMap y).hom.toAlgebra
    haveI : Module.Flat S O := Flat.stalkMap H.hom y
    have hr : IsSMulRegular O (algebraMap T S ϖ) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs0)
    intro h
    have h1 : (algebraMap T S ϖ) • (1 : O) = (algebraMap T S ϖ) • (0 : O) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one]
      exact h
    exact one_ne_zero (hr h1)
  have ha₀m : a₀ ∈ maximalIdeal O := map_nonunit (H.hom.stalkMap y).hom _
    (hmS ▸ Ideal.mem_span_singleton_self _)

  have hred := isReduced_quot_of_smooth H.hom y
  rw [hmS, Ideal.map_span, Set.image_singleton] at hred
  have hm : maximalIdeal O = Ideal.span {a₀} :=
    maximalIdeal_eq_span_of_isReduced hdim ha₀ ha₀m hred

  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hnf : ¬ IsField O := fun h => ha₀ (by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.1 h) ▸ ha₀m
    rwa [Ideal.mem_bot] at this)
  have hpr : Submodule.IsPrincipal (maximalIdeal O) := ⟨⟨a₀, hm⟩⟩
  haveI : IsDiscreteValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O hnf).out 1 5).2 hpr
  have hirr : Irreducible a₀ := IsDiscreteValuationRing.irreducible_iff_uniformizer a₀ |>.2 hm
  have hc : cst H.hom ϖ ≠ 0 := by
    rw [hcst]
    exact fun h => ha₀ (IsFractionRing.injective O H.left.functionField (h.trans (map_zero _).symm))
  refine ⟨hc, fun u hu => ?_⟩
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) u
  have hx : x ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hirr
  obtain ⟨n, v', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hirr
  have hv' : algebraMap O H.left.functionField (v' : O) ≠ 0 :=
    (v'.isUnit.map (algebraMap O H.left.functionField)).ne_zero
  refine ⟨(m : ℤ) - n, algebraMap O _ (v : O) * (algebraMap O _ (v' : O))⁻¹,
    UnitAt.mul ⟨_, v.isUnit, rfl⟩ (UnitAt.inv ⟨_, v'.isUnit, rfl⟩), ?_⟩
  rw [hcst, zpow_sub₀ (fun h => hc (hcst.trans h)), zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
  have hc' : algebraMap O H.left.functionField a₀ ≠ 0 := hcst ▸ hc
  field_simp

end GlobalTheory.Desc.GenFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem sharpOver_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left),
    SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  intro g n o _ ζ F W T T' P P' u f φ hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n o ζ T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  refine ⟨c', hc'u, pr', hmon, huniv', ?_⟩
  let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
  have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
  have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
  have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
  have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
  have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
    LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
  have h1 := pull_isLB P.isLB φ
  have h2 := pull_isLB l0 φ
  exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.finrank_le : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : Trait F),
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem Trait.finrank_le_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F,
    Module.finrank ℤ T.D.toPre.X ≤ g :=
  fun g n F hn T => Trait.finrank_le g n (by omega) F T

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCond
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem sum_boxEnt_diag {r : ℕ} (d : Fin r → ℝ) (z a b : Fin r) (h : (a, b) ≠ (z, z)) :
    ∑ c, boxEnt d z a b c c = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg h1, if_neg h2]
  · subst hab
    have haz : a ≠ z := fun hz => h (by rw [hz])
    have : ∀ c, boxEnt d z a a c c = (if c = a then Complex.I else 0) + (if c = z then -Complex.I else 0) := by
      intro c
      simp only [boxEnt, lt_irrefl, if_false, and_self]
      by_cases h1 : c = a
      · subst h1
        simp [haz]
      · simp [h1]
    simp [this, Finset.sum_add_distrib]
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne' (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne' (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt, if_neg h1, if_neg h2]

theorem boxEnt_skew {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b a' b' : Fin r) :
    boxEnt d z a b b' a' * (d b' : ℂ) + (d a' : ℂ) * (starRingEnd ℂ) (boxEnt d z a b a' b') = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp
  · subst hab
    simp only [boxEnt, lt_irrefl, if_false]
    by_cases h1 : a' = a ∧ b' = a
    · obtain ⟨rfl, rfl⟩ := h1
      simp [mul_comm]
    · have h1' : ¬ (b' = a ∧ a' = a) := fun hc => h1 hc.symm
      simp only [if_neg h1, if_neg h1']
      by_cases h2 : a' = z ∧ b' = z
      · obtain ⟨rfl, rfl⟩ := h2
        simp [mul_comm]
      · have h2' : ¬ (b' = z ∧ a' = z) := fun hc => h2 hc.symm
        simp only [if_neg h2, if_neg h2']
        simp
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp

theorem skewCond_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  intro E _ _ _ r Ψ d z hd k τ
  by_cases hτ : τ = k.1
  · have he : ∀ a b, boxVec d z k (τ, a, b) = boxEnt (d τ) z k.2.1.1 k.2.1.2 a b := by
      intro a b
      simp only [boxVec, if_pos hτ]
      rw [hτ]
    simp only [he]
    exact ⟨sum_boxEnt_diag _ _ _ _ k.2.2, fun a b => boxEnt_skew _ (hd τ) _ _ _ _ _⟩
  · have he : ∀ a b, boxVec d z k (τ, a, b) = 0 := by
      intro a b
      simp only [boxVec, if_neg hτ]
    simp [he]

end GlobalTheory.CovTop.VolUp.FrameBox
end

