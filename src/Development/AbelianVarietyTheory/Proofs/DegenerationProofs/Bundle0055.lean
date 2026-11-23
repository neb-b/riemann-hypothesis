module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.StructureHomApply
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChartsOfUniversal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem charts_of_universal {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I K : Type} [Fintype I] [Fintype K]
    {t : I → Ω} {e : ℕ} {v : K → J → Ω} (ht : M.HasDiv t)
    (hv : ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e))
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (hd : M'.HasDiv fun k => pairing φ s (v k))
    (hu : ∀ N : RatModel o Ω', N.HasDiv (fun q : I × K => φ (t q.1) * pairing φ s (v q.2)) →
      ∃ g, M'.IsHom N (AlgHom.id o Ω') g)
    (W : M.Z.Opens) (B : J → J → Ω) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty)
    (hB : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) :
    (∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z') ∧ ∀ i, pairing φ s (B i) ≠ 0 →
      ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div (fun j => pairing φ s (B j)) i z'} ∧
        M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
          Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) := by
  have hc : ∀ (N : RatModel o Ω') (i : I) (k : K) (z : N.Z), t i ≠ 0 →
      (N.Div (fun k => pairing φ s fun j => v k j / t i ^ e) k z ↔ N.Div (fun k => pairing φ s (v k)) k z) := by
    intro N i k z hi
    simp only [pairing_div]
    exact div_mul_iff (inv_ne_zero ((map_ne_zero φ).2 (pow_ne_zero _ hi)))
  have h1 : ∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z' := fun z' hz' => by
    obtain ⟨i, hi⟩ := ht (f z')
    obtain ⟨k, hk⟩ := hd z'
    exact hf.exists_div_pairing s ((hv _ i hi).symm.trans (hB _ hz')) ((hc M' i k z' hi.1).2 hk)
  refine ⟨h1, fun i hi => ?_⟩
  set R := Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
    Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) with hR
  have hR1 : ∀ x ∈ M.ringOn W, φ x ∈ R := fun x hx => Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  have hR2 : ∀ j, pairing φ s (B j) / pairing φ s (B i) ∈ R := fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
  have hfg : R.FG := by
    rw [hR, Algebra.adjoin_union]
    refine Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    rw [← AlgHom.map_adjoin, Algebra.adjoin_eq]
    exact (fg_ringOn hW hne).map φ
  haveI : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 hfg
  haveI : IsFractionRing R Ω' := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    have hK : Subfield.closure (R : Set Ω') = ⊤ :=
      EE.eq_top_of_pairing_mem hs (hB _ hne.some_mem) hi
        (map_mem_of_ringOn hW hne fun x hx => Subfield.subset_closure (hR1 x hx))
        fun j => Subfield.subset_closure (hR2 j)
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 (hK ▸ Subfield.mem_top x)
    have hle : Subring.closure (R : Set Ω') ≤ R.toSubring := Subring.closure_le.2 le_rfl
    exact ⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, rfl⟩
  have hN : ∀ x ∈ R, ∀ z, x ∈ (ofAffine o Ω' R).O z := fun x hx z => algebraMap_mem_O_ofAffine z (⟨x, hx⟩ : R)
  have hN1 : ∀ x ∈ M.ringOn W, φ x ∈ (ofAffine o Ω' R).ringOn (⊤ : (ofAffine o Ω' R).Z.Opens) :=
    fun x hx => mem_ringOn.2 fun z _ => hN _ (hR1 x hx) z
  obtain ⟨p, hp⟩ : ∃ p, M.IsHom (ofAffine o Ω' R) φ p :=
    exists_isHom_of_local fun z => ⟨⊤, W, trivial, hW, hne, hN1⟩
  have hpW : ∀ z, p z ∈ W := fun z => hp.map_mem_of_ringOn hW hne hN1 trivial
  have hNd : ∀ z, (ofAffine o Ω' R).Div (fun j => pairing φ s (B j)) i z := fun z => ⟨hi, fun j => hN _ (hR2 j) z⟩
  obtain ⟨g, hg⟩ := hu (ofAffine o Ω' R) fun z => by
    obtain ⟨i', hi'⟩ := ht (p z)
    obtain ⟨k, hk⟩ := hp.exists_div_pairing s ((hB _ (hpW z)).symm.trans (hv _ i' hi')) (hNd z)
    exact ⟨(i', k), div_mul_prod_iff.2 ⟨hp.div hi', (hc _ i' k z hi'.1).1 hk⟩⟩
  have hgf : g ≫ f = p := (hf.comp hg).unique hp
  let U : M'.Z.Opens := f ⁻¹ᵁ W ⊓ ⟨_, M'.isOpen_setOf_div (fun j => pairing φ s (B j)) i⟩
  have := isAffineOpen_of_isHom R (U := U) ?_ hg ?_
  · exact ⟨U, this.1, rfl, this.2⟩
  · refine Algebra.adjoin_le ?_
    rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hf.map_mem_O (mem_ringOn.1 hx _ hz.1)
    · exact mem_ringOn.2 fun z hz => hz.2.2 j
  · rintro _ ⟨z, rfl⟩
    have hz : f (g z) ∈ W := by
      have := hpW z
      rwa [← hgf] at this
    obtain ⟨j, hj⟩ := h1 _ hz
    exact ⟨hz, hg.div_of_div hj (hNd z)⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocus
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread.ClosedFac

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

def str {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) : CommRingCat.of R ⟶ Γ(H, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom q U)

theorem fromSpec_comp {H : Scheme.{0}} (q : H ⟶ Sp R) {U : H.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (str q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl

theorem str_res {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) (a : R) :
    str q U a = H.presheaf.map (homOfLE le_top).op (str q ⊤ a) :=
  (GlobalTheory.SectionsCommRing.map_structureHom q le_top a).symm

theorem appTop_str {H T : Scheme.{0}} (q : H ⟶ Sp R) {R' : Type} [CommRing R'] (g : R →+* R') (x : T ⟶ H)
    (t : T ⟶ Sp R') (w : x ≫ q = t ≫ spMap g) (a : R) : x.appTop (str q ⊤ a) = str t ⊤ (g a) := by
  have e {Y : Scheme.{0}} {S : Type} [CommRing S] (p : Y ⟶ Sp S) :
      str p ⊤ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop :=
    congrArg ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ·) (Scheme.Hom.appLE_eq_app (f := p) (U := ⊤))
  have : str q ⊤ ≫ x.appTop = CommRingCat.ofHom g ≫ str t ⊤ := by
    rw [e, e, Category.assoc, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => φ.hom a) this

theorem eq_zero_of_app_eq_zero {H : Scheme.{0}} {U : H.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (f : Γ(H, U) ⟶ B) (s : Γ(H, U)) (hs : (Spec.map f ≫ hU.fromSpec).app U s = 0) : f s = 0 := by
  have hz : ⊤ ≤ (Spec.map f ≫ hU.fromSpec) ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(H, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(H, U)).presheaf.map_id _
  have h2 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map f).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [h1, ← Scheme.ΓSpecIso_inv_naturality] at h2
  have h3 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz s = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hs, map_zero]
  rw [h2, CommRingCat.comp_apply] at h3
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective).1 h3

theorem exists_mul_eq_zero [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Z H : Scheme.{0}} (i : Z ⟶ H) (q : H ⟶ Sp R) [IsLocallyNoetherian H]
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) (U : H.affineOpens) :
    ∃ a : R, a ≠ 0 ∧ ∀ s ∈ i.ker.ideal U, str q U.1 a * s = 0 := by
  classical
  let M : Submonoid Γ(H, U.1) := (nonZeroDivisors R).map (str q U.1).hom
  let B := Localization M
  let φ : R →+* B := (algebraMap Γ(H, U.1) B).comp (str q U.1).hom
  have hφ (y : nonZeroDivisors R) : IsUnit (φ y) := IsLocalization.map_units B (⟨_, y, y.2, rfl⟩ : M)
  let ψ : K →+* B := IsLocalization.lift (M := nonZeroDivisors R) hφ
  obtain ⟨y, hy⟩ := h B (spMap (algebraMap Γ(H, U.1) B) ≫ U.2.fromSpec) (spMap ψ) (by
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact (IsLocalization.lift_comp (M := nonZeroDivisors R) hφ).symm)
  have key (s : Γ(H, U.1)) (hs : s ∈ i.ker.ideal U) : ∃ a : R, a ≠ 0 ∧ str q U.1 a * s = 0 := by
    have h1 := (y ≫ i).ideal_ker_le U (y.le_ker_comp i U hs)
    rw [hy] at h1
    have h2 : algebraMap Γ(H, U.1) B s = 0 :=
      eq_zero_of_app_eq_zero U.2 (CommRingCat.ofHom (algebraMap Γ(H, U.1) B)) s h1
    obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff M B s).1 h2
    exact ⟨a, nonZeroDivisors.ne_zero ha, hm⟩
  have := IsLocallyNoetherian.component_noetherian U
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (i.ker.ideal U)
  have hS' (s : S) : s.1 ∈ i.ker.ideal U := hS ▸ Ideal.subset_span s.2
  choose a ha ha' using fun s : S => key s (hS' s)
  refine ⟨∏ s, a s, Finset.prod_ne_zero_iff.2 fun s _ => ha s, fun s hs => ?_⟩
  rw [← hS] at hs
  refine Submodule.span_induction (fun s hs => ?_) (mul_zero _) (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hs
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨s, hs⟩ : S)), map_mul, mul_assoc, ha' ⟨s, hs⟩, mul_zero]
  · rw [mul_add, hu, hv, add_zero]
  · rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

theorem exists_lift (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R) (hi : IsClosedImmersion i)
    (hq : LocallyOfFiniteType q) (hq' : QuasiCompact q)
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  classical
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS, hSU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : H.Opens))).1
    isCompact_univ
  have : Fintype S := hS.fintype
  choose a ha ha' using exists_mul_eq_zero i q h
  refine ⟨∏ U : S, a U, Finset.prod_ne_zero_iff.2 fun U _ => ha U, fun R' _ g hg T x t w => ?_⟩
  set s := str q ⊤ (∏ U : S, a U) with hs
  have hx : IsUnit (x.appTop s) := by
    rw [hs, appTop_str q g x t w]
    exact hg.map _
  have hle : i.ker ≤ (H.basicOpen s).ι.ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) ?_ fun U u hu => ?_
    · rw [hSU, iSup_subtype]
    · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      have h0 : str q U.1.1 (∏ U : S, a U) * u = 0 := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ U), map_mul, mul_assoc, ha' _ u hu, mul_zero]
      have h1 : IsUnit ((H.basicOpen s).ι.app U.1.1 (str q U.1.1 (∏ U : S, a U))) := by
        rw [str_res, ← hs, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        refine IsUnit.map _ ?_
        refine (H.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => ?_
        refine (Scheme.mem_basicOpen _ _ z _).1 ?_
        rw [← Scheme.preimage_basicOpen]
        exact z.2
      exact h1.mul_right_eq_zero.1 (by rw [← map_mul, h0, map_zero])
  have hr : Set.range x ⊆ Set.range (H.basicOpen s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ x ⁻¹ᵁ H.basicOpen s
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hx]
    trivial
  refine ⟨IsOpenImmersion.lift _ x hr ≫ IsClosedImmersion.lift i _ hle, ?_⟩
  rw [Category.assoc, IsClosedImmersion.lift_fac, IsOpenImmersion.lift_fac]

end GlobalTheory.GenSpread.ClosedFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.TestBasis

open FreeNear

theorem exists_eStd_eq_linear (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
  · by_contra hxH
    let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
    obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
      (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
    obtain ⟨b, hb⟩ := exists_eStd_eq_linear _ _ (f ∘ₗ H'.mkQ)
    have hb' : b ∈ S.perp H := fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
    have h1 : eStd S.g _ x b = 0 := hx b hb'
    rw [Weights.eStd_swap, neg_eq_zero, hb] at h1
    exact hf h1
  · rw [Weights.eStd_swap, hy x hx, neg_zero]

variable {S} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem exists_nsmul_of_wt_eq_zero [ArithBase o Ω] (α : τ.X) (h : τ.wt α = 0) : ∃ v, α = S.N • v := by
  choose w hw using fun x => QuotientAddGroup.mk_surjective (τ.yy x)
  have h1 := ((test_weights o Ω S p y₀ τ).2 _ τ.isoFree le_rfl w (fun x => (hw x).symm) τ.yy.ker
    (by rw [perp_perp, AddSubgroup.closure_eq]) α).1 (fun t h₂ _ => by rw [h]; rfl)
  have h2 : AddSubgroup.closure (w '' τ.yy.ker ∪ Set.range fun v₀ : τ.X => S.N • v₀) ≤
      (nsmulAddMonoidHom S.N : τ.X →+ τ.X).range := by
    rw [AddSubgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | ⟨v, rfl⟩)
    · have h3 := hw x
      rw [AddMonoidHom.mem_ker.1 hx, QuotientAddGroup.eq_zero_iff] at h3
      obtain ⟨u, hu⟩ := h3
      exact ⟨S.r • u, by rw [← hu]; exact (mul_nsmul u S.r S.N).symm⟩
    · exact ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := h2 h1
  exact ⟨v, hv.symm⟩

theorem q_le_of_wt_eq [ArithBase o Ω] {α β : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀))
    (h : τ.wt β = τ.wt α) : τ.q α ≤ τ.q β := by
  obtain ⟨v, hv⟩ := exists_nsmul_of_wt_eq_zero τ (β - α) (by rw [map_sub, h, sub_self])
  have := hα v
  rwa [← hv, add_sub_cancel] at this

theorem exists_norm_eq_exp {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ l : PadicAlgCl p, ‖l‖ = Real.exp (τ.q α / S.N) := by
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  obtain ⟨x, hx⟩ := τ.δ_max.1
  refine ⟨y₀ ⟨S.th x, S.th_mem x⟩ / y₀ ⟨_, hk⟩, ?_⟩
  have hx' : ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = τ.δ := hx
  rw [norm_div, hx', h, Real.exp_neg]
  have := τ.δ_pos.ne'
  have := (Real.exp_pos (τ.q α / S.N)).ne'
  field_simp

theorem exists_proj_ne_zero {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ j i, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) ≠ 0 := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [h1] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, h0, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

end GlobalTheory.ZH.TestBasis

namespace GlobalTheory.ZH


open FreeNear TestBasis in
theorem exists_adapted_basis_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (B : Matrix S.J S.J (PadicAlgCl p)) (l : S.J → PadicAlgCl p) (α : S.J → τ.X), (∀ i j, ‖B i j‖ ≤ 1) ∧ ‖B.det‖ = 1 ∧ (∀ i v₀, τ.q (α i) ≤ τ.q (α i + S.N • v₀)) ∧ (∀ i, ‖l i‖ = Real.exp (τ.q (α i) / S.N)) ∧ (∀ c, ∃ i, τ.wt (α i) = c) ∧ (∀ i, ((S.proj _ (τ.wt (α i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (B i) = B i) ∧ τ.E = Submodule.span (OO p) (Set.range fun i j => l i * B i j) := by
  intro o Ω _ _ _ hA S p _ y₀ τ hint
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := proj_orthogonal S _ τ.isoFree
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (OO p) S.J
    (S.perp τ.yy.ker →+ ZMod S.N) (fun c => φ.mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  choose a ha hwa using (test_weights o Ω S p y₀ τ).1
  choose f hf using fun c => exists_norm_eq_exp τ (ha c)
  refine ⟨Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i))), fun i => f (κ i),
    fun i => a (κ i), fun i j => hint _, ?_, fun i => ha _, fun i => hf _, fun c => ?_, fun i => ?_, ?_⟩
  · have h1 : (((Matrix.of fun i j => φ.mapMatrix (S.proj _ (κ i)) j (col i)).det : OO p) : PadicAlgCl p) =
        (Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))).det :=
      RingHom.map_det (OO p).subtype _
    rw [← h1]
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hdet)
  · by_contra! h
    obtain ⟨j, i, hji⟩ := exists_proj_ne_zero τ (ha c)
    rw [hwa] at hji
    have h1 := (hspan c).le (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : {v : S.J → OO p | ∃ i, κ i = c ∧ v = fun j => φ.mapMatrix (S.proj _ c) j (col i)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨i, hi, _⟩ => h i ((hwa _).trans hi)
    rw [h2, Submodule.span_empty, Submodule.mem_bot] at h1
    exact hji (congrArg Subtype.val (congrFun h1 j))
  · rw [hwa]
    funext j
    have h1 := congrArg (fun a => y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul (κ i) (κ i)) j) (col i))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [if_true, Matrix.mul_apply, map_sum, map_mul] at h1
    exact h1
  · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨α, l, i, hα, hl, rfl⟩
      generalize hc : τ.wt α = c
      have h1 : ∀ w ∈ Submodule.span (OO p) {v : S.J → OO p | ∃ i, κ i = c ∧
          v = fun j => φ.mapMatrix (S.proj _ c) j (col i)},
          (fun j => f c * (w j : PadicAlgCl p)) ∈ Submodule.span (OO p) (Set.range fun i j =>
            f (κ i) * y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem _ h' =>
          obtain ⟨i', rfl, rfl⟩ := h'
          exact Submodule.subset_span ⟨i', rfl⟩
        | zero =>
          have : (fun j => f c * (((0 : S.J → OO p) j : OO p) : PadicAlgCl p)) = 0 := funext fun j => by simp
          rw [this]
          exact Submodule.zero_mem _
        | add a a' _ _ ha ha' =>
          convert Submodule.add_mem _ ha ha' using 1
          funext j
          simp [mul_add]
        | smul s a _ ha =>
          convert Submodule.smul_mem _ s ha using 1
          funext j
          change f c * ((s : PadicAlgCl p) * a j) = (s : PadicAlgCl p) * (f c * a j)
          ring
      have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
      have hpos : 0 < ‖f c‖ := hf c ▸ Real.exp_pos _
      have h0 : f c ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / f c ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hf]
        refine hl.trans (Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)))
        exact q_le_of_wt_eq τ hα ((hwa c).trans hc.symm)
      have h3 : (fun j => l * y₀ (algebraMap o S.R (S.proj _ c j i))) =
          (⟨_, hq⟩ : OO p) • fun j => f c * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
        funext j
        change _ = l / f c * (f c * y₀ (algebraMap o S.R (S.proj _ c j i)))
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [h3]
      exact Submodule.smul_mem _ _ h2
    · rintro _ ⟨i, rfl⟩
      exact ⟨a (κ i), f (κ i), col i, ha _, (hf _).le, by rw [hwa]; rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTestMatch
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem exists_test_match : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∀ h ∈ l.yy.ker, ∀ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) → ∃ τ : S.Test p y₀, l.Match τ := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l h1 h2 h3 h4 h5
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hmax : IsGreatest (Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (S.delta y₀) := by
    obtain ⟨x, hx⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖)
    refine ⟨⟨x, hx⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove z
  let τ : S.Test p y₀ :=
    { X := u.D.toPre.X
      q := l.q
      pos := l.pos
      yy := l.yy
      yy_onto := l.yy_onto
      isoFree := l.isoFree
      wt := l.wt
      wt_eq := l.wt_eq
      δ := S.delta y₀
      δ_max := hmax
      δ_pos := h2.1
      supp := h2.2
      tx := h1
      le := h3
      eq := h4
      unit0 := h5 }
  exact ⟨τ, AddEquiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl⟩
end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

def UnivBasis {S : Scheme.{0}} (P : PolAV S) (n : ℤ) {T₀ : Over S} {κ : Type} (b : κ → SecM P.A P.L n T₀) : Prop :=
  ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ T₀), ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
    ∀ i, c i = VVRank.pullM P.A P.L n h (b i)

theorem exists_univBasis (h : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V), UnivBasis P n b := by
  obtain ⟨V, hV, b, hb⟩ := h S P n hn p
  exact ⟨V, hV, fun i => SecM.ofSec P.A (b i), fun T _ h => VVRank.exists_basis P n b hb T h⟩

end GlobalTheory.ThetaReal
end
end

