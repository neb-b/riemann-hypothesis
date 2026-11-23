module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullO1SectionCoordinatesPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemNormalLevelModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
section
noncomputable section

namespace GlobalTheory.BalRank

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def balBil : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β β' h k a y z
    simp only [LinearMap.add_apply, h a y z, k a y z]
  zero_mem' := by simp
  smul_mem' := by
    rintro n β h a y z
    simp only [LinearMap.smul_apply, h a y z]

variable {bar X}

end GlobalTheory.BalRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfForallRingEquivFixedOfIsAlgClosedAl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K,
      (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  intro K _ _ k₀ hk₀ x hfix
  by_contra hx
  have htr : Transcendental k₀ x := by
    intro halg
    have hint : IsIntegral k₀ x := halg.isIntegral
    have hdeg : (minpoly k₀ x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
    obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one k₀ x hdeg
    apply hx
    rw [← hr]
    exact r.2
  obtain ⟨σ, hσk, hσx⟩ := GlobalTheory.FixedRoots.exists_ringEquiv_add_one k₀ x htr
  have h := hfix σ hσk
  rw [hσx] at h
  simp at h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegMinTop

theorem lemProper : ∀ (R o' : Type) [CommRing R] [IsNoetherianRing R] [CommRing o'] (β : R →+* o') (S' X Z : Scheme.{0}) (s' : S' ⟶ Sp o') (z : Z ⟶ Sp R) (π : S' ⟶ Z) (i : X ⟶ Z) (U : S'.Opens) (c : U.toScheme ⟶ X), IsProjOver s' → β.Finite → IsProjOver z → Surjective c → U.ι ≫ π = c ≫ i → Dense (Set.range i) → π ≫ z = s' ≫ spMap β → Surjective π ∧ IsProper π ∧ AlgebraicGeometry.IsNoetherian Z := by
  intro R o' _ _ _ β S' X Z s' z π i U c hs' hβ hz hc hUπ hi hπz
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hs'
  have := GlobalTheory.ProperFamily.isProper_of_isProjOver hz
  haveI : IsFinite (spMap β) := (IsFinite.SpecMap_iff _).2 hβ
  haveI : IsProper (π ≫ z) := by rw [hπz]; infer_instance
  haveI : IsProper π := IsProper.of_comp π z
  refine ⟨⟨?_⟩, inferInstance, ?_⟩
  · have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hsub : Set.range i ⊆ Set.range π := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := c.surjective x
      exact ⟨U.ι u, by rw [← Scheme.Hom.comp_apply, hUπ, Scheme.Hom.comp_apply]⟩
    have h := hi.closure_eq ▸ closure_minimal hsub hcl
    exact fun y => h (Set.mem_univ y)
  · have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace z
    exact {}

theorem lemGen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens) [Nonempty U], ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt ∧ Set.range x = {genericPoint U.toScheme} := by
  intro o Ω _ _ _ M U _
  obtain ⟨⟨y₀, hy₀⟩⟩ := ‹Nonempty U›
  have hsub : Set.range M.pt ⊆ Set.range U.ι := by
    rw [M.gen, Scheme.Opens.range_ι, Set.singleton_subset_iff]
    exact (genericPoint_specializes y₀).mem_open U.isOpen hy₀
  have hg : U.ι (genericPoint U.toScheme) = genericPoint M.Z := by
    have h1 := (genericPoint_spec U.toScheme).image U.ι.continuous
    rw [Set.image_univ, Scheme.Opens.range_ι, (U.isOpen.dense ⟨y₀, hy₀⟩).closure_eq] at h1
    exact h1.eq (genericPoint_spec M.Z)
  set x := IsOpenImmersion.lift U.ι M.pt hsub with hx
  have hxU : x ≫ U.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxa : ∀ a, x a = genericPoint U.toScheme := fun a => by
    apply U.ι.isOpenEmbedding.injective
    rw [hg, ← M.pt_apply a, ← hxU, Scheme.Hom.comp_apply]
  refine ⟨x, hxU, Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint Ω, hxa _⟩, ?_⟩⟩
  rintro _ ⟨a, rfl⟩
  exact hxa a

theorem minSt5 : GlobalTheory.SiegJoin.MinSt5 := by
  intro g hg n hn ho F
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hℓo : Odd ℓ := Odd.of_dvd_nat ho hℓn
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨hXi, hXn, -⟩ := _root_.GlobalTheory.SiegelIntegral.integral_normal_noetherian g n hg hn ho F
  obtain ⟨P, rig, hPg, hPs, hrig, -⟩ := GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli g n hg hn ho F W hW
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.SiegThQF.finite_fibres ℓ hℓ hℓo g
  have hmo : Odd (ℓ ^ (j₀ + 1)) := hℓo.pow
  have hm3 : 3 ≤ ℓ ^ (j₀ + 1) := by
    have h2 := hℓ.two_le
    have h1 : ℓ ≤ ℓ ^ (j₀ + 1) := Nat.le_self_pow (by omega) ℓ
    obtain ⟨k, hk⟩ := hℓo
    omega
  have hmu : IsUnit ((ℓ ^ (j₀ + 1) : ℕ) : cycAway n) := by
    obtain ⟨k, hk⟩ := hℓn
    have hu := isUnit_natCast (n := n) (by omega)
    have e : ((n : ℕ) : cycAway n) = (ℓ : cycAway n) * (k : cycAway n) := by
      rw [← Nat.cast_mul, ← hk]
    rw [e] at hu
    rw [Nat.cast_pow]
    exact (isUnit_of_mul_isUnit_left hu).pow _
  obtain ⟨N, f, hf⟩ := _root_.GlobalTheory.SiegTh.exists_thAt g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) hPg hPs hrig hmo hm3 hmu
  have hq : QFin f := hj₀ (j₀ + 1) (by omega) n hg hn ho F W hW hℓn P rig N f hf
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hf.2.2.2.2.2.2.2.1
  have hlft : LocallyOfFiniteType F.s := GlobalTheory.SiegUnram.locallyOfFiniteType_of_isQProjOver F.qproj
  have hqc : QuasiCompact F.s := GlobalTheory.SiegelFamilyBaseChange.quasiCompact_of_isQProjOver F.qproj
  obtain ⟨Z, p, i, hpf, hio, hip, hZn, hZi, hid⟩ :=
    _root_.GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin (cycAway n) N F.X F.s f hXi hXn hlft hqc F.isSeparated hfs hq
  obtain ⟨hzproj, hOZlb, hOZamp, -⟩ := _root_.GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB (cycAway n) N 8 Z p (by norm_num) hpf
  obtain ⟨o, Ω, _, _, _, _, β, S, ρ, u, Y, q, hsys, hlev, hbig, hfin⟩ :=
    _root_.GlobalTheory.SiegLevSys.exists_sys_levModel ℓ hℓ hℓo j₀ g n hg hn ho F W hW hℓn (hbas g)
  obtain ⟨X, M, U₀, EE, fM, Xab, Zh, hmin, hab, habeq⟩ := _root_.GlobalTheory.SiegJoin.minor_model o Ω S ρ hbig hfin
  have hXnm : X.IsNm S.th := hmin.1
  have hXnorm : Geo.Tor.IsNormalScheme X.Z := hmin.2.2.1
  have hover : S.Over₀ M U₀ := hmin.2.2.2.1
  obtain ⟨d, hd, hdo⟩ :=
    _root_.GlobalTheory.SiegOpen.level_openImmersion g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys hq Y X q hlev hXnm hXnorm
  obtain ⟨U, c, hUc, -⟩ :=
    _root_.GlobalTheory.OpenLev.exists_open_finite g n hg hn ho F W hW o Ω β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin habeq hd hdo
  obtain ⟨G, _, e, _, hGs, hGsm, hGpb, hGh⟩ :=
    _root_.GlobalTheory.SiegFactor.firstFactor g n hg hn ho F W hW o Ω β S ρ u hsys M U₀ EE Zh U c hover hUc
  obtain ⟨eS, hSymE, hcrd⟩ := _root_.GlobalTheory.SiegTh.exists_symE_pCrd g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys
  have hMn : Geo.Tor.IsNormalScheme M.Z := hover.normal
  have hscale := _root_.GlobalTheory.SiegTh.sameScale_theta_symE g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf o Ω β S ρ u hsys M eS hMn
    hover.div hSymE
  have hediv : M.HasDiv eS := fun z' => by
    obtain ⟨i', hi'⟩ := hover.div z'
    obtain ⟨j', hj', -⟩ := hscale z' i' hi'
    exact ⟨j', hj'⟩
  obtain ⟨h, hhs, hhc⟩ := _root_.GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv o Ω (cycAway n) β M N eS hediv
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  obtain ⟨δ, t, hδ, htop, -, hsec⟩ := GlobalTheory.TupleBundle.exists_lb_of_hasDiv o Ω M S.Gam S.th hover.div
  have hhb := _root_.GlobalTheory.SiegTh.PullO1.lbIso_pull_O1_lbPow o Ω (cycAway n) M S.Gam S.th δ t N (N + 1).factorial eS h hδ htop hsec hhc hscale
  have hSg : S.g = 8 * g := hsys.2.2.1
  have hkey := _root_.GlobalTheory.KeyZh.key_zh o Ω S ρ M U₀ EE Zh (by omega) hover hab δ t hδ htop hsec
  haveI : Nonempty U := ⟨⟨_, hUc.1.some_mem⟩⟩
  obtain ⟨x, hxU, hxg⟩ := lemGen o Ω M U
  have hUh : U.ι ≫ h = c ≫ f := _root_.GlobalTheory.SiegCrd.eq_of_generic_pCrd (cycAway n) N U.toScheme (c ≫ F.s) (U.ι ≫ h) (c ≫ f) Ω x eS
    (by rw [Category.assoc, hhs, hUc.2.2.2.1]) (by rw [Category.assoc, hfs]) hxg
    (by rw [← Category.assoc, hxU]; exact hhc)
    (by rw [← Category.assoc, hUc.2.2.2.2 x hxU, Category.assoc]; exact hcrd _ rfl)
  haveI : Surjective c := hUc.2.2.1
  have hUd : Dense (U : Set M.Z) := U.isOpen.dense hUc.1
  obtain ⟨π, hπU, hπp⟩ := _root_.GlobalTheory.NormalFiniteLift.exists_lift_of_finite (cycAway n) N M.Z F.X Z U c i p h inferInstance hMn hZi hUd
    inferInstance hpf hio hid (by rw [hUh, hip])
  have hss : π ≫ p ≫ PSpace.str (cycAway n) N = M.s ≫ spMap β := by rw [← Category.assoc, hπp, hhs]
  obtain ⟨hπs, hπpr, hZno⟩ := lemProper (cycAway n) o β M.Z F.X Z M.s (p ≫ PSpace.str (cycAway n) N) π i U c
    hover.proj hsys.1 hzproj hUc.2.2.1 hπU hid hss
  have hTI : GlobalTheory.Poinc.ThetaInt F W i := by
    have h0 := _root_.GlobalTheory.SiegTh.ThIntAll.thetaInt_all g n hg hn ho F W hW P rig (ℓ ^ (j₀ + 1)) N f hf
    rw [← hip] at h0
    intro o' Ω' _ _ _ _ S' ρ' u' hsh hgen M' π' hM' hpt
    exact h0 o' Ω' S' ρ' u' hsh hgen M' (π' ≫ p) hM' (by rw [← Category.assoc, hpt]; simp only [Category.assoc])
  have hiz : i ≫ p ≫ PSpace.str (cycAway n) N = F.s := by rw [← Category.assoc, hip, hfs]

  haveI : IsSeparated G.hom := hGs.separated
  haveI : IsSeparated Zh.G.hom := Zh.semi.separated
  haveI := hGsm
  haveI := Zh.dim
  have hH2 : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det
  have hH1 : (hodge Zh.G S.g).IsLB := (GlobalTheory.LieVB.isVB_omega Zh.G S.g).isLB_det
  have hO := GlobalTheory.ProjSpace.O1_isLB (cycAway n) N
  have hLB : LBIso ((lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8).pull π)
      (lbPow (hodge G g) (32 * (N + 1).factorial)) := by
    have e1 := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hO h) (isLB_lbPow hδ _)).2 hhb
    have e2 := (GlobalTheory.CechPic.cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hH1 4)).2 hkey
    have e3 := (GlobalTheory.CechPic.cls_eq_iff hH1 (isLB_lbPow hH2 8)).2 hGh
    rw [GlobalTheory.CechPic.cls_pull hO, GlobalTheory.CechPic.cls_lbPow hδ] at e1
    rw [GlobalTheory.CechPic.cls_lbPow hδ, GlobalTheory.CechPic.cls_lbPow hH1] at e2
    rw [GlobalTheory.CechPic.cls_lbPow hH2] at e3
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hOZlb π) (isLB_lbPow hH2 _)).1 ?_
    rw [GlobalTheory.CechPic.cls_pull hOZlb, GlobalTheory.CechPic.cls_lbPow (pull_isLB hO p), GlobalTheory.CechPic.cls_pull hO,
      GlobalTheory.CechPic.cls_lbPow hH2, map_nsmul, ← GlobalTheory.CechPic.pull_comp, hπp, e1, smul_comm 8, e2, e3, smul_smul,
      smul_smul]
    congr 1
    ring
  refine ⟨Z, p ≫ PSpace.str (cycAway n) N, i, lbPow ((GlobalTheory.ProjSpace.O1 (cycAway n) N).pull p) 8, o, inferInstance, β,
    M.Z, M.s, U, c, π, G, inferInstance, e, inferInstance, 32 * (N + 1).factorial,
    ⟨⟨hzproj, GlobalTheory.IsNormalScheme.of_pred hZn, hio, hiz, hid, W, hW, hTI⟩, hzproj, GlobalTheory.IsNormalScheme.of_pred hZn,
      hiz, hid, hOZlb, hOZamp⟩,
    ⟨hsys.1, hsys.2.1, hover.proj, GlobalTheory.IsNormalScheme.of_pred hMn, hUd, hUc.2.1, hUc.2.2.1, hπU, hss, hπs, hπpr, hZno⟩,
    ⟨hGs, hGsm, hGpb⟩, by have := Nat.factorial_pos (N + 1); omega, hLB⟩

end GlobalTheory.SiegMinTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.RankZero

theorem nonempty_moduli : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H), D.p + D.q = 0 → Nonempty (Moduli D l) :=
  fun H D l hD => (GlobalTheory.Models.RankZero.main _ H D hD).1.map fun X => X l

end GlobalTheory.UCanon.RankZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_comp_idPow {S : Scheme.{0}} {B Y : Over S} [GrpObj B] (b : Y ⟶ B) (n : ℕ) :
    b ≫ (𝟙 B) ^ n = b ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem zClsDiag_nsmul_evc {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B]
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hs : IsDual B A (swap Q)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    n • evc hQ a b = evc hQ a (b ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ← evc_swap hQ hs.isLB, hs.additive.evc_one hs.isLB]
  | succ n ih =>
    rw [succ_nsmul, ih, pow_succ, ← evc_swap hQ hs.isLB (b ^ n * b), (isAdditive_iff hs.isLB).1 hs.additive,
      evc_swap hQ hs.isLB, evc_swap hQ hs.isLB]

theorem zClsDiag_key {h M d : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
    {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (c.A ⊗ B).left} {la : c.A ⟶ B} {mu : B ⟶ c.A}
    (hZ : ZData c d B Q la mu) {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B) :
    d • pull (lift a b).left (cls Q hZ.2.1.isLB) = pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := by
  have hQ := hZ.2.1.isLB
  have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  show d • evc hQ a b = _
  rw [e, pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hZ.2.2.2.2.2.2.1, zClsDiag_comp_idPow,
    zClsDiag_nsmul_evc hQ hZ.2.2.1]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_sum_sig {M : Type*} [AddCommMonoid M] (F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → M) :
    ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) = ∑ s, ∑ t, F s t := by
  let e : Fin 8 ≃ Fin 4 ⊕ Fin 4 := Equiv.ofBijective sig (by decide)
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun k _ => Equiv.sum_comp e (F (sig k))).trans (Equiv.sum_comp e fun s => ∑ t, F s t)

theorem nsmul_pull_diag_zCls : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ _
  let F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Pic (Zob c.A B).left := fun s u =>
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 s u •
      pull (lift (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) s)
        (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) u)).left (cls c.P c.isLB)
  rw [show (∑ kl : Fin 8 × Fin 8, zW d kl.1 kl.2 • pull (lift (zpr c.A B mu kl.1) (zpr c.A B mu kl.2)).left
      (cls c.P c.isLB)) = ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) from rfl, zClsDiag_sum_sig]
  simp only [F, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp]
  have hk : ∀ {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B), d • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun a b => zClsDiag_key c hZ a b
  have hk' : ∀ {Y : Over S} (z : ℤ) (a : Y ⟶ c.A) (b : Y ⟶ B), d • z • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      z • pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun z a b => by rw [smul_comm, hk]
  simp only [smul_add, Finset.smul_sum, hk, hk', Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
    zero_add, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, one_smul, Finset.sum_add_distrib, mul_smul, two_smul, natCast_zsmul]
  abel

end GlobalTheory.ZarhinFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapUniqueOfNilpotentNilradical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ObjMapUnique

theorem objMap_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f : S' ⟶ S}
    (m₁ m₂ : ObjMap o' o f) : m₁.toSABMap.φ = m₂.toSABMap.φ :=
  GlobalTheory.obj_rigid_any_base GlobalTheory.lawsAndExpansions.1.1 E H D l B B' b b' S S' s s' o o' f m₁.toSABMap m₂.toSABMap
    fun a ↦ ⟨_, m₁.eta a, m₂.eta a⟩

theorem objMap_unique_of_nilpotent_nilradical :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ {S : Scheme.{0}} (s' : Sp A ⟶ Sp (KA l)) (s : S ⟶ Sp (KA l)) (o' : Obj D l (baseKA l) s') (o : Obj D l (baseKA l) s) (f : Sp A ⟶ S) (m₁ m₂ : ObjMap o' o f), m₁.toSABMap.φ = m₂.toSABMap.φ := by
  intro E _ _ _ H D l A _ _ S s' s o' o f m₁ m₂
  exact objMap_unique m₁ m₂

end GlobalTheory.ObjMapUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDefinedOverSubfieldOfIsIntegralHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefOverIntegral

theorem mem_of_isIntegral {K : Type} [Field K] (k₀ : Subfield K) (hk : IsAlgClosed k₀) {x : K}
    (hx : IsIntegral k₀ x) : x ∈ k₀ := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k₀)
    (K := integralClosure k₀ K)).2 ⟨x, hx⟩
  have h1 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = x := congrArg Subtype.val ha
  have h2 : ((algebraMap k₀ (integralClosure k₀ K) a : integralClosure k₀ K) : K) = (a : K) := rfl
  rw [← h1, h2]
  exact a.2

theorem defOver_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K]
    (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  intro X Y f _ K _ k₀ hk P ⟨Q₀, hQ⟩
  let g := pullback.snd f Q₀
  let Pt : Sp K ⟶ pullback f Q₀ := pullback.lift P (spMap k₀.subtype) hQ.symm
  haveI : IsAffine (pullback f Q₀) := isAffine_of_isAffineHom g
  have hint : (g.app ⊤).hom.IsIntegral := g.isIntegral_app ⊤ (isAffineOpen_top _)
  let φc : Γ(pullback f Q₀, ⊤) ⟶ CommRingCat.of K := Pt.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hPt : Pt = Spec.map φc ≫ (pullback f Q₀).isoSpec.inv := by
    have h := Scheme.isoSpec_inv_naturality Pt
    rw [Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg : Pt ≫ g = spMap k₀.subtype := pullback.lift_snd _ _ _
  have hcomp : g.appTop ≫ φc = (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom ≫ CommRingCat.ofHom k₀.subtype := by
    have h := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at h
    simp only [φc, ← Category.assoc, h]
    exact Scheme.ΓSpecIso_naturality _
  have hmem : ∀ r, φc.hom r ∈ k₀ := by
    intro r
    obtain ⟨p, hpm, hp⟩ := hint r
    refine mem_of_isIntegral k₀ hk ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap k₀ K).comp (Scheme.ΓSpecIso (CommRingCat.of k₀)).hom.hom = φc.hom.comp (g.app ⊤).hom := by
      have := congrArg CommRingCat.Hom.hom hcomp
      exact this.symm
    rw [e]
    have h3 := Polynomial.hom_eval₂ p (g.app ⊤).hom φc.hom r
    rw [hp] at h3
    exact h3.symm.trans (RingHom.map_zero _)
  let φ₀ : Γ(pullback f Q₀, ⊤) →+* k₀ := φc.hom.codRestrict k₀ hmem
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ (pullback f Q₀).isoSpec.inv ≫ pullback.fst f Q₀, ?_⟩
  have e2 : spMap k₀.subtype ≫ Spec.map (CommRingCat.ofHom φ₀) = Spec.map φc := by
    rw [spMap, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, e2, ← Category.assoc, ← hPt]
  exact pullback.lift_fst _ _ _

end GlobalTheory.DefOverIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem quasiFinite_of_tautB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hS k _ m e C hC ξ hξ
  obtain ⟨⟨_, _, _, _, ⟨_, _, hft⟩, _⟩, ⟨n, s, ε, τ₀, h1, h2, h3, h4, hP⟩⟩ := hC
  have hb : ξ ≫ π ≫ zs = spMap C.b := by
    refine GlobalTheory.ChartQF.eq_spMap_of_injective (algebraMap _ (FractionRing (ChartRing k m e)))
      (IsFractionRing.injective _ _) _ _ ?_
    have e1 : i ≫ zs = pullback.snd _ _ := hU.1.2.2.2.2.1
    have e2 : j ≫ π = i := hU.2.2.2.2.1.2.2.2.2.1
    show jK _ ≫ _ = jK _ ≫ _
    rw [← Category.assoc, ← hξ, Category.assoc, reassoc_of% e2, e1, C.y_over]
  exact GlobalTheory.ChartQF.quasiFinite_of_pointRigid ξ (π ≫ zs) C.b hb hft fun K _ _ ev k₀ hk hemb hq hd =>
    hP K ev k₀ hk hemb (hS _ C (GlobalTheory.ChartQF.base_chartRing C.toFam) ξ hξ n s ε τ₀ h1 h2 h3 h4 K ev k₀ hk hq hd)

end GlobalTheory.UCanon
end

