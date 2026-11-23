module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.Pick

theorem exists_indep_of_sat {R E : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [AddCommGroup E] [Module R E]
    [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E) (F : Submodule R E)
    (hF : ∀ x, x ∈ F ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ Submodule.span R T) :
    ∃ f : Fin (Module.finrank R F) → E, (∀ j, f j ∈ T) ∧ LinearIndependent R f :=
  _root_.UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat T F hF

def valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) : X.presheaf.stalk (centre z) →+* R :=
  (Scheme.stalkClosedPointTo z).hom

theorem isLocalHom_valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) :
    IsLocalHom (valMap z) :=
  inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)

theorem inv_nat_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) :
    (m : Ω) ≠ 0 ∧ (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  have hu : IsUnit ((m : X.presheaf.stalk (centre z))) := by
    have hv : IsUnit (valMap z (m : X.presheaf.stalk (centre z))) := by
      rw [map_natCast]; exact (Nat.cast_ne_zero.2 hm.ne').isUnit
    haveI := isLocalHom_valMap z
    exact isUnit_of_map_unit (valMap z) _ hv
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have h1 : (m : Ω) * genMap ξ ⟨centre z, h⟩ g = 1 := by
    have := congrArg (genMap ξ ⟨centre z, h⟩) hg
    rwa [map_mul, map_natCast, map_one] at this
  have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨h0, ⟨g, eq_inv_of_mul_eq_one_right h1⟩⟩

theorem reg_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h'⟩ := by
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem exists_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem valAt_zero_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (hg : IsCptGen ξ) (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) {a κ : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) (hκ : κ ∈ regAt ξ ⟨centre z, h⟩) (hκi : κ⁻¹ ∈ regAt ξ ⟨centre z, h⟩) (hκ0 : κ ≠ 0)
    (hv : ValAt ξ z ((m : Ω) * a * κ) 0) : ValAt ξ z a 0 := by
  obtain ⟨ga, hga⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = a := ha
  obtain ⟨gk, hgk⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ := hκ
  obtain ⟨gi, hgi⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ⁻¹ := hκi
  obtain ⟨_, gt, hgt, hgt0⟩ := hv
  replace hgt0 : valMap z gt = 0 := hgt0
  have e1 : gt = (m : X.presheaf.stalk (centre z)) * ga * gk := by
    apply hg.inj ⟨centre z, h⟩
    rw [hgt, map_mul, map_mul, map_natCast, hga, hgk]
  have e2 : gk * gi = 1 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_mul, map_one, hgk, hgi, mul_inv_cancel₀ hκ0]
  have e3 : valMap z gk * valMap z gi = 1 := by rw [← map_mul, e2, map_one]
  have e4 : valMap z gk ≠ 0 := left_ne_zero_of_mul_eq_one e3
  have e5 : valMap z ga = 0 := by
    rw [e1, map_mul, map_mul, map_natCast] at hgt0
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    simpa [hm', e4] using hgt0
  exact ⟨h, ga, hga, e5⟩

theorem lie_val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (hg : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v v' : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : M.ValAt z e v') : v = v' := by
  obtain ⟨h₁, u, hu, hv⟩ := h
  obtain ⟨h₂, u', hu', hv'⟩ := h'
  have : u = u' := (lieLat_carrier X G Ω ξ Li M ⟨centre z, h₁⟩).2 hg inferInstance e u u' hu hu'
  subst this
  apply Over.OverMorphism.ext
  rw [hv, hv']

theorem mem_lat_of_val {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : genPt ξ ⤳ centre z) : e ∈ M.lat ⟨centre z, h'⟩ := by
  obtain ⟨_, u, hu, -⟩ := h
  exact Submodule.subset_span ⟨u, hu⟩

theorem inChart_of_coords {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {L : Type} [Field L] {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (hw : CoordsAt ξ y z w)
    (h : genPt ξ ⤳ centre z) (c₀ : (k : K) → J k) (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ ⟨centre z, h⟩ := by
  have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (hc₀ k).isUnit).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k (c₀ k) (hc₀ k).isUnit).2 (c' k)
  exact reg_of_valAt hr h

theorem exists_cls {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b₀ (i + 1)) : ∃ t : Ω, IsCls b₀ i e t := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by simpa [IsCls] using hy⟩

theorem sub_coord_mem {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E)
    (π : Fin r → Module.Dual Ω E) (hπ : ∀ j l, π j (b l) = if j = l then 1 else 0) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b (i + 1)) : e - π i e • b i ∈ flagStep Ω b i := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hker : flagStep Ω b i ≤ LinearMap.ker (π i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have h0 : π i y = 0 := hker hy
  have : y + t • b i - π i (y + t • b i) • b i = y := by
    simp [h0, hπ]
  rwa [this]

theorem pick : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ ((vf j).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (f j)).left)) ∧
        M.ValAt _ e ve ∧ (ve.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt s).left) ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ hc hall htie hm hind hsw hdeg L _ _ w z hw B MB F hsub c₀ hc₀
  have hg : IsCptGen ξ := htie.gen
  have hsub₀ : IsSubFibre M (flagStep Ω b₀ i) z MB (F.F i.castSucc) := by simpa using hsub i.castSucc
  have hsub₁ : IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB (F.F i.succ) := by simpa using hsub i.succ
  set zL := spMap (algebraMap (𝓞 L) L) ≫ z with hzL

  obtain ⟨f₀, hfT, hfi⟩ := exists_indep_of_sat _ (F.F i.castSucc) hsub₀
  have hrk : Module.finrank (𝓞 L) (F.F i.castSucc) = i := (F.rank i.castSucc).trans (by simp)
  have hrk₁ : Module.finrank (𝓞 L) (F.F i.succ) = i + 1 := (F.rank i.succ).trans (by simp)
  let f : Fin i → B.carrier := fun j => f₀ (Fin.cast hrk.symm j)
  have hfi' : LinearIndependent (𝓞 L) f := hfi.comp _ (Fin.cast_injective _)
  choose ef hef vf hv hl using fun j : Fin i => hfT (Fin.cast hrk.symm j)
  have hfF : ∀ j, f j ∈ F.F i.castSucc := fun j =>
    (hsub₀ _).2 ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span (hfT _)⟩

  obtain ⟨s, ⟨e, he, ve, hve, hsv⟩, hs0⟩ : ∃ s, (∃ e ∈ flagStep Ω b₀ (i + 1), ∃ v : epsAt zL ⟶ G,
      M.ValAt zL e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt s).left)) ∧ s ∉ F.F i.castSucc := by
    by_contra hno
    push_neg at hno
    have hle : F.F i.succ ≤ F.F i.castSucc := by
      intro x hx
      obtain ⟨c, hc₁, hcx⟩ := (hsub₁ x).1 hx
      have hsp := Submodule.span_le.2 (fun t ht => hno t ht) hcx
      exact F.sat _ c x hc₁ hsp
    have heq : F.F i.succ = F.F i.castSucc := le_antisymm hle (F.mono Fin.castSucc_lt_succ.le)
    rw [heq, hrk] at hrk₁
    omega
  have hs1 : s ∈ F.F i.succ := (hsub₁ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨e, he, ve, hve, hsv⟩⟩

  have h : genPt ξ ⤳ centre zL := hall _
  obtain ⟨b, π, κ, hb, hfr, hmb, hπb, hπm, hκ0, hκ, hκi, hcl⟩ := cls_frame X Ω ξ K J y G Li M V r b₀ m i a e₀ hind hsw hdeg
    ⟨centre zL, h⟩ c₀ (inChart_of_coords hw h c₀ hc₀)
  obtain ⟨t, ht⟩ := exists_cls b₀ i he
  have hm0 := inv_nat_reg (ξ := ξ) zL h hm
  have he_lat := mem_lat_of_val M hve h
  have hAr : π i e ∈ regAt ξ ⟨centre zL, h⟩ := by
    have := mul_mem hm0.2 (hπm i e he_lat)
    rwa [inv_mul_cancel_left₀ hm0.1] at this
  have hα : (m : Ω)⁻¹ * π i e ∈ regAt ξ ⟨centre zL, h⟩ := mul_mem hm0.2 hAr
  have htg : t / gen y a e₀ c₀ = (m : Ω) * ((m : Ω)⁻¹ * π i e) * κ := by
    rw [hcl e t he ht, mul_inv_cancel_left₀ hm0.1]
  have hreg : t / gen y a e₀ c₀ ∈ regAt ξ ⟨centre zL, h⟩ := by
    rw [hcl e t he ht]; exact mul_mem hAr hκ
  obtain ⟨u, hu⟩ := exists_valAt hreg
  refine ⟨f, fun j => ef j, s, e, t, u, fun j => vf j, ve, hfF, hfi', hs1, hs0, hef, he,
    fun j => ⟨hv j, hl j⟩, hve, hsv, ht, hu, ?_⟩

  rintro rfl
  have hv0 : ValAt ξ zL ((m : Ω)⁻¹ * π i e) 0 :=
    valAt_zero_factor hg zL h hm hα hκ hκi hκ0 (htg ▸ hu)
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G L zL
  obtain ⟨ev, hev, hevs, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ Li M L zL h ER MR hg inferInstance
  let ar : regAt ξ ⟨centre zL, h⟩ := ⟨_, hα⟩
  let xb : M.lat ⟨centre zL, h⟩ := ⟨_, hmb i⟩
  let xe : M.lat ⟨centre zL, h⟩ := ⟨e, he_lat⟩
  have h1 : ev (ar • xb) = 0 := by rw [hevs ar 0 xb hv0, zero_smul]
  have h2 : ((xe - ar • xb : M.lat ⟨centre zL, h⟩) : Li) = e - π i e • b i := by
    show e - ((m : Ω)⁻¹ * π i e) • (m : Ω) • b i = _
    have hmm : ((m : Ω)⁻¹ * π i e) * (m : Ω) = π i e := by
      have := hm0.1
      field_simp
    rw [smul_smul, hmm]
  have hval : M.ValAt zL e (MR.pt (ev xe)) := (hev e _).2 ⟨he_lat, rfl⟩
  have hveq : ve = MR.pt (ev xe) := lie_val_unique M hg hve hval
  have hval' : M.ValAt zL (e - π i e • b i) ve := by
    rw [hveq]
    refine (hev _ _).2 ⟨h2 ▸ (xe - ar • xb).2, ?_⟩
    have : (⟨e - π i e • b i, h2 ▸ (xe - ar • xb).2⟩ : M.lat ⟨centre zL, h⟩) = xe - ar • xb := Subtype.ext h2.symm
    rw [this, map_sub, h1, sub_zero]
  have hmem : e - π i e • b i ∈ flagStep Ω b₀ i := by
    rw [← hb i]
    exact sub_coord_mem b π hπb i (by rw [hb]; exact he)
  exact hs0 ((hsub₀ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨_, hmem, ve, hval', hsv⟩⟩)

end GlobalTheory.CompanionTheory.Ar.RootHt.Pick
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberSectionDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem secVal_congr {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem epsMul_snd {C : Type} [CommRing C] (c : C) (a : DualNumber C) :
    (GlobalTheory.CompanionTheory.Ar.epsMul c a).snd = c * a.snd := by
  simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem one_left_eps {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) :
    (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left = spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  simp

theorem pt_zero {S : Scheme.{0}} {G : Over S} [GrpObj G] {C : Type} [CommRing C] {y : Sp C ⟶ S} {L : Type}
    [AddCommGroup L] [Module C L] (M : LieModel G y L) : M.pt 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem one_snd {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) (W : G.left.Opens)
    (h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W) (h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W) (s : Γ(G.left, W)) :
    (secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s).snd = 0 := by
  have e := one_left_eps G y
  have h2 : ⊤ ≤ (spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left) ⁻¹ᵁ W := e ▸ h1
  rw [secVal_congr e W h1 h2 s, secring C (DualNumber C) _ G.left _ W h0 h2 s]
  exact TrivSqZeroExt.snd_inl _ _

theorem exists_linear_snd : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  intro S G _ C _ y L _ _ M W h s
  have p0 := pt_zero M
  have h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W := p0 ▸ h 0
  have h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W := by
    intro z _
    have t : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ (M.pt 0).left = (1 : Over.mk y ⟶ G).left := M.tan 0
    show (1 : Over.mk y ⟶ G).left z ∈ W
    rw [← t]
    exact h 0 (show spMap (TrivSqZeroExt.fstHom C C C).toRingHom z ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨{ toFun := fun l => (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd, map_add' := ?_, map_smul' := ?_ },
    fun l => rfl⟩
  · intro l l'
    have e : (M.pt (l + l')).left = (M.pt l * M.pt l').left := by rw [M.add]
    have hvw : ⊤ ≤ (M.pt l * M.pt l').left ⁻¹ᵁ W := e ▸ h (l + l')
    have key := _root_.GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add S G C y (M.pt l) (M.pt l') (M.tan l) (M.tan l') W (h l) (h l') hvw h1 s
    have key' := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom t) key
    simp only [map_add (f := _)] at key'
    have key'' : secVal (B := DualNumber C) (M.pt l * M.pt l').left W hvw s +
        secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s =
        secVal (B := DualNumber C) (M.pt l).left W (h l) s + secVal (B := DualNumber C) (M.pt l').left W (h l') s := key'
    have key3 := congrArg TrivSqZeroExt.snd key''
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, one_snd G y W h0 h1 s, add_zero] at key3
    show (secVal (B := DualNumber C) (M.pt (l + l')).left W (h (l + l')) s).snd = _
    rw [secVal_congr e W (h (l + l')) hvw s]
    exact key3
  · intro c l
    have e := M.smul c l
    have h2 : ⊤ ≤ (spMap (GlobalTheory.CompanionTheory.Ar.epsMul c) ≫ (M.pt l).left) ⁻¹ᵁ W := e ▸ h (c • l)
    show (secVal (B := DualNumber C) (M.pt (c • l)).left W (h (c • l)) s).snd = c • _
    rw [secVal_congr e W (h (c • l)) h2 s, secring _ _ _ G.left _ W (h l) h2 s, epsMul_snd]
    rfl

end GlobalTheory.CompanionTheory.Ar.HtPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorsPull

theorem spMap_cancel {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of Ω) ⟶ Z) (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom i)) :=
    GlobalTheory.CompanionTheory.Ar.LieEx.std_of_inj (CommRingCat.ofHom i) i.injective
  refine GlobalTheory.CompanionTheory.Ar.LieEx.epi_of_surj (Spec.map (CommRingCat.ofHom i)) ?_ a b h
  intro y
  have hs : Subsingleton (Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of Ω')) :=
    inferInstanceAs (Nonempty (PrimeSpectrum Ω'))
  exact ⟨x, Subsingleton.elim _ _⟩

theorem tr_pow {S : Scheme.{0}} {T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (n : ℕ) (u : Over.mk a ⟶ G) (hu : u ^ n = 1) :
    ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
  subst h
  exact ⟨u, rfl, hu⟩

theorem torsion_of_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ _ φ h n hf
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  let u : Over.mk (ξ' ≫ f) ⟶ Over.mk ξ := Over.homMk (spMap i) (by simpa using hd'.symm)
  let P : (Over.mk ξ' ⟶ G') →* (Over.mk (ξ' ≫ f) ⟶ G) := pushHom h (Over.mk ξ')
  let Q : (Over.mk ξ ⟶ G) →* (Over.mk (ξ' ≫ f) ⟶ G) := preHom u
  have rel : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → P a = Q c :=
    fun a c e => Over.OverMorphism.ext e
  have lerp : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), P a = Q c → a.left ≫ φ = spMap i ≫ c.left :=
    fun a c e => congrArg (fun z => z.left) e
  have Pinj : Function.Injective P := by
    intro a a' e
    have e1 : a.left ≫ φ = a'.left ≫ φ := congrArg (fun z => z.left) e
    have w : ∀ b : Over.mk ξ' ⟶ G', b.left ≫ G'.hom = ξ' := fun b => by simpa using Over.w b
    exact Over.OverMorphism.ext (h.1.hom_ext e1 ((w a).trans (w a').symm))
  have Qinj : Function.Injective Q := by
    intro c c' e
    have e1 : spMap i ≫ c.left = spMap i ≫ c'.left := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (spMap_cancel i _ _ e1)
  refine ⟨GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates X X' Ω Ω' ξ ξ' f i G G' φ n hd h hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hxw : y.left ≫ G.hom = ξ := by simpa using Over.w y
    have hw : (spMap i ≫ y.left) ≫ G.hom = ξ' ≫ f := by rw [Category.assoc, hxw, hd']
    let y' : Over.mk ξ' ⟶ G' := Over.homMk (h.1.lift (spMap i ≫ y.left) ξ' hw) (h.1.lift_snd _ _ _)
    have e : y'.left ≫ φ = spMap i ≫ y.left := h.1.lift_fst _ _ _
    refine ⟨y', Pinj ?_, e⟩
    rw [map_pow, map_one, rel y' y e, ← map_pow, hy, map_one]
  · intro y' hy'
    have hP : (P y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    obtain ⟨g, hl, hg⟩ := tr_pow hd' n (P y') hP
    obtain ⟨y, hy⟩ := hf Ω' i g hg
    have e : y'.left ≫ φ = spMap i ≫ y.left := hl.symm.trans hy
    refine ⟨y, Qinj ?_, e⟩
    rw [map_pow, map_one, ← rel y' y e, hP]
  · intro a a' c c' e e'
    apply lerp
    rw [map_mul, map_mul, rel a c e, rel a' c' e']
  · intro a a' c e e'
    exact Pinj ((rel a c e).trans (rel a' c e').symm)
  · intro a c c' e e'
    exact Qinj ((rel a c e).symm.trans (rel a c' e'))

end GlobalTheory.CompanionTheory.Ar.TorsPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.Chart

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

theorem ring_eq' {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem exists_chart_values : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hpN hc
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends X G Ω ξ E M p N J c hpN hc
  obtain ⟨_, ⟨A, hA, rfl⟩, hpA, hAx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hpx x.opensRange.isOpen
  replace hA : IsAffineOpen A := hA
  have hrange : Set.range hA.fromSpec ⊆ Set.range x := by
    rw [hA.range_fromSpec]
    exact hAx
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(X, A), spMap a ≫ x = hA.fromSpec :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x hA.fromSpec hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨EB, iEB, mEB, ⟨MB⟩⟩ := lieModel_exists X G Γ(X, A) hA.fromSpec
  have hex : ∀ i, ∃ b, MB.pt b = epsBase a ha ≫ MR.pt (e i) := fun i =>
    MB.onto _ (isTanAt_base a ha (MR.tan _))
  choose eB heB using hex
  refine ⟨A, hA, EB, iEB, mEB, MB, eB, hpA, fun t ht => hxN (hAx ht), ?_⟩
  intro y f hg hy i w hw
  let q : Cpt ξ := ⟨centre y, hg⟩
  have hqr : q.1 ∈ x.opensRange := by
    refine hrange ⟨spMap f (IsLocalRing.closedPoint ℂ), ?_⟩
    change _ = centre y
    simp only [centre, hy, Scheme.Hom.comp_apply]
    rfl
  have hqx : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo y).hom.comp ψ = f.comp a := by
    refine ring_eq' x y ψ hψ _ ?_
    have e2 : spMap (f.comp a) = spMap f ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, hy]
  let vq : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G := epsBase ψ hψ ≫ MR.pt (e i)
  refine ⟨hg, vq, hext q ψ hψ i vq rfl, ?_⟩
  rw [hw, heB]
  change spMap (dualMap f) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
    spMap (dualMap (Scheme.stalkClosedPointTo y).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
  rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]

end GlobalTheory.CompanionTheory.Ar.LocFrames.Chart
end
end

