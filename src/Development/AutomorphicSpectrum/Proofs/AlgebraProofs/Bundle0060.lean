module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatLocallyFreeAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAbelianVarietyPTorsion
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.FinFlatNorm

open TopologicalSpace GlobalTheory.FiniteAmple GlobalTheory.LB ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm
open GlobalTheory.FlatNorm (nm nm_of_isPushout isUnit_of_nm exists_preimage_le)

variable {X Y : Scheme.{0}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]

theorem exists_finFree_app_of_finitePresentation {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (π.app V).hom := by
  obtain ⟨V0, hV0, hxV0, hV0U⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hfin : (π.app V0).hom.Finite := IsFinite.finite_app π V0 hV0
  have hfl : (π.app V0).hom.Flat := by
    have := HasRingHomProperty.appLE @Flat π inferInstance ⟨V0, hV0⟩ ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hfp : (π.app V0).hom.FinitePresentation := by
    have := HasRingHomProperty.appLE @LocallyOfFinitePresentation π inferInstance ⟨V0, hV0⟩
      ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  obtain ⟨r, hr, H⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_finFree_away_of_finitePresentation hfin hfl hfp
    (hV0.primeIdealOf ⟨x, hxV0⟩)
  refine ⟨X.basicOpen r, hV0.basicOpen r, ?_, (X.basicOpen_le r).trans hV0U, ?_⟩
  · have h1 : hV0.primeIdealOf ⟨x, hxV0⟩ ∈
        (TopologicalSpace.Opens.map hV0.fromSpec.base).obj (X.basicOpen r) := by
      rw [hV0.fromSpec_preimage_basicOpen]
      exact hr
    have h2 : hV0.fromSpec (hV0.primeIdealOf ⟨x, hxV0⟩) ∈ X.basicOpen r := h1
    rwa [hV0.fromSpec_primeIdealOf] at h2
  · exact H (isPushout_app π hV0 (hV0.basicOpen r) (X.basicOpen_le r))
      (RingedSpace.isUnit_res_basicOpen _ r)

abbrev FreeOpen (V : X.Opens) : Type := {W : X.Opens // IsAffineOpen W ∧ W ≤ V ∧ FinFree (π.app W).hom}

theorem le_iSup_freeOpen (V : X.Opens) : V ≤ ⨆ W : FreeOpen π V, W.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWV, hF⟩, hxW⟩

theorem ext_freeOpen {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ W : FreeOpen π V, resG X W.2.2.1 a = resG X W.2.2.1 b) : a = b := by
  refine TopCat.Presheaf.section_ext X.sheaf V a b fun x hx => ?_
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp (le_iSup_freeOpen π V hx)
  have e := congrArg (X.presheaf.germ W.1 x hxW).hom (h W)
  simp [resG] at e
  exact e

omit [Flat π] [LocallyOfFinitePresentation π] in
theorem resG_nm {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (π.app V).hom) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (nm (π.app V).hom b) = nm (π.app W).hom (resG Y (π.preimage_mono h) b) := by
  exact (nm_of_isPushout (isPushout_app π hV hW h) hF b).symm

private theorem resG_nm_app_eq_nm_app_of_le_freeOpen {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (k : FreeOpen π V) {W' : X.Opens}
    (hW' : IsAffineOpen W') (h : W' ≤ k.1) :
    resG X h (nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) =
      nm (π.app W').hom (resG Y (π.preimage_mono (h.trans k.2.2.1)) b) := by
  rw [resG_nm π k.2.1 hW' h k.2.2.2, resG_resG]

theorem exists_normFun (V : X.Opens) (b : Γ(Y, π ⁻¹ᵁ V)) : ∃ a : Γ(X, V), ∀ W : FreeOpen π V,
    resG X W.2.2.1 a = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  refine exists_fun_of_cover (fun k : FreeOpen π V => k.1) (fun k => k.2.2.1) (le_iSup_freeOpen π V)
    (fun k => nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) fun k l => ?_
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_resG, resG_nm_app_eq_nm_app_of_le_freeOpen π b k W'.2.1, resG_nm_app_eq_nm_app_of_le_freeOpen π b l W'.2.1]

def normFun (V : X.Opens) : Γ(Y, π ⁻¹ᵁ V) →* Γ(X, V) where
  toFun b := (exists_normFun π V b).choose
  map_one' := ext_freeOpen π fun W => by
    rw [(exists_normFun π V 1).choose_spec W, map_one, map_one, map_one]
  map_mul' a b := ext_freeOpen π fun W => by
    rw [(exists_normFun π V _).choose_spec W, map_mul, map_mul, map_mul,
      (exists_normFun π V a).choose_spec W, (exists_normFun π V b).choose_spec W]

theorem resG_normFun_free {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (W : FreeOpen π V) :
    resG X W.2.2.1 (normFun π V b) = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  exact (exists_normFun π V b).choose_spec W

theorem resG_normFun {V W : X.Opens} (h : W ≤ V) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (normFun π V b) = normFun π W (resG Y (π.preimage_mono h) b) := by
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_normFun_free π b ⟨W'.1, W'.2.1, W'.2.2.1.trans h, W'.2.2.2⟩,
    resG_normFun_free π _ W', resG_resG]

private theorem basicOpen_resG_eq_inf_basicOpen {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U)) :
    Z.basicOpen (resG Z h f) = V ⊓ Z.basicOpen f :=
  Z.basicOpen_res f (homOfLE h).op

private theorem isUnit_resG_of_le_basicOpen' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U))
    (hV : V ≤ Z.basicOpen f) : IsUnit (resG Z h f) := by
  rw [← resG_resG (Z.basicOpen_le f) hV f]
  exact (RingedSpace.isUnit_res_basicOpen _ f).map (resG Z hV)

theorem mem_basicOpen_normFun {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (normFun π V b) ↔ ∀ y, π y = x → y ∈ Y.basicOpen b := by
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  have e0 := resG_normFun_free π b ⟨W, hW, hWV, hF⟩
  have key : x ∈ X.basicOpen (normFun π V b) ↔
      x ∈ X.basicOpen (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b)) := by
    rw [← e0, basicOpen_resG_eq_inf_basicOpen]
    exact ⟨fun h => ⟨hxW, h⟩, fun h => h.2⟩
  rw [key]
  constructor
  · intro hx' y hy
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ := exists_finFree_app_of_finitePresentation π hx'
    have hW''W : W'' ≤ W := hle.trans (X.basicOpen_le _)
    have hu := isUnit_resG_of_le_basicOpen' hW''W _ hle
    rw [resG_nm π hW hW'' hW''W hF, resG_resG] at hu
    have hu' := isUnit_of_nm hF'' hu
    have hy'' : y ∈ Y.basicOpen (resG Y (π.preimage_mono (hW''W.trans hWV)) b) := by
      rw [Y.basicOpen_of_isUnit hu']
      show π y ∈ W''
      rw [hy]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at hy''
    exact hy''.2
  · intro hall
    have hall' : ∀ y, π y = x → y ∈ Y.basicOpen (resG Y (π.preimage_mono hWV) b) := by
      intro y hy
      rw [basicOpen_resG_eq_inf_basicOpen]
      refine ⟨?_, hall y hy⟩
      show π y ∈ W
      rw [hy]
      exact hxW
    obtain ⟨V', hxV', hV'⟩ := exists_preimage_le π hall'
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ :=
      exists_finFree_app_of_finitePresentation π (U := W ⊓ V') ⟨hxW, hxV'⟩
    have hW''W : W'' ≤ W := hle.trans inf_le_left
    have hu := isUnit_resG_of_le_basicOpen' (π.preimage_mono hW''W) (resG Y (π.preimage_mono hWV) b)
      ((π.preimage_mono (hle.trans inf_le_right)).trans hV')
    have hu2 := hu.map (nm (π.app W'').hom)
    rw [← resG_nm π hW hW'' hW''W hF] at hu2
    have h3 : x ∈ X.basicOpen (resG X hW''W (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b))) := by
      rw [X.basicOpen_of_isUnit hu2]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at h3
    exact h3.2

end GlobalTheory.CompanionTheory.FinFlatNorm


open GlobalTheory.CompanionTheory.FinFlatNorm in
theorem GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  intro X Y q h1 h2 h3
  exact ⟨normFun q, fun V W h a => resG_normFun q h a, fun V a y hy => mem_basicOpen_normFun q a hy⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitAffineNeighbourhood
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

theorem mem_orbit_iff {x y : X.left} : y ∈ orbit G X x ↔
    ∃ z, (snd G X).left z = x ∧ (γ[G, X] : G ⊗ X ⟶ X).left z = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem orbit_symm {x y : X.left} (h : y ∈ orbit G X x) : x ∈ orbit G X y := by
  obtain ⟨σ, -, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd G X
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  refine (mem_orbit_iff G X).2 ⟨σ.left z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h2]

theorem orbit_hom {x y : X.left} (h : y ∈ orbit G X x) : X.hom y = X.hom x := by
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  have e : (γ[G, X] : G ⊗ X ⟶ X).left ≫ X.hom = (snd G X).left ≫ X.hom := (Over.w _).trans (Over.w _).symm
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]

theorem stable_of_forall (V : X.left.Opens) (h : ∀ y ∈ V, orbit G X y ⊆ V) :
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  ext z
  constructor
  · intro hz
    exact h _ hz (orbit_symm G X ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩))
  · intro hz
    exact h _ hz ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩)

variable {G X} in
theorem isFinite_snd (hG : IsFiniteLocallyFree G.hom) : IsFinite (snd G X).left := by
  have := hG.1
  have h : IsFinite (pullback.snd G.hom X.hom) := inferInstance
  exact h

variable {G X} in
theorem orbit_finite (hG : IsFiniteLocallyFree G.hom) (x : X.left) : (orbit G X x).Finite := by
  have := isFinite_snd (X := X) hG
  exact ((snd G X).left.finite_preimage_singleton x).image _

variable {G X} in
theorem isOpen_saturated (hG : IsFiniteLocallyFree G.hom) (O : X.left.Opens) :
    IsOpen {y : X.left | orbit G X y ⊆ O} := by
  have := isFinite_snd (X := X) hG
  have hc : IsClosed ((snd G X).left '' ((γ[G, X] : G ⊗ X ⟶ X).left ⁻¹' (O : Set X.left)ᶜ)) :=
    (snd G X).left.isClosedMap _ (O.isOpen.isClosed_compl.preimage (γ[G, X] : G ⊗ X ⟶ X).left.continuous)
  convert hc.isOpen_compl using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]
  constructor
  · intro h z hz hy
    exact hz (h ((mem_orbit_iff G X).2 ⟨z, hy, rfl⟩))
  · intro h w hw
    obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
    by_contra hn
    exact h z hn hz

theorem mem_basicOpen_appLE' {P Y : Scheme.{0}} (c : P ⟶ Y) (U : Y.Opens) (hc : ⊤ ≤ c ⁻¹ᵁ U) (f : Γ(Y, U)) (z : P) :
    z ∈ P.basicOpen ((c.appLE U ⊤ hc).hom f) ↔ c z ∈ Y.basicOpen f := by
  have key : P.basicOpen ((c.appLE U ⊤ hc).hom f) = c ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  rw [key]
  rfl

theorem exists_norm {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D)
    (hv : FiniteFreeHom v.appTop.hom) (e : Γ(P, ⊤)) :
    ∃ N : Γ(D, ⊤), ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  letI := v.appTop.hom.toAlgebra
  have h1 : Module.Free Γ(D, ⊤) Γ(P, ⊤) := hv.1
  have h2 : Module.Finite Γ(D, ⊤) Γ(P, ⊤) := hv.2
  refine ⟨Algebra.norm Γ(D, ⊤) e, _root_.GlobalTheory.CompanionTheory.PrimesToPts.primes_to_pts v _ e fun p => ?_⟩
  rw [GlobalTheory.T.norm_not_mem_prime_iff e p.asIdeal p.isPrime]
  constructor
  · intro h q hq
    exact h q.asIdeal q.isPrime hq
  · intro h q hq hq'
    exact h ⟨q, hq⟩ hq'

theorem exists_stable_affine_nbhd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → ∀ (x : X.left) (U : X.left.Opens), IsAffineOpen U → orbit G X x ⊆ U → ∃ (V : X.left.Opens) (W : S.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ V ≤ X.hom ⁻¹ᵁ W ∧ (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  intro S G X _ _ hG x U hU hxU
  have hfl := hG.1
  have hfl2 := hG.2.1
  have hfl3 := hG.2.2
  obtain ⟨W, hsW, hW, hfree⟩ := _root_.GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_affine_finiteFreeHom G.hom (X.hom x)
  have htrans : ∀ {y w : X.left}, y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x :=
    fun {y w} => _root_.GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans G X x y w
  let O : X.left.Opens := U ⊓ X.hom ⁻¹ᵁ W
  have hxO : orbit G X x ⊆ O := fun y hy => ⟨hxU hy, by
    show X.hom y ∈ W
    rw [orbit_hom G X hy]; exact hsW⟩
  let V₀ : X.left.Opens := ⟨{y | orbit G X y ⊆ O}, isOpen_saturated hG O⟩
  have hV₀O : V₀ ≤ O := fun y hy => hy (_root_.GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self G X y)
  have hV₀U : V₀ ≤ U := hV₀O.trans inf_le_left
  have hxV₀ : orbit G X x ⊆ V₀ := fun y hy w hw => hxO (htrans hy hw)
  obtain ⟨f, hKf, hfV⟩ := GlobalTheory.T.finite_set_basic_open_affine U V₀ hU hV₀U _ (orbit_finite hG x) hxV₀
  let D : X.left.Opens := X.left.basicOpen f
  have hD : IsAffineOpen D := hU.basicOpen f
  have hDW : D ≤ X.hom ⁻¹ᵁ W := (hfV.trans hV₀O).trans inf_le_right
  have hsq : IsPullback (fst G X).left (snd G X).left G.hom X.hom :=
    IsPullback.of_hasPullback G.hom X.hom
  obtain ⟨h, u, hpb⟩ := _root_.GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens hsq W D hDW
  have := isFinite_snd (X := X) hG
  haveI : IsAffine D.toScheme := hD
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (G.hom ⁻¹ᵁ W).toScheme := hW.preimage G.hom
  haveI : IsAffine ((snd G X).left ⁻¹ᵁ D).toScheme := hD.preimage (snd G X).left
  have hfree' := _root_.GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback hpb hfree
  let P' : (G ⊗ X).left.Opens := (snd G X).left ⁻¹ᵁ D
  let c : P'.toScheme ⟶ X.left := P'.ι ≫ (γ[G, X] : G ⊗ X ⟶ X).left
  have hc : ⊤ ≤ c ⁻¹ᵁ U := by
    rintro z -
    have hz : (snd G X).left z.1 ∈ D := z.2
    have h1 : (γ[G, X] : G ⊗ X ⟶ X).left z.1 ∈ orbit G X ((snd G X).left z.1) :=
      (mem_orbit_iff G X).2 ⟨z.1, rfl, rfl⟩
    exact (hfV hz h1).1
  obtain ⟨N, hN⟩ := exists_norm ((snd G X).left ∣_ D) hfree' ((c.appLE U ⊤ hc).hom f)
  let V : X.left.Opens := D.ι ''ᵁ (D.toScheme.basicOpen N)
  have hVmem : ∀ y, y ∈ V ↔ y ∈ D ∧ orbit G X y ⊆ D := by
    intro y
    show y ∈ D.ι '' (D.toScheme.basicOpen N : Set D.toScheme) ↔ _
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, fun w hw => ?_⟩
      obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
      have hzP : z ∈ P' := by
        show (snd G X).left z ∈ D
        rw [hz]; exact y'.2
      have h1 := (hN y').1 hy' ⟨z, hzP⟩ (Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz))
      exact (mem_basicOpen_appLE' c U hc f _).1 h1
    · rintro ⟨hyD, ho⟩
      refine ⟨⟨y, hyD⟩, (hN ⟨y, hyD⟩).2 fun z hz => ?_, rfl⟩
      refine (mem_basicOpen_appLE' c U hc f _).2 ?_
      have h2 : (snd G X).left z.1 = y :=
        (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)
      exact ho ((mem_orbit_iff G X).2 ⟨z.1, h2, rfl⟩)
  refine ⟨V, W, (hVmem x).2 ⟨hKf (_root_.GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self G X x), fun y hy => hKf hy⟩, ?_, hW, ?_, ?_⟩
  · exact ((isAffineOpen_top D.toScheme).basicOpen N).image_of_isOpenImmersion D.ι
  · exact fun y hy => hDW ((hVmem y).1 hy).1
  · refine stable_of_forall G X V fun y hy w hw => (hVmem w).2 ⟨((hVmem y).1 hy).2 hw, fun t ht => ?_⟩
    exact ((hVmem y).1 hy).2 (_root_.GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans G X y w t hw ht)

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAbelianVarietyPTorsionStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_abelian_variety_p_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (z : sp (R₀ := R) R ⟶ P.A), P.g = 1 ∧ z ^ p = 1 ∧ ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point | exact GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point <;> assumption)
end

