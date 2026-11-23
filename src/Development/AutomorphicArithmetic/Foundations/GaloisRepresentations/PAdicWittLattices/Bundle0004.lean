module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHTrace
section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.G3.HeckeTraceSheaves

section Two
variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}

private theorem omegaPullS_app_toOm {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    (omegaPullS hg j).app U (toOm s j U x) = toOm s' j (g ⁻¹ᵁ U) (formPullS hg U j x) :=
  omegaPullS_toOmega hg j U x

private theorem formRes_formPullS_eq {X Y' : Scheme.{0}} {s : X ⟶ Sp k} {r' : Y' ⟶ Sp k'} {u v : Y' ⟶ X}
    (w : u = v) (hu : u ≫ s = r' ≫ spMap φ) (hv : v ≫ s = r' ≫ spMap φ) (U : X.Opens)
    (hle : v ⁻¹ᵁ U ≤ u ⁻¹ᵁ U) (j : ℕ) (x : OmU s U j) :
    formRes r' hle j (formPullS hu U j x) = formPullS hv U j x := by
  subst w
  have h := formRes_refl r' (u ⁻¹ᵁ U) (formPullS hu U j x)
  rw [h]

end Two

section Sheaf

variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}
  {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
  {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'} {e : Y' ⟶ Y} {f : Y ⟶ X} {f' : Y' ⟶ X'}

private def mid (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) :
    (Scheme.Modules.pushforward f).obj (Omega r a) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj (Omega r' a)) :=
  (Scheme.Modules.pushforward f).map (omegaPullS he a) ≫
    (Scheme.Modules.pushforwardComp e f).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr w).hom.app _ ≫
        (Scheme.Modules.pushforwardComp f' g).inv.app _

private theorem mid_app (he : e ≫ r = r' ≫ spMap φ) (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U))
    (y : Γ((Scheme.Modules.pushforward f).obj (Omega r a), U)) :
    (mid he w a).app U y = (Omega r' a).presheaf.map (homOfLE hle).op
      ((omegaPullS he a).app (f ⁻¹ᵁ U) y) := by
  simp [mid]
  rfl

private theorem mid_form (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ)
    (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g) (a : ℕ) (U : X.Opens)
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm r' a (f' ⁻¹ᵁ (g ⁻¹ᵁ U)) (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b') •
        formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x)) := by
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, hg, ← Category.assoc, hf']
  have key : formRes r' hle a (formPullS he (f ⁻¹ᵁ U) a (formPull hf U a x)) =
      formPull hf' (g ⁻¹ᵁ U) a (formPullS hg U a x) :=
    ((congrArg (formRes r' hle a) (formPullS_formPull hf he hu U a x)).trans
      (formRes_formPullS_eq w hu hu' U hle a x)).trans (formPull_formPullS hg hf' hu' U a x).symm
  refine (mid_app he w a U hle _).trans ?_
  rw [omegaPullS_app_toOm, res_toOm, formPullS_smul, formRes_smul, key]

private theorem sheaf_lhs [IsFinite f] [Etale f] (hg : g ≫ s = s' ≫ spMap φ) (hf : f ≫ s = r)
    (a : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (omegaTrace hf a ≫ omegaPullS hg a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (appSecS s s' g U (secTrace s r hU b') • formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaPullS hg a).app U
    ((omegaTrace hf a).app U (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [omegaTrace_toOm_smul_formPull hf a hU, omegaPullS_app_toOm, formPullS_smul]

private theorem sheaf_rhs [IsFinite f'] [Etale f'] (hg : g ≫ s = s' ≫ spMap φ)
    (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r') (w : e ≫ f = f' ≫ g)
    (a : ℕ) {U : X.Opens} (hV : IsAffineOpen (g ⁻¹ᵁ U))
    (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b' : Sec r (f ⁻¹ᵁ U)) (x : OmU s U a) :
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
        (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x)) =
      toOm s' a (g ⁻¹ᵁ U) (secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b')) •
        formPullS hg U a x) := by
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf' a).app (g ⁻¹ᵁ U) ((mid he w a).app U
    (toOm r a (f ⁻¹ᵁ U) (b' • formPull hf U a x))) = _
  rw [mid_form hg he hf hf' w a U hle, omegaTrace_toOm_smul_formPull hf' a hV]

private theorem sheaf_id [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] [IsAffineHom g]
    (hg : g ≫ s = s' ≫ spMap φ) (he : e ≫ r = r' ≫ spMap φ) (hf : f ≫ s = r) (hf' : f' ≫ s' = r')
    (w : e ≫ f = f' ≫ g)
    (hT : ∀ (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
      (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)),
      appSecS s s' g U (secTrace s r hU b) =
        secTrace s' r' hV (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) (a : ℕ) :
    omegaTrace hf a ≫ omegaPullS hg a =
      mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a) := by
  refine hom_ext_affine fun U hU y ↦ ?_
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  have hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  obtain ⟨z, rfl⟩ := toOm_surjective (s := r) (j := a) (hU.preimage f) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hf a ≫ omegaPullS hg a).app U
      (toOm r a (f ⁻¹ᵁ U) z) =
    (mid he w a ≫ (Scheme.Modules.pushforward g).map (omegaTrace hf' a)).app U
      (toOm r a (f ⁻¹ᵁ U) z)) hf hU ?_ (fun y z hy hz ↦ ?_) (fun b' x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · rw [sheaf_lhs hg hf a hU, sheaf_rhs hg he hf hf' w a hV hle, hT U hU hV hle b']

end Sheaf

section Coh

private theorem pull_pull {X Y Z : Scheme.{0}} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] [Algebra T Γ(Z, ⊤)] {σ : R →+* S} {τ : S →+* T}
    {ρ : R →+* T} {u : Y ⟶ X} {v : Z ⟶ Y} {F : X.Modules} {G : Y.Modules} {L : Z.Modules}
    (hσ : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hτ : ∀ r, v.appTop (algebraMap S Γ(Y, ⊤) r) = algebraMap T Γ(Z, ⊤) (τ r))
    (hρ : ∀ r, (v ≫ u).appTop (algebraMap R Γ(X, ⊤) r) = algebraMap T Γ(Z, ⊤) (ρ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (Ψ : G ⟶ (Scheme.Modules.pushforward v).obj L)
    (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hτ Ψ (le_refl (v ⁻¹ᵁ ⊤)) n (cohOn.pull hσ Φ (le_refl (u ⁻¹ᵁ ⊤)) n x) =
      cohOn.pull hρ (Φ ≫ (Scheme.Modules.pushforward u).map Ψ ≫
        (Scheme.Modules.pushforwardComp v u).hom.app L) (le_refl ((v ≫ u) ⁻¹ᵁ ⊤)) n x := by
  apply (cohOn.toH' L _ n).injective
  refine (cohOn.toH'_pull hτ Ψ _ _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hρ _ _ x).symm
  erw [cohOn.toH'_pull hσ Φ, SheafPull.pull_pull]
  rfl

private theorem comp_pushforwardCongr_rfl_hom_app {X Y : Scheme.{0}} {F : X.Modules} {G : Y.Modules}
    (u : Y ⟶ X) (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) :
    Φ ≫ (Scheme.Modules.pushforwardCongr (rfl : u = u)).hom.app G = Φ := by
  ext U x
  simp
  rfl

private theorem pull_congr {X Y : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
    [Algebra R Γ(X, ⊤)] [Algebra S Γ(Y, ⊤)] {σ : R →+* S} {F : X.Modules} {G : Y.Modules}
    {u v : Y ⟶ X} (w : u = v)
    (hu : ∀ r, u.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (hv : ∀ r, v.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (Φ : F ⟶ (Scheme.Modules.pushforward u).obj G) (n : ℕ) (x : cohOn F ⊤ n) :
    cohOn.pull hv (Φ ≫ (Scheme.Modules.pushforwardCongr w).hom.app G)
        (le_refl (v ⁻¹ᵁ ⊤)) n x = cohOn.pull hu Φ (le_refl (u ⁻¹ᵁ ⊤)) n x := by
  subst w
  rw [comp_pushforwardCongr_rfl_hom_app]

end Coh

end UpperTheory.Gal.G3.HeckeTraceSheaves

open UpperTheory.Gal.G3.HeckeTraceSheaves in
theorem UpperTheory.Gal.G3.jHTrace :
    (∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b))) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → ∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y) := by
  intro hT hP k k' _ _ φ X X' Y Y' s s' g h r r' e he f hf f' hf' w a b _ _ _ _ y
  haveI : IsAffineHom g := hP k k' φ X X' s s' g h
  have hpb : IsPullback e f' f g := by
    subst hf hf'
    exact IsPullback.of_bot he w h
  have hid := sheaf_id h.w he.w hf hf' w
    (fun U hU hV hle b => hT k k' s s' g r r' e f f' hpb U hU hV hle b) a
  letI := algΓ s
  letI := algΓ s'
  letI := algΓ r
  letI := algΓ r'
  obtain ⟨z, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).surjective y
  change cohOn.pull (appTop_algebraMapS h.w) (omegaPullS h.w a) _ b
      (cohOn.map k (omegaTrace hf a) ⊤ b
        ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b).symm
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z))) =
    cohOn.map k' (omegaTrace hf' a) ⊤ b
      ((coh.pushforwardEquiv k' (appTop_algebraMap hf') (Omega r' a) b).symm
        (cohOn.pull (appTop_algebraMapS he.w) (omegaPullS he.w a) _ b
          ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega r a) b) z)))
  rw [LinearEquiv.symm_apply_apply]
  refine (cohOn.pull_map (appTop_algebraMapS h.w) (omegaPullS h.w a) (omegaTrace hf a) _ z).trans ?_
  rw [hid]
  refine (cohOn.map_pull (appTop_algebraMapS h.w) (mid he.w w a) (omegaTrace hf' a) _ z).symm.trans ?_
  congr 1
  rw [LinearEquiv.eq_symm_apply]
  have hu : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he.w]
  have hu' : (f' ≫ g) ≫ s = r' ≫ spMap φ := by
    rw [Category.assoc, h.w, ← Category.assoc, hf']
  refine (pull_pull (appTop_algebraMapS h.w) (appTop_algebraMap hf') (appTop_algebraMapS hu')
    (mid he.w w a) (𝟙 _) b z).trans ?_
  refine Eq.trans ?_ (pull_pull (appTop_algebraMap hf) (appTop_algebraMapS he.w)
    (appTop_algebraMapS hu) (𝟙 _) (omegaPullS he.w a) b z).symm
  refine Eq.trans ?_ (pull_congr w (appTop_algebraMapS hu) (appTop_algebraMapS hu') _ b z)
  congr 1

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

namespace UpperTheory.Gal.G3.FunctionRings

variable {G R : Type} [Group G] [Field R] {K : Subgroup G}

variable {B : Scheme.{0}} (X : Tower B G)

end UpperTheory.Gal.G3.FunctionRings

private theorem apply_out_mk_eq_of_tower_biinvariant {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f : G → R) (hf : ∀ k ∈ X.K j, ∀ g : G, f (k * g) = f g ∧ f (g * k) = f g) (w : G) :
    f ((QuotientGroup.mk w : G ⧸ X.K j).out) = f w := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) w
  rw [hu]
  exact (hf _ u.2 w).2

private theorem tower_isFn_ind_inv_of_mem {B : Scheme} {G : Type} [Group G] (X : Tower B G) (R : Type) [Field R]
    (j : X.ι) (h : G) (hh : h ∈ X.Δ) : X.IsFn j (ind R (X.K j) h⁻¹) := by
  classical
  have key : ∀ g, ind R (X.K j) h⁻¹ g ≠ 0 ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro g
    unfold ind
    rw [Set.indicator_apply]
    split_ifs with hg <;> simp [hg]
  have memL : ∀ k ∈ X.K j, ∀ g, k * g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro k hk g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨k⁻¹ * x, (X.K j).mul_mem ((X.K j).inv_mem hk) hx, y, hy, ?_⟩
      rw [show k⁻¹ * x * h⁻¹ * y = k⁻¹ * (x * h⁻¹ * y) by group, ← e]
      group
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k * x, (X.K j).mul_mem hk hx, y, hy, by rw [e]; group⟩
  have memR : ∀ k ∈ X.K j, ∀ g, g * k ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro k hk g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y * k⁻¹, (X.K j).mul_mem hy ((X.K j).inv_mem hk), ?_⟩
      rw [show x * h⁻¹ * (y * k⁻¹) = (x * h⁻¹ * y) * k⁻¹ by group, ← e]
      group
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k, (X.K j).mul_mem hy hk, by rw [e]; group⟩
  refine ⟨fun k hk g => ⟨?_, ?_⟩, fun g hg => ?_, ?_⟩
  · unfold ind
    simp only [Set.indicator_apply, memL k hk g, Pi.one_apply]
  · unfold ind
    simp only [Set.indicator_apply, memR k hk g, Pi.one_apply]
  · obtain ⟨x, hx, y, hy, e⟩ := DoubleCoset.mem_doubleCoset.mp ((key g).mp hg)
    rw [e, show (x * h⁻¹ * y)⁻¹ = y⁻¹ * (h * x⁻¹) by group]
    exact X.Δ.mul_mem (X.K_le _ _ ((X.K j).inv_mem hy))
      (X.Δ.mul_mem hh (X.K_le _ _ ((X.K j).inv_mem hx)))
  · obtain ⟨m, -, -, hS⟩ := X.deep j {(j, h)}
    have hu : ∀ u ∈ X.K m, h * u * h⁻¹ ∈ X.K j :=
      fun u hu => hS (j, h) (Finset.mem_singleton_self _) u hu
    have fin : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := by
      have := X.idx m j
      rw [Subgroup.relIndex, Subgroup.index] at this
      exact (Nat.card_ne_zero.mp this).2
    refine (Set.finite_range (fun q : X.K j ⧸ (X.K m).subgroupOf (X.K j) =>
      (QuotientGroup.mk (((q.out : X.K j) : G) * h⁻¹) : G ⧸ X.K j))).subset ?_
    intro y hy
    obtain ⟨x, hx, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp ((key _).mp hy)
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
    obtain ⟨u, hu'⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) ⟨x, hx⟩
    have hum : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
    have hc := hu _ hum
    simp only
    rw [hu']
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [e, QuotientGroup.eq]
    rw [show ((⟨x, hx⟩ * (u : X.K j) : X.K j) : G) = x * ((u : X.K j) : G) from rfl]
    rw [show (x * ((u : X.K j) : G) * h⁻¹)⁻¹ * (x * h⁻¹ * z) =
      (h * ((u : X.K j) : G) * h⁻¹)⁻¹ * z by group]
    exact (X.K j).mul_mem ((X.K j).inv_mem hc) hz

private theorem tower_isFn_add {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f f' : G → R) (hf : X.IsFn j f) (hf' : X.IsFn j f') : X.IsFn j (f + f') := by
  obtain ⟨a1, b1, c1⟩ := hf
  obtain ⟨a2, b2, c2⟩ := hf'
  refine ⟨fun k hk g => ?_, fun g hg => ?_, (c1.union c2).subset ?_⟩
  · simp [(a1 k hk g).1, (a1 k hk g).2, (a2 k hk g).1, (a2 k hk g).2]
  · by_cases h1 : f g = 0
    · exact b2 g (by simpa [h1] using hg)
    · exact b1 g h1
  · intro y hy
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    exact hy (by simp [hn.1, hn.2])

private theorem tower_isFn_conv {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f f' : G → R) (hf : X.IsFn j f) (hf' : X.IsFn j f') :
    X.IsFn j (conv (X.K j) f f') := by
  obtain ⟨a1, b1, c1⟩ := hf
  obtain ⟨a2, b2, c2⟩ := hf'
  have nz : ∀ x, conv (X.K j) f f' x ≠ 0 →
      ∃ y : G ⧸ X.K j, f y.out ≠ 0 ∧ f' (y.out⁻¹ * x) ≠ 0 := by
    intro x hx
    by_contra hn
    push_neg at hn
    apply hx
    have h0 : ∀ y : G ⧸ X.K j, f y.out * f' (y.out⁻¹ * x) = 0 := by
      intro y
      by_cases h : f y.out = 0
      · simp [h]
      · simp [hn y h]
    simp only [conv, h0, finsum_zero]
  refine ⟨fun k hk g => ⟨?_, ?_⟩, fun g hg => ?_, ?_⟩
  · unfold conv
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ X.K j))]
    refine finsum_congr (fun z => ?_)
    have e1 : (MulAction.toPerm k : Equiv.Perm (G ⧸ X.K j)) z =
        (QuotientGroup.mk (k * z.out) : G ⧸ X.K j) := by
      conv_lhs => rw [← QuotientGroup.out_eq' z]
      rfl
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) (k * z.out)
    rw [e1, hu, (a1 _ u.2 _).2, (a1 k hk _).1]
    congr 1
    rw [show (k * z.out * (u : G))⁻¹ * (k * g) = (u : G)⁻¹ * (z.out⁻¹ * g) by group]
    exact (a2 _ ((X.K j).inv_mem u.2) _).1
  · unfold conv
    refine finsum_congr (fun y => ?_)
    rw [← mul_assoc, (a2 k hk _).2]
  · obtain ⟨y, h1, h2⟩ := nz g hg
    have := X.Δ.mul_mem (b2 _ h2) (b1 _ h1)
    rwa [show (y.out⁻¹ * g)⁻¹ * y.out⁻¹ = g⁻¹ by group] at this
  · refine (Set.Finite.biUnion (t := fun y : G ⧸ X.K j =>
      (fun w => (y.out : G) • w) '' {z : G ⧸ X.K j | f' z.out ≠ 0}) c1
      (fun y _ => c2.image _)).subset ?_
    intro x hx
    obtain ⟨y, h1, h2⟩ := nz _ hx
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    refine ⟨y, h1, QuotientGroup.mk (y.out⁻¹ * x.out), ?_, ?_⟩
    · rw [apply_out_mk_eq_of_tower_biinvariant X j f' a2]
      exact h2
    · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_inv_cancel_left, QuotientGroup.out_eq']

private theorem tower_isFn_smul {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (c : R) (f : G → R) (hf : X.IsFn j f) : X.IsFn j (c • f) := by
  obtain ⟨a1, b1, c1⟩ := hf
  refine ⟨fun k hk g => ?_, fun g hg => b1 g ?_, c1.subset ?_⟩
  · simp [(a1 k hk g).1, (a1 k hk g).2]
  · intro h0
    apply hg
    simp [h0]
  · intro y hy h0
    apply hy
    simp [h0]

open UpperTheory.Gal.G3.FunctionRings in
theorem UpperTheory.Gal.G3.pFnRing : FnRing := by
  intro B G _ X R _ j
  refine ⟨fun h hh => tower_isFn_ind_inv_of_mem X R j h hh, ?_,
    fun f f' hf hf' => ⟨tower_isFn_add X j f f' hf hf', tower_isFn_conv X j f f' hf hf'⟩,
    fun c f hf => tower_isFn_smul X j c f hf⟩
  refine ⟨fun k _ g => ⟨rfl, rfl⟩, fun g hg => (hg rfl).elim, ?_⟩
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)

universe u v

namespace UpperTheory.Gal.G3

abbrev etG (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Th.{1} (sp k) ℚ_[l] :=
  (et l (sp Ω)).bc (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def AlgIsoPts : Prop := ∀ (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E],
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (algebraMap D E) = x) →
  Function.Bijective (algebraMap D E)

def AlgSplit : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Algebra.Etale A A']
  (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)),
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : C →+* Ω) (y : A' →+* Ω), y.comp (algebraMap A A') = x.comp (algebraMap A C) →
    ∃! j, x.comp (τ j : A' →+* C) = y) →
  ∃ e : C ⊗[A] A' ≃ₐ[C] (J → C), ∀ b j, e (1 ⊗ₜ b) j = τ j b

def AlgTr : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Module.Finite A A']
  [Algebra.Etale A A'] (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)) (e : C ⊗[A] A' ≃ₐ[C] (J → C)),
  (∀ b j, e (1 ⊗ₜ b) j = τ j b) → ∀ b, algebraMap A C (etTrace A A' b) = ∑ j, τ j b

def FEtBasic : Prop :=
  (∀ {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ), IsPullback v s' s g → FEt s d → FEt s' d) ∧
  (∀ {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ), FEt r e → FEt s d → FEt (r ≫ s) (d * e)) ∧
  ∀ {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)), IsGalois c G a → FEt c (Nat.card G)

def SplitsBasic : Prop :=
  (∀ {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W),
    Splits s c σ → Splits s (g ≫ c) fun j => g ≫ σ j) ∧
  ∀ {P Y Z' Z W : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) [IsFinite s] [Etale s], IsPullback v s' s g →
    ∀ (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P)), (∀ j, σ j ≫ s' = c) →
      (Splits s' c σ ↔ Splits s (c ≫ g) fun j => σ j ≫ v)

def OrdEx : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ), ∃ (W : Scheme.{0}) (c : W ⟶ Z)
  (σ : Fin d → (W ⟶ Y)), IsFinite c ∧ Etale c ∧ (∀ j, σ j ≫ s = c) ∧
  (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j) ∧
  ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
    (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
    ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j

def OrdStep : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (d : ℕ) (σ : Fin d → (W ⟶ Y)),
  (∀ j, σ j ≫ s = c) → ∃ V : (pullback s c).Opens, IsClosed (V : Set ↑(pullback s c)) ∧
    ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ pullback s c),
      (x (IsLocalRing.closedPoint Ω) ∈ V ↔ ∀ j, x ≫ pullback.snd s c ≫ σ j ≠ x ≫ pullback.fst s c)

def GalClosD : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) (d : ℕ), FEt s d →
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (σ : Fin d → (W ⟶ Y)),
    IsGalois c G a ∧ Splits s c σ

def MultiSplit : Prop := ∀ {Z : Scheme.{0}} (n : ℕ) (Y : Fin n → Scheme.{0}) (s : ∀ i, Y i ⟶ Z) (d : Fin n → ℕ),
  (∀ i, FEt (s i) (d i)) → ∃ (W : Scheme.{0}) (c : W ⟶ Z) (e : ℕ), 0 < e ∧ FEt c e ∧
    ∀ i, ∃ σ : Fin (d i) → (W ⟶ Y i), Splits (s i) c σ

def FEtInj : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z W : Scheme.{0}} (p : Z ⟶ B)
  (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (d : ℕ), 0 < d → FEt c d → Function.Injective (T.pull c hc)

def TrBase : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {P Y Z' Z : Scheme.{0}}
  (p : Z ⟶ B) (q : Y ⟶ B) (p' : Z' ⟶ B) (q' : P ⟶ B) (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ)
  (hv : v ≫ q = q') (hg : g ≫ p = p'), s' ≫ p' = q' → IsPullback v s' s g → FEt s d →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p' q' s' tr' → ∀ x, T.pull g hg (tr x) = tr' (T.pull v hv x)

def TrPushM : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Y P Z : Scheme.{0}}
  (p : Z ⟶ B) (q : P ⟶ B) (r : Y ⟶ B) (κ : Y ⟶ P) (s : P ⟶ Z) (d m : ℕ) (hκ : κ ≫ q = r), s ≫ p = q → FEt s d → FEt κ m →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p r (κ ≫ s) tr' → ∀ x, tr' (T.pull κ hκ x) = (m : R) • tr x

def SplitsComp : Prop := ∀ {Y P Z W : Scheme.{0}} (κ : Y ⟶ P) (s : P ⟶ Z) [IsFinite κ] [Etale κ] [IsFinite s] [Etale s]
  (c : W ⟶ Z) (I J : Type) [Finite I] [Finite J] (τ : I → (W ⟶ P)) (σ : I → J → (W ⟶ Y)), Splits s c τ →
  (∀ i, Splits κ (τ i) (σ i)) → Splits (κ ≫ s) c fun x : I × J => σ x.1 x.2

def LiesAbs : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z Y C D : Scheme.{0}}
  (pZ : Z ⟶ B) (pY : Y ⟶ B) (pC : C ⟶ B) (pD : D ⟶ B) (π : Z ⟶ Y) (hπ : π ≫ pY = pZ) (sg tg : C ⟶ Z) (htg : tg ≫ pZ = pC)
  (s t : D ⟶ Y) (ht : t ≫ pY = pD) (κ : C ⟶ D) (h : sg ≫ π = κ ≫ s) (d m : ℕ), sg ≫ pZ = pC → s ≫ pY = pD →
  κ ≫ t = tg ≫ π → FEt s d → FEt (pullback.lift sg κ h) m → ∀ tr trg, T.IsTr pY pD s tr → T.IsTr pZ pC sg trg →
  ∀ x, trg (T.pull tg htg (T.pull π hπ x)) = (m : R) • T.pull π hπ (tr (T.pull t ht x))

abbrev piK {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    H.Z ⟶ pullback C.p (gen O k) := pullback.lift C.π H.q C.ov

theorem piK_snd {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    piK C ≫ pullback.snd C.p (gen O k) = H.q := pullback.lift_snd _ _ _

def HopSpec : Prop := ∀ (l : ℕ) [Fact l.Prime] {k : Type} [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω]
  [Algebra k Ω] (g : H.Γ) (d : ℕ), FEt (H.s g) d → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) ∧
    ∀ tr, (etG l k Ω).IsTr H.q (H.s g ≫ H.q) (H.s g) tr → hop l H Ω g = tr ∘ₗ (etG l k Ω).pull (H.t g) (H.comm g)

def LiesGen : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m : ℕ), C.Lies g s t m →
  ∃ (κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k)) (h : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl),
    κ ≫ bcMap (gen O k) t hst = H.t g ≫ piK C ∧ FEt (pullback.lift (H.s g) κ h) m

def LiesOp : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m d : ℕ), C.Lies g s t m →
  FEt (bcMap (gen O k) s (rfl : s ≫ C.p = _)) d → ∀ {R : Type} [Field R] (T : Th.{u} (sp k) R), T.Good →
  ∀ tr trg, T.IsTr (pullback.snd C.p (gen O k)) (pullback.snd (s ≫ C.p) (gen O k)) (bcMap (gen O k) s rfl) tr →
    T.IsTr H.q (H.s g ≫ H.q) (H.s g) trg →
    ∀ x, trg (T.pull (H.t g) (H.comm g) (T.pull (piK C) (piK_snd C) x)) =
      (m : R) • T.pull (piK C) (piK_snd C) (tr (T.pull (bcMap (gen O k) t hst) (bcMap_snd _ _ _) x))

def CoverInv : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O), C.Onto → ∀ {R : Type} [Field R] [CharZero R] (T : Th.{u} (sp k) R), T.Good →
  Function.Injective (T.pull (piK C) (piK_snd C)) ∧ ∀ y : T.H H.q,
    (∀ g, IsIso (H.s g) → θ g = 1 → ∃ tr, T.IsTr H.q (H.s g ≫ H.q) (H.s g) tr ∧ tr (T.pull (H.t g) (H.comm g) y) = y) →
    ∃ x, T.pull (piK C) (piK_snd C) x = y

def PieceLe : Prop := ∀ (l : ℕ) [Fact l.Prime] {k L O : Type} [Field k] [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O k],
  (l : k) ≠ 0 → ∀ {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O), C.Onto → ∀ (Ω : Type) [Field Ω] [Algebra k Ω],
  Function.Injective (((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L) ∧
  ∀ y ∈ piece l H Ω L θ, ∃ x, ((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L x = y

end UpperTheory.Gal.G3

end
end

