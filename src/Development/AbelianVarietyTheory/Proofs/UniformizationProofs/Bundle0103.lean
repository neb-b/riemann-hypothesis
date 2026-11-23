module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaAction
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjBaseChange

open MvPolynomial

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem appLE_cst (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V h).hom.comp (cst f U) = cst (φ ≫ f) V := by
  have e : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ φ.appLE U V h =
      φ.appTop ≫ X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  ext a
  exact congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) e

theorem cst_comp (f' : X' ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (V : X'.Opens) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) V = (cst f' V).comp g := by
  ext a
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact congrArg (fun q => rs X' (le_top : V ≤ ⊤) (f'.appTop.hom q)) e.symm

theorem gs_appLE (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (z : X') (hz : z ∈ V) (a : Γ(X, U)) :
    gs (𝟙 X') z V ((φ.appLE U V h).hom a) = gs φ z U a :=
  (gs_res (𝟙 X') z h hz ((φ.app U).hom a)).trans ((gs_pull (𝟙 X') φ z U (h hz) a).trans (by rw [Category.id_comp]))

theorem isClosedImmersion_of_charts (φ : X' ⟶ X) {J : Type} (U : J → X.Opens) (hc : ⨆ i, U i = ⊤)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (φ ⁻¹ᵁ U i))
    (hs : ∀ i, Function.Surjective (φ.app (U i)).hom) : IsClosedImmersion φ := by
  refine @HasAffineProperty.of_iSup_eq_top _ _ IsClosedImmersion.hasAffineProperty _ _ _ _
    (fun i => ⟨U i, hU i⟩) hc fun i => ⟨hV i, ?_⟩
  have key : ∀ (A : X.Opens) (B : X'.Opens) (h : B ≤ φ ⁻¹ᵁ A), A = U i → B = φ ⁻¹ᵁ U i →
      Function.Surjective (φ.appLE A B h).hom := by
    rintro _ _ h rfl rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact hs i
  show Function.Surjective ((φ ∣_ U i).app ⊤).hom
  rw [morphismRestrict_app']
  exact key _ _ _ (by simp) (by simp)

theorem isPullback_of_charts (g : R →+* R') (hg : Function.Surjective g) (φ : X' ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (hw : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) {J : Type} (U : J → X.Opens) (V : J → X'.Opens)
    (hUV : ∀ i, V i = φ ⁻¹ᵁ U i) (hc : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hs : ∀ i, Function.Surjective (φ.appLE (U i) (V i) (hUV i).le).hom)
    (hk : ∀ i a, (φ.appLE (U i) (V i) (hUV i).le).hom a = 0 → ∀ (B : Type) [CommRing B] (θ : Γ(X, U i) →+* B)
      (c : R' →+* B), θ.comp (cst f (U i)) = c.comp g → θ a = 0) :
    IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  obtain rfl : V = fun i => φ ⁻¹ᵁ U i := funext hUV
  simp only [Scheme.Hom.appLE_eq_app] at hs hk
  have := isClosedImmersion_of_charts φ U hc hU hV hs
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have hle : φ.ker ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom g))).ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i => ⟨U i, hU i⟩) hc fun i a ha => ?_
    rw [Scheme.Hom.ker_apply] at ha ⊢
    refine hk i a ha _ _ (cst (pullback.snd f (Spec.map (CommRingCat.ofHom g))) _) ?_
    rw [← cst_comp, ← pullback.condition, ← appLE_cst _ f le_rfl, Scheme.Hom.appLE_eq_app]
  have hl := IsClosedImmersion.lift_fac φ _ hle
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.fst t.snd t.condition ≫ IsClosedImmersion.lift φ _ hle) (fun t => ?_) (fun t => ?_)
    (fun t m h₁ _ => ?_)⟩⟩
  · rw [Category.assoc, hl, pullback.lift_fst]
  · rw [← cancel_mono (Spec.map (CommRingCat.ofHom g)), Category.assoc, ← hw, ← Category.assoc, Category.assoc _ _ φ,
      hl, pullback.lift_fst, t.condition]
  · rw [← cancel_mono φ, Category.assoc, hl, pullback.lift_fst, h₁]

theorem eventually_exists_form (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {m : ℕ} {s : Fin (m + 1) → H.Sec}
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i)) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (hp : eval₂Hom (cst f _) (r i) p = 0) :
    ∀ᶠ d in Filter.atTop, ∃ F ∈ vanishingForms f s d, MvPolynomial.X i - 1 ∣ F - p := by
  obtain ⟨e, F, hF, hFp⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    obtain ⟨G, hG⟩ := hFp
    rw [eq_add_of_sub_eq hG, map_add (f := _), hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup n + e)] with d hd
  obtain ⟨c, rfl⟩ : ∃ c, d = c + e := ⟨d - e, by omega⟩
  refine ⟨MvPolynomial.X i ^ c * F, ?_, ?_⟩
  · refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i c).mul hF) fun j => ?_
    have hle : n j ≤ c := (Finset.le_sup (Finset.mem_univ j)).trans (by omega)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]
  · have : MvPolynomial.X i ^ c * F - p = (MvPolynomial.X i ^ c - 1) * F + (F - p) := by ring
    rw [this]
    exact ((sub_one_dvd_pow_sub_one _ c).mul_right _).add hFp

theorem isPullback_of_equations_lift : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Function.Surjective g → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g)) → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ t₀ : ℕ, (∀ t, t₀ ≤ t → ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f' ≫ (Spec.map (CommRingCat.ofHom g))) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ F₁ : MvPolynomial (Fin (n + 1)) R, F₁.IsHomogeneous t ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F₁) = 0) ∧ MvPolynomial.map g F₁ = MvPolynomial.map g F) → IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  intro R _ X f H n s hH ⟨hc, hs⟩ R' _ g hg X' f' H' s' φ w hH' ⟨hc', hs'⟩ hw _ hrel t₀ hlift
  choose ha r hr hsur using hs
  choose ha' r' hr' hsur' using hs'
  have hR : ∀ i, IsRatioFamily s i (r i) := hr
  have hR' : ∀ i, IsRatioFamily s' i (r' i) := hr'
  have unit : ∀ i z k, φ z ∈ H.U k → (φ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs φ z _ ((s i).f k))) := fun i z k hk =>
    ((mem_nonzeroLocus_iff_isUnit _ hk).trans (LBGerm.isUnit_gs_iff (𝟙 X) _ _ hk _)).trans
      (LBGerm.isUnit_gs_iff φ z _ hk _).symm
  have hUV : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext z
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    refine (mem_nonzeroLocus_iff_isUnit _ hk').trans (Iff.trans ?_ (unit i z k hk).symm)
    rw [hrel i z k k' hk hk', Units.isUnit_units_mul]
  have hrr : ∀ i j, (φ.appLE _ _ (hUV i).le).hom (r i j) = r' i j := fun i j => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    have hz₁ : φ z ∈ nonzeroLocus (s i) := (hUV i).le hz
    have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hz₁, hk⟩
    have e := congrArg (gs φ z _) (hr i j k)
    rw [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e
    rw [gs_appLE φ _ z hz]
    refine ((unit i z k hk).1 hz₁).mul_right_cancel (e.symm.trans ?_)
    rw [hrel j z k k' hk hk', hrel i z k k' hk hk', (hR' i).gs_eq hz hk' j]
    ring
  have hev : ∀ i p, (φ.appLE _ _ (hUV i).le).hom (eval₂Hom (cst f _) (r i) p) =
      eval₂Hom (cst (f' ≫ Spec.map (CommRingCat.ofHom g)) _) (r' i) p := fun i p => by
    rw [map_eval₂Hom, appLE_cst, hw]
    simp only [hrr]
  refine isPullback_of_charts g hg φ f f' hw _ _ hUV hc ha ha' (fun i b => ?_) fun i a h0 B _ θ c hθ => ?_
  · obtain ⟨q, rfl⟩ := hsur' i b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective g hg q
    exact ⟨_, (hev i p).trans (by rw [cst_comp, eval₂Hom_map_hom])⟩
  · obtain ⟨p, rfl⟩ := hsur i a
    rw [hev] at h0
    obtain ⟨t, ht, F, hF, G, hG⟩ := ((Filter.eventually_ge_atTop t₀).and
      (eventually_exists_form _ hc' ha' r' hR' i p h0)).exists
    obtain ⟨F₁, h₁, h₂, h₃⟩ := hlift t ht F hF.1 hF.2
    have e₁ : eval₂Hom (cst f _) (r i) F₁ = 0 := (hR i).eval_eq_zero f ⟨h₁, h₂⟩
    have e₂ : eval₂Hom (cst f _) (r i) p = eval₂Hom (cst f _) (r i) F := by
      rw [eq_add_of_sub_eq hG, map_add (f := _), map_mul, map_sub, map_one, eval₂Hom_X', (hR i).self_eq_one]
      simp
    have e₃ : ∀ P, θ (eval₂Hom (cst f _) (r i) P) = eval₂Hom c (fun j => θ (r i j)) (MvPolynomial.map g P) :=
      fun P => by rw [map_eval₂Hom, hθ, eval₂Hom_map_hom]
    rw [e₂, e₃, ← h₃, ← e₃, e₁, map_zero]

end GlobalTheory.ProjBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

section Germ
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem gm_eq_of_isWt {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V) (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  have hz : z ∈ W := ⟨h₁, h₂⟩
  let ρ : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  have hW : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have inj : Function.Injective (W.ι.appLE W ⊤ hW).hom := by
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.left.presheaf.mapIso (eqToIso (by simp : W.ι ''ᵁ ⊤ = W)).op).hom).1
  have e₁ : ((ρ ≫ t) ≫ i) * (ρ ≫ g) = ρ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have a : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) k',
      ((W.ι ≫ r).appLE U ⊤ k').hom x.val = (W.ι.appLE W ⊤ hW).hom (res k (pullU r U x)).val := fun r U k x k' =>
    (congrArg (fun q => q.hom x.val) (Scheme.Hom.appLE_comp_appLE W.ι r U W ⊤ k hW)).symm
  have b : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      gm (𝟙 Z.left) z W (res k (pullU r U x)) = gm r z U x := fun r U k x =>
    (gm_res (𝟙 Z.left) z k hz _).trans ((gm_pull (𝟙 Z.left) r z U (k hz) x).trans (by simp only [Category.id_comp]))
  have h := hu _ (ρ ≫ t) (ρ ≫ g) (by rw [e₁]; exact fun x _ => x.2.1) (fun x _ => x.2.2)
  have c : ∀ (r r' : Over.mk (W.ι ≫ Z.hom) ⟶ G) (_ : r = r') k k',
      (r.left.appLE V ⊤ k).hom u.val = (r'.left.appLE V ⊤ k').hom u.val := by
    rintro r _ rfl k k'; rfl
  have d : (ρ ≫ t).left.appTop = (W.ι ≫ t.left).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [c _ _ e₁ _ (fun x _ => x.2.1), d] at h
  have h' := ((a _ V inf_le_left u _).symm.trans h).trans
    ((congrArg₂ (· * ·) (a t.left ⊤ le_top (charUnit S X χ) _) (a g.left V inf_le_right u _)).trans
      (map_mul _ _ _).symm)
  rw [← b _ V inf_le_left, ← b t.left ⊤ le_top, ← b g.left V inf_le_right, ← map_mul]
  exact congrArg _ (Units.ext (inj h'))

end Germ

section Flat
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem mem_pull_linComb {y : Y'} {j : PUnit → K → L.ι} :
    y ∈ ((LB.LinComb L φ ε).pull F).U j ↔ y ∈ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 h) k,
    fun h => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)⟩

theorem gm_pull_linComb (y : Y') (j j' : PUnit → K → L.ι) (h : y ∈ ((LB.LinComb L φ ε).pull F).U j)
    (h' : y ∈ ((LB.LinComb L φ ε).pull F).U j') :
    gm (𝟙 Y') y _ (((LB.LinComb L φ ε).pull F).g j j') =
      gm (𝟙 Y') y _ ((LB.LinComb L (fun k => F ≫ φ k) ε).g (j PUnit.unit) (j' PUnit.unit)) := by
  have a := gm_pull_g (LB.LinComb L φ ε) F (𝟙 Y') y j j' h h'
  have m : ∀ j : PUnit → K → L.ι, y ∈ ((LB.LinComb L φ ε).pull F).U j →
      (𝟙 Y' ≫ F) y ∈ LB.wchart L φ (j PUnit.unit) := fun j h => by
    rw [Category.id_comp]; exact (mem_pull (L := LB.LinComb L φ ε)).1 h
  have b := gm_linComb L φ ε (𝟙 Y' ≫ F) y (j PUnit.unit) (j' PUnit.unit) (m j h) (m j' h')
  have c := gm_linComb L (fun k => F ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit) (mem_pull_linComb.1 h)
      (mem_pull_linComb.1 h')
  simp only [Category.assoc] at b
  exact a.trans (b.trans c.symm)

def flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε) :=
  ⟨fun j => res (show LB.wchart L (fun k => F ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull F).U (fun _ => j) from
    fun _ h => (mem_pull_linComb (ε := ε) (j := fun _ => j)).2 h) (u.s fun _ => j)⟩

def unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) : LB.Gen ((LB.LinComb L φ ε).pull F) :=
  ⟨fun j => res (fun _ h => mem_pull_linComb.1 h) (v.s (j PUnit.unit))⟩

theorem flatGen_isGen {u : LB.Gen ((LB.LinComb L φ ε).pull F)} (hu : u.IsGen) : (flatGen u).IsGen := fun j j' =>
  unit_ext fun y hy => by
    have m : y ∈ ((LB.LinComb L φ ε).pull F).U (fun _ => j) ⊓ ((LB.LinComb L φ ε).pull F).U (fun _ => j') :=
      ⟨(mem_pull_linComb (j := fun _ => j)).2 hy.1, (mem_pull_linComb (j := fun _ => j')).2 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hu (fun _ => j) (fun _ => j'))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m, gm_pull_linComb y _ _ m.1 m.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

theorem unflatGen_isGen {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) : (unflatGen v).IsGen :=
  fun j j' => unit_ext fun y hy => by
    have m : y ∈ (LB.LinComb L (fun k => F ≫ φ k) ε).U (j PUnit.unit) ⊓
        (LB.LinComb L (fun k => F ≫ φ k) ε).U (j' PUnit.unit) := ⟨mem_pull_linComb.1 hy.1, mem_pull_linComb.1 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hv (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull_linComb y _ _ hy.1 hy.2]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

end Flat

section Add
variable {S A Y : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A} {F : G.left ⟶ Y}
  (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
include hF

theorem val_flatGen {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ} {u : LB.Gen ((LB.LinComb L φ ε).pull F)}
    {χ : X} (hu : ∀ j, IsWt i _ (u.s j).val χ) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} {J}
    (hJ : Good L z J) : val (flatGen u) ((t ≫ i) * g).left z J =
      gm t.left z ⊤ (charUnit S X χ) * val (flatGen u) g.left z J := by
  have e : ∀ k, J (((t ≫ i) * g).left ≫ F ≫ φ k) = J (g.left ≫ F ≫ φ k) := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  have m₁ := hJ.mem (fun k => F ≫ φ k) ((t ≫ i) * g).left
  have m₂ := hJ.mem (fun k => F ≫ φ k) g.left
  rw [funext e] at m₁
  rw [val_of _ _ z J _ e]
  exact (gm_res _ z _ m₁ _).trans ((gm_eq_of_isWt (hu fun _ k => J (g.left ≫ F ≫ φ k)) t g z
    (mem_pull_linComb.2 m₁) (mem_pull_linComb.2 m₂)).trans
    (congrArg _ (gm_res _ z _ m₂ _).symm))

theorem isWt_unflatGen (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
      val v ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val v g.left z J) (j) :
    IsWt i _ ((unflatGen v).s j).val χ := isWt_of_gm _ _ fun Z t g z m₂ => by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have m₁ : ((t ≫ i) * g).left z ∈ ((LB.LinComb L φ ε).pull F).U j := by
    have := mem_pull.1 m₂
    refine mem_pull.2 ?_
    exact (congrArg (fun q => q z) (hF Z t g)).symm ▸ this
  have le : ((LB.LinComb L φ ε).pull F).U j ≤ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
    fun _ h => mem_pull_linComb.1 h
  have e₁ := (gm_res _ z le m₁ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₁) (hJ.mem _ _))
  have e₂ := (gm_res _ z le m₂ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₂) (hJ.mem _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg _ e₂.symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (h Z t g z J hJ)
  have e : ∀ k, ((t ≫ i) * g).left ≫ F ≫ φ k = g.left ≫ F ≫ φ k := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  refine Finset.prod_congr rfl fun k _ => ?_
  beta_reduce
  rw [e]

theorem exists_genWt_add (hL : L.IsLB) {K K' K'' K₀ : Type} [Fintype K] [Fintype K'] [Fintype K''] [Fintype K₀]
    {φ : K → (Y ⟶ A)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A)} {ε'' : K'' → ℤ}
    {φ₀ : K₀ → (Y ⟶ A)} {ε₀ : K₀ → ℤ} (hw : Triv (LB.LinComb L φ₀ ε₀))
    (hs : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ A) → U),
      (∏ k, f (φ k) ^ ε k) * (∏ k, f (φ' k) ^ ε' k) * ∏ k, f (φ₀ k) ^ ε₀ k = ∏ k, f (φ'' k) ^ ε'' k) {χ χ' : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ ε).pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ)
    (h' : ∃ u : LB.Gen ((LB.LinComb L φ' ε').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ') :
    ∃ u : LB.Gen ((LB.LinComb L φ'' ε'').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val (χ + χ') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨u', hu', hχ'⟩ := h'
  obtain ⟨v, hv, H⟩ := exists_gen (φ' := fun k => F ≫ φ'' k) (ε' := ε'') hL
    (fun U _ f => (Fintype.prod_sum_type _).trans ((congrArg (· * _) (Fintype.prod_sum_type _)).trans
      (hs U fun q => f (F ≫ q)))) _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (flatGen_isGen hu'))
      (DVR.pullGen_isGen _ _ _ _ hw F))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen hF hL hv fun Z t g z J hJ => ?_⟩
  rw [H _ _ z J hJ, H _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hF,
    val_flatGen hF hχ t g hJ, val_flatGen hF hχ' t g hJ, gm_charUnit, gm_charUnit, gm_charUnit, chV_add, map_mul]
  ac_rfl

end Add

theorem TQ.mul_comp_q {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem triv_square_sections {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    [IsCommMonObj B] {L : RigLB B} (κ : CubicalStr B L) (c c' : 𝟙_ _ ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left] ![1, 1, -1, -1]) := by
  obtain ⟨w, hw⟩ := GlobalTheory.Square.triv_square (t := 𝟙 (Spec (CommRingCat.of V))) κ c c'
  let ρ : B ⟶ 𝟙_ _ ⊗ B := lift (toUnit B) (𝟙 B)
  have e : ∀ x : 𝟙_ _ ⟶ B, ρ.left ≫ (translPt (T := 𝟙_ _) B x).left = ((toUnit B ≫ x) * 𝟙 B).left := fun x => by
    rw [← Over.comp_left]
    change (ρ ≫ ((fst _ B ≫ x) * snd _ B)).left = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e' : ρ.left ≫ (snd (𝟙_ _) B).left = 𝟙 B.left := by rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left]) (ε' := ![1, 1, -1, -1]) L.isLB (fun U _ f => Finset.prod_congr rfl fun k _ => by
      fin_cases k
      exacts [congrArg (fun q => f q ^ (1 : ℤ)) (e _), congrArg (fun q => f q ^ (1 : ℤ)) e',
        congrArg (fun q => f q ^ (-1 : ℤ)) (e _), congrArg (fun q => f q ^ (-1 : ℤ)) (e _)])
    _ (DVR.pullGen_isGen _ _ _ _ hw ρ.left)
  exact ⟨u, hu⟩

theorem repWt_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  intro V _ _ _ A G _ _ s t a χ χ' c c' e h h'
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem mem_wchart_oneTerm {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (k : K) {j : K → L.ι} {x : X} :
    x ∈ LB.wchart L (fun _ : K => 𝟙 X) j ↔ x ∈ L.U (j k) :=
  ⟨fun h => Set.mem_iInter.1 h k, fun h => Set.mem_iInter.2 fun k' => by
    obtain rfl := Subsingleton.elim k k'; exact h⟩

theorem exists_sec_oneTerm {X : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Unique K] [Fintype K'] [Unique K']
    {e e' : ℤ} (he : e = e') (s : (LB.LinComb L (fun _ : K => 𝟙 X) (fun _ => e)).Sec) :
    ∃ s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e')).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (s'.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) := by
  subst he
  have le : ∀ j : K' → L.ι, LB.wchart L (fun _ : K' => 𝟙 X) j ≤
      LB.wchart L (fun _ : K => 𝟙 X) (fun _ => j default) := fun j x hx =>
    (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hx)
  let s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)).Sec :=
    secOfGerm (M := LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)) (fun j => resG X (le j) (s.f fun _ => j default))
      fun y j j' hj hj' => by
        refine (gs_res (𝟙 X) y (le j) hj _).trans ((sec_trans s (𝟙 X) y (le j hj) (le j' hj')).trans
          (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hj' _).symm))
        refine Eq.trans ?_ (gm_linComb L (fun _ : K' => 𝟙 X) (fun _ => e) (𝟙 X) y j j' hj hj').symm
        rw [trF, Fintype.prod_unique, Fintype.prod_unique]
  have hs : ∀ (x : X) (j : K' → L.ι), x ∈ LB.wchart L (fun _ : K' => 𝟙 X) j →
      gs (𝟙 X) x _ (s'.f j) = gs (𝟙 X) x _ (s.f fun _ => j default) := fun x j hx => gs_res (𝟙 X) x (le j) hx _
  refine ⟨s', nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y j hj => ?_,
    fun x i hx => hs x _ ((mem_wchart_oneTerm default).2 hx)⟩
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j default, (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hj)⟩
  · rw [hs y j hj]
    exact (mem_nonzeroLocus_iff_isUnit s (le j hj)).symm

theorem sec_extend_of_nonzeroLocus : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (N : ℕ) (s : H0 L N), (∀ a : Γ(X, nonzeroLocus s), ∃ (m : ℕ) (t : H0 L (N * m)), ∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = Geo.Tor.gs (𝟙 X) x _ (s.f j) ^ m * Geo.Tor.gs (𝟙 X) x _ a) ∧ ∀ (n : ℕ) (t : H0 L n), (∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = 0) → ∃ m : ℕ, ∀ j : Fin 1 → L.ι, (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from s.f j) ^ m * (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from t.f j) = 0 := by
  intro X _ _ L hL N s
  have hj : ∀ j : Fin 1 → L.ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
  have hJ : ∀ j : PUnit.{1} → L.ι, ∃ i, j = fun _ => i := fun j => ⟨j PUnit.unit, rfl⟩
  obtain ⟨s', hl, hs⟩ : ∃ s' : (lbPow L N).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn s' fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) :=
    exists_sec_oneTerm L (K' := PUnit) rfl s
  refine ⟨fun a => ?_, fun n t ht => ?_⟩
  · obtain ⟨m, hm⟩ := exists_sec_eq_pow_mul (m := 0) hL s' (fun J => resG X (inf_le_left.trans hl.le) a)
      (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' h hJ hJ' => by
        rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
        exact (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ⟩ a).trans
          (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ'⟩ a).symm)
    obtain ⟨u, hu⟩ := hm m le_rfl
    obtain ⟨t, -, ht⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((N * m : ℕ) : ℤ)) (by rw [zero_add]) u
    refine ⟨m, t, fun x j hx hxj => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hy : x ∈ nonzeroLocus s' ⊓ powChart L (fun _ => i) := ⟨hl.ge hx, mem_powChart.2 hxj⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, gs_res _ x _ hy, hs x i hxj] at e
    exact (ht x i hxj).trans e
  · obtain ⟨t', -, ht'⟩ : ∃ t' : (lbPow L n).Sec, nonzeroLocus t' = nonzeroLocus t ∧
        ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn t' fun _ => i) = gs (𝟙 X) x _ (t.f fun _ => i) :=
      exists_sec_oneTerm L (K' := PUnit) rfl t
    obtain ⟨m, hm⟩ := exists_pow_mul_powFn_eq_zero hL s' t' fun J => fn_ext fun y hy => by
      obtain ⟨i, rfl⟩ := hJ J
      rw [gs_res _ y _ hy, gs_zero _ y _ hy, ht' y i (mem_powChart.1 hy.2)]
      exact ht y _ (hl.le hy.1) (mem_powChart.1 hy.2)
    refine ⟨m, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hi : y ∈ L.U i := (mem_wchart_oneTerm (j := fun _ : Fin 1 => i) 0).1 hy
    have hp : y ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have e := congrArg (gs (𝟙 X) y _) (hm fun _ => i)
    rw [gs_mul _ y _ hp, gs_pow _ y _ hp, gs_zero _ y _ hp, hs y i hi, ht' y i hi] at e
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_zero _ y _ hy]
    exact e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaActionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∃ m : {g : GtPtF D (Kbar V) // GtTors D N g} → (TFK (R := V) (Kbar V) ⟶ A.A), Function.Injective m ∧ (∀ g, U.Acts (Kbar V) N 0 g.1 (m g)) ∧ ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') := by
  first | exact @GlobalTheory.UU.Eqv.main | exact GlobalTheory.UU.Eqv.main | (intros; apply GlobalTheory.UU.Eqv.main <;> assumption)
end

