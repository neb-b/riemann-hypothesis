module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem r_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 _ := rfl
  simp only [resG, this, CategoryTheory.Functor.map_id]; rfl

theorem r_appLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V) (a : Γ(X, U)) :
    resG Y h ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← f.appLE_map e (homOfLE h).op]; rfl

theorem appLE_r (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(X, U')) :
    (f.appLE U V e).hom (resG X h a) = (f.appLE U' V (e.trans (fun _ hy => h hy))).hom a := by
  rw [← f.map_appLE e (homOfLE h).op]; rfl

theorem appLE_appLE (f : Z ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = ((f ≫ g).appLE U W e).hom a := by
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂]; rfl

theorem pull_le (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j PUnit.unit) :=
  LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit

theorem le_pull (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : f ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull f).U j :=
  fun _ h => Set.mem_iInter.2 fun _ => h

theorem pull_g (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (e : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    ((M.pull f).g j j').val = (f.appLE _ _ e).hom (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  show ((∏ _k : PUnit, (res e (pullU f _ (M.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ) :
    Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem pull_inf_le (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι) :
    (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :=
  fun _ h => ⟨pull_le M f j h.1, pull_le M f j' h.2⟩

def secPull (M : LB X) (f : Y ⟶ X) (s : M.Sec) : (M.pull f).Sec where
  f j := (f.appLE _ _ (pull_le M f j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h := congrArg (f.appLE _ _ (pull_inf_le M f j j')).hom (s.compat (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul] at h
    erw [← pull_g M f j j'] at h
    erw [appLE_r, appLE_r] at h
    erw [r_appLE, r_appLE]
    exact h

theorem isGen_val {L : LB X} (t : L.Gen) : t.IsGen ↔ ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i).val =
    (L.g i j).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j).val :=
  forall₂_congr fun _ _ => Units.ext_iff

theorem le₁ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J : PUnit → PUnit → M.ι) :
    ((M.pull π).pull x).U J ≤ (M.pull (x ≫ π)).U (J PUnit.unit) :=
  fun _ h => le_pull M (x ≫ π) _ (pull_le M π _ (pull_le (M.pull π) x J h))

theorem le₂ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) :=
  fun _ h => le_pull (M.pull π) x (fun _ => j) (le_pull M π _ (pull_le M (x ≫ π) j h))

theorem pullpull_g (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by
  rw [pull_g (M.pull π) x J J' (pull_inf_le _ _ _ _), pull_g M π _ _ (pull_inf_le _ _ _ _)]
  exact appLE_appLE x π _ _ e _

theorem secCoord_pull {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun j => res (le₂ M π x j) (τ.s fun _ => j)⟩, (isGen_val _).2 fun j j' => ?_, fun i j e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₂ M π x j) (le₂ M π x j')))
        ((isGen_val τ).1 hτ (fun _ => j) (fun _ => j'))
      rw [map_mul] at h0
      erw [pullpull_g M π x (fun _ => j) (fun _ => j') ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _)),
        rr, r_appLE] at h0
      erw [pull_g M (x ≫ π) j j' (pull_inf_le _ _ _ _)]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₂ M π x j') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₂ M π x j)) (h i (fun _ => j) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ _ e _).symm.trans h0
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun J => res (le₁ M π x J) (τ.s (J PUnit.unit))⟩, (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₁ M π x J) (le₁ M π x J')))
        ((isGen_val τ).1 hτ (J PUnit.unit) (J' PUnit.unit))
      rw [map_mul] at h0
      erw [pull_g M (x ≫ π) (J PUnit.unit) (J' PUnit.unit) (pull_inf_le _ _ _ _), rr, r_appLE] at h0
      erw [pullpull_g M π x J J' ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _))]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₁ M π x J') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₁ M π x J)) (h i (J PUnit.unit) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ e _ _).trans h0

theorem projRep_baseChange : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  intro R R' σ _ _ φ I Z Z' s s' π M th ⟨hM, hloc, hpts⟩ hp
  refine ⟨fun i => secPull M π (th i), ⟨pull_isLB hM π, fun T _ β x v hx hv => ?_, fun T _ β v hu hF => ?_⟩,
    fun T _ x v => secCoord_pull M th π x v⟩
  · have hs : (x ≫ π) ≫ s = spMap (β.comp φ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    obtain ⟨h1, h2⟩ := hloc T (β.comp φ) (x ≫ π) v hs ((secCoord_pull M th π x v).1 hv)
    refine ⟨h1, fun F hF => ?_⟩
    have : I.map (MvPolynomial.map φ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      rw [Ideal.map_le_iff_le_comap]
      intro G hG
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact h2 G hG
    exact this hF
  · obtain ⟨y, ⟨hy, hv⟩, huniq⟩ := hpts T (β.comp φ) v hu fun G hG => by
      rw [← MvPolynomial.eval₂_map]
      exact hF _ (Ideal.mem_map_of_mem _ hG)
    have hw : y ≫ s = spMap β ≫ spMap φ := by rw [hy, spMap_comp]
    refine ⟨hp.lift y (spMap β) hw, ⟨hp.lift_snd _ _ _, (secCoord_pull M th π _ v).2 (by rw [hp.lift_fst]; exact hv)⟩, ?_⟩
    rintro x ⟨hx, hxv⟩
    apply hp.hom_ext
    · rw [hp.lift_fst]
      refine huniq _ ⟨?_, (secCoord_pull M th π x v).1 hxv⟩
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    · rw [hp.lift_snd, hx]

end GlobalTheory.ZM.RepBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocally
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.LocalCoord

theorem appLE_resG {X Y : Scheme.{0}} (x : Y ⟶ X) {U U' : X.Opens} (hU : U' ≤ U) {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U')
    (a : Γ(X, U)) : (x.appLE U' V h).hom (resG X hU a) = (x.appLE U V (h.trans (x.preimage_mono hU))).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem resG_appLE {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem res_val_lemma {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := by
  rfl

private theorem res_pullU_val_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : ((res h (pullU f W u) : Γ(Y, V)ˣ) : Γ(Y, V)) = (f.appLE W V h).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_U_le_preimage_U {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) (k : PUnit) :
    (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j k) := by
  intro y hy
  have hy' : y ∈ ⋂ k, f ⁻¹' (M.U (j k) : Set X) := hy
  exact Set.mem_iInter.1 hy' k

private theorem resG_app_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)) : resG Y h ((f.app W).hom u) = (f.appLE W V h).hom u := by
  rfl

private theorem pullU_val_eq_app {X Y : Scheme.{0}} (f : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    ((pullU f W u : Γ(Y, f ⁻¹ᵁ W)ˣ) : Γ(Y, f ⁻¹ᵁ W)) = (f.app W).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_g_lemma_6 {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull f).g j j' : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ) : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')) =
      (f.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp only [Fintype.prod_unique, zpow_one]
  rfl

private theorem resG_eq_presheaf_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG X h a = (X.presheaf.map (homOfLE h).op).hom a := by
  rfl

theorem exists_secCoord_of_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) {I : Type} (th : I → M.Sec)
    {R : Type} [CommRing R] (x : Sp R ⟶ X) (j₀ : M.ι) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U j₀) : ∃ v, SecCoord M th x v := by
  have hV : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U j₀) := by
    intro j y hy
    exact ⟨pull_U_le_preimage_U M x j PUnit.unit hy, h₀ trivial⟩
  let τ : (M.pull x).Gen := ⟨fun j => res (hV j) (pullU x _ (M.g (j PUnit.unit) j₀))⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE (M.U j₀) ⊤ h₀).hom ((th i).f j₀)), τ, ?_, ?_⟩
  · intro j j'
    apply Units.ext
    have hc := congrArg Units.val (hM.cocycle (j PUnit.unit) (j' PUnit.unit) j₀)
    simp only [Units.val_mul, res_val_lemma] at hc
    have hT : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) ⊓ M.U j₀) := by
      intro y hy
      exact ⟨⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩, h₀ trivial⟩
    have hc' := congrArg (x.appLE _ _ hT).hom hc
    rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at hc'
    have hjj : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) := by
      intro y hy
      exact ⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩
    simp only [τ, Units.val_mul, res_val_lemma, pullU_val_eq_app, resG_app_eq_appLE, resG_appLE, pull_g_lemma_6 M x j j' hjj]
    exact hc'.symm
  · intro i j h
    have hf := (th i).compat (j PUnit.unit) j₀
    simp only [τ, res_pullU_val_eq_appLE]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, resG_appLE,
      ← appLE_resG x (inf_le_left : M.U (j PUnit.unit) ⊓ M.U j₀ ≤ _) (hV j), resG_eq_presheaf_map, hf, map_mul,
      ← resG_eq_presheaf_map, appLE_resG, mul_comm]

theorem exists_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) (p : X) : ∃ j, p ∈ M.U j := by
  have hp : p ∈ (⨆ i, M.U i) := by
    rw [hM.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hp

theorem secCoord_local : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  intro X M I th hM
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _ x
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x (IsLocalRing.closedPoint R))
    refine exists_secCoord_of_chart M hM th x j₀ ?_
    intro y _
    exact (IsLocalRing.specializes_closedPoint (R := R) y).mem_open (x ⁻¹ᵁ M.U j₀).isOpen hj
  · intro R _ x p
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x p)
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := (p : PrimeSpectrum R)) hj
        (x ⁻¹ᵁ M.U j₀).isOpen
    refine ⟨f, hpf, exists_secCoord_of_chart M hM th _ j₀ ?_⟩
    intro y _
    have hy : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (show PrimeSpectrum (Localization.Away f) from y) ∈
        ((PrimeSpectrum.basicOpen (f : R) : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) (f : R)]
      exact ⟨_, rfl⟩
    exact hsub hy
  · intro p
    obtain ⟨j₀, hj⟩ := exists_chart M hM p
    obtain ⟨V, hV, hpV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hj
    have hV' : IsAffineOpen V := hV
    obtain ⟨v, hv⟩ := exists_secCoord_of_chart M hM th (R := Γ(X, V)) hV'.fromSpec j₀ (by
      intro y _
      apply hVU
      have h1 : hV'.fromSpec y ∈ Set.range hV'.fromSpec := ⟨y, rfl⟩
      rw [hV'.range_fromSpec] at h1
      exact h1)
    refine ⟨Γ(X, V), inferInstance, hV'.fromSpec, v, inferInstance, ?_, hv⟩
    rw [hV'.range_fromSpec]
    exact hpV

end GlobalTheory.ZM.LocalCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfIndependentAndTangentBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.GenericSmooth

theorem le_ringKrullDim_of_mem_minimalPrimes (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  let K := FractionRing (S ⧸ q)
  let ψ : S →ₐ[o] K := (IsScalarTower.toAlgHom o (S ⧸ q) K).comp (Ideal.Quotient.mkₐ o q)
  let φ : R →ₐ[o] K := ψ.comp (IsScalarTower.toAlgHom o R S)
  have hψ : ∀ s, ψ s = 0 ↔ s ∈ q := fun s ↦ by
    change algebraMap (S ⧸ q) K (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker φ = q.under R := by
    ext r
    exact hψ (algebraMap R S r)
  have hmin : RingHom.ker φ ∈ minimalPrimes R := by
    have h' := IsLocalization.minimalPrimes_map
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S ⊥
    rw [Ideal.map_bot] at h'
    rw [hker]
    exact h'.le hq
  have hs : ∀ s : S, ∃ a b, φ b ≠ 0 ∧ ψ s = φ a / φ b := fun s ↦ by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) s
    have hb : φ b ≠ 0 := ((IsLocalization.map_units S b).map ψ).ne_zero
    refine ⟨a, b, hb, ?_⟩
    rw [eq_div_iff hb]
    have := congrArg ψ hab
    rw [map_mul] at this
    exact this
  have hsurj : ∀ z : K, ∃ a b, z = φ a / φ b := fun z ↦ by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, hb, h₁⟩ := hs x
    obtain ⟨a', b', hb', h₂⟩ := hs y
    refine ⟨a * b', b * a', ?_⟩
    change ψ x / ψ y = _
    rw [h₁, h₂, map_mul, map_mul, div_div_div_eq]
  obtain ⟨y, hy⟩ := h K φ hmin hsurj
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (S ⧸ q)
  have hk : AlgebraicIndependent k y := by
    have : Algebra.IsAlgebraic o k := IsLocalization.isAlgebraic k (nonZeroDivisors o)
    exact hy.extendScalars k
  have h₃ := hk.cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic (S ⧸ q) K := IsLocalization.isAlgebraic K (nonZeroDivisors (S ⧸ q))
  have : FaithfulSMul k (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (S ⧸ q)).injective
  rw [← trdeg_add_eq k (S ⧸ q) (A := K), trdeg_eq_zero (R := S ⧸ q) (A := K), add_zero, h₂,
    Cardinal.mk_fin] at h₃
  rw [h₁]
  exact_mod_cast h₃

theorem finrank_derivation_le (o k R S C : Type) [CommRing o] [CommRing k]
    [CommRing R] [CommRing S] [Field C] [Algebra o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    (M : Submonoid R) [IsLocalization M S] [Algebra.FiniteType o R]
    [Algebra k C] [Algebra S C] [IsScalarTower k S C] [Algebra o C] [Algebra R C]
    [IsScalarTower o R C] [IsScalarTower R S C] [IsScalarTower o S C] [IsScalarTower o k C] :
    Module.finrank C (Derivation k S C) ≤ Module.finrank C (Derivation o R C) := by
  have : Module.Finite C (Derivation o R C) :=
    Module.Finite.equiv (GlobalTheory.SmoothTangent.derivationEquivDual o R C).symm
  let f : Derivation k S C →ₗ[C] Derivation o R C :=
    { toFun := fun D ↦ (D.restrictScalars o).compAlgebraMap R
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro D hD
  have h0 : ∀ r, D (algebraMap R S r) = 0 := fun r ↦ congr($hD r)
  ext s
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M s
  have := congrArg D hab
  rw [D.leibniz, h0, h0, smul_zero, zero_add, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this).resolve_left
    ((IsLocalization.map_units S b).map (algebraMap S C)).ne_zero

end GlobalTheory.GenericSmooth

namespace GlobalTheory


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le :
    ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  intro o _ _ em R _ _ d hem hft hind htan
  let e : FractionRing o →+* ℂ := IsFractionRing.lift hem
  have : CharZero (FractionRing o) := e.charZero
  have := IsLocalization.tensorRight (S := R) (FractionRing o) (nonZeroDivisors o)
  refine smoothOfRelativeDimension_of_dim_of_finrank_derivation_le (FractionRing o) e _ d
    inferInstance
    (GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes o (FractionRing o) R _ d hind) ?_
  intro _ _ _ he
  let : Algebra o ℂ := em.toAlgebra
  let : Algebra R ℂ :=
    ((algebraMap (FractionRing o ⊗[o] R) ℂ).comp (algebraMap R _)).toAlgebra
  have h₁ : IsScalarTower o (FractionRing o) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [he]
    exact (IsFractionRing.lift_algebraMap hem x).symm
  have h₂ : IsScalarTower o (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply o (FractionRing o) ℂ,
      IsScalarTower.algebraMap_apply (FractionRing o) (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o (FractionRing o) (FractionRing o ⊗[o] R)]
  have h₃ : IsScalarTower R (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun _ ↦ rfl
  have h₄ : IsScalarTower o R ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o R (FractionRing o ⊗[o] R),
      ← IsScalarTower.algebraMap_apply o (FractionRing o ⊗[o] R) ℂ]
  exact (GenericSmooth.finrank_derivation_le o (FractionRing o) R _ ℂ
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))).trans (htan rfl)

end GlobalTheory
end

