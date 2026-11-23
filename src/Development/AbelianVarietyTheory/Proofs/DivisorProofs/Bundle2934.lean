module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDvrOfCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSysGlobalModels
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DenseGlue

open GlobalTheory.PicGlue GlobalTheory.CechPic

theorem cls_pull_comp {P T T' : Scheme.{0}} {W : P.Opens} {L : LB P} (hL : IsOn W L) (g : T ⟶ P)
    (hg : ∀ z, g z ∈ W) (s : T' ⟶ T) {g' : T' ⟶ P} (w : s ≫ g = g') (h : (L.pull g).IsLB)
    (h' : (L.pull g').IsLB) : cls (L.pull g') h' = CechPic.pull s (cls (L.pull g) h) := by
  subst w
  rw [← cls_pull h s (pull_isLB h s)]
  exact ((cls_eq_iff _ _).2 (isOn_pull_comp P _ _ _ L g s hL hg)).symm

theorem exists_rigidify {X P : Scheme.{0}} (p : P ⟶ X) {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {V : X.Opens} {M : LB P}
    (hM : IsOn (p ⁻¹ᵁ V) M) : ∃ M' : LB P, IsOn (p ⁻¹ᵁ V) M' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ P),
      (∀ z, g z ∈ p ⁻¹ᵁ V) → ∀ (h₁ : (M'.pull g).IsLB) (h₂ : (M.pull g).IsLB) (h₃ : (M.pull (g ≫ p ≫ e)).IsLB),
        cls _ h₁ = cls _ h₂ - cls _ h₃ := by
  have hpe := retract_section_apply p e he
  have hι : ∀ z, (p ⁻¹ᵁ V).ι z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
  have hι' : ∀ z, ((p ⁻¹ᵁ V).ι ≫ p ≫ e) z ∈ p ⁻¹ᵁ V := fun z ↦ by
    change p (e (p _)) ∈ V
    rw [hpe]
    exact z.2
  have k₁ := pull_isLB_of_isOn P _ _ M _ hM hι
  have k₂ := pull_isLB_of_isOn P _ _ M _ hM hι'
  obtain ⟨N, hN, hc⟩ := cls_surj (cls _ k₁ - cls _ k₂)
  obtain ⟨M', hM', hi⟩ := exists_isOn_of_openImmersion P _ (p ⁻¹ᵁ V).ι N hN
  rw [Scheme.Opens.opensRange_ι] at hM'
  refine ⟨M', hM', fun T g hg h₁ h₂ h₃ ↦ ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ (p ⁻¹ᵁ V).toScheme, t ≫ (p ⁻¹ᵁ V).ι = g :=
    ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι g (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg z), IsOpenImmersion.lift_fac _ _ _⟩
  have k₃ := pull_isLB_of_isOn P _ _ M' _ hM' hι
  rw [cls_pull_comp hM' _ hι t ht k₃, cls_pull_comp hM _ hι t ht k₁,
    cls_pull_comp hM _ hι' t (by rw [reassoc_of% ht]) k₂, ← map_sub, ← hc, (cls_eq_iff k₃ hN).2 hi]

theorem exists_glue_of_rigid {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (U : X.Opens) [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P}
    (he : e ≫ p = 𝟙 X) {L₀ : LB P} (h₀ : IsOn (p ⁻¹ᵁ U) L₀) (t₀ : ∃ t : LB.Gen (L₀.pull (U.ι ≫ e)), t.IsGen)
    {Ix : Type} (V : Ix → X.Opens) (hV : ∀ y, ∃ i, y ∈ V i) (L : Ix → LB P) (hL : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i))
    (t : ∀ i, ∃ t : LB.Gen ((L i).pull ((V i).ι ≫ e)), t.IsGen)
    (hi : ∀ i, LBIso ((L i).pull (p ⁻¹ᵁ (V i ⊓ U)).ι) (L₀.pull (p ⁻¹ᵁ (V i ⊓ U)).ι)) :
    ∃ N : LB P, N.IsLB ∧ ∀ i, ∃ v : Cmp (p ⁻¹ᵁ V i) N (L i), IsoOn (p ⁻¹ᵁ V i) N (L i) v := by
  have hpe := retract_section_apply p e he
  have hR : ∀ {W : X.Opens} {M : LB P}, IsOn (p ⁻¹ᵁ W) M → (∃ t : LB.Gen (M.pull (W.ι ≫ e)), t.IsGen) →
      ∃ r : RigD e M, RigOn e M r := fun {W M} hM ht ↦
    rigOn_of_triv_open P X e W M (fun a y hy ↦ by
      have : p (e y) ∈ W := hM.le a hy
      rwa [hpe] at this) ht
  obtain ⟨r₀, hr₀⟩ := hR h₀ t₀
  choose r hr using fun i ↦ hR (hL i) (t i)
  have hv : ∀ i, ∃ v : Cmp (p ⁻¹ᵁ (V i ⊓ U)) (L i) L₀, IsoOn _ (L i) L₀ v ∧
      PicGlue.Norm e _ (L i) L₀ v (r i) r₀ := fun i ↦ by
    obtain ⟨w, hw⟩ := isoOn_of_lbIso P _ (L i) L₀ (hi i)
    exact exists_norm P X p e he _ _ _ (L i) L₀ w (r i) r₀ (hL i) h₀ (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr i) hr₀
  choose v hv hn using hv
  obtain ⟨w, hw, hc⟩ := exists_cocycle U p he h₀ r₀ V L hL r v hv hn
  exact lb_glue P Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL hw hc

theorem exists_glue {X P U Q : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j)) (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {a : Q ⟶ P} {π : Q ⟶ U} (sq : IsPullback a π p j) {eU : U ⟶ Q}
    (w : eU ≫ a = j ≫ e) {L : LB Q} (hL : L.IsLB) (hrig : ∃ t : LB.Gen (L.pull eU), t.IsGen)
    (H : ∀ y : X, y ∉ Set.range j → ∃ V : X.Opens, y ∈ V ∧ ∃ M : LB P, IsOn (p ⁻¹ᵁ V) M ∧
      LBIso (M.pull ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a)) (L.pull (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι)) :
    ∃ M : LB P, M.IsLB ∧ LBIso (M.pull a) L := by
  have hpe := retract_section_apply p e he
  have : IsOpenImmersion a := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip ‹_›
  let U₀ : X.Opens := j.opensRange
  have : IsDominant U₀.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hj⟩
  have hD : a.opensRange = p ⁻¹ᵁ U₀ := by
    ext x
    change x ∈ Set.range a ↔ p x ∈ Set.range j
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨π q, by rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
    · intro hx
      obtain ⟨q, rfl⟩ : x ∈ Set.range (pullback.fst p j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      exact ⟨sq.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]⟩
  obtain ⟨L₀, h₀, i₀⟩ := exists_isOn_of_openImmersion P Q a L hL
  rw [hD] at h₀
  have ha : ∀ z, a z ∈ p ⁻¹ᵁ U₀ := fun z ↦ hD ▸ ⟨z, rfl⟩
  have k₀ := pull_isLB_of_isOn P _ _ L₀ a h₀ ha
  have c₀ : cls _ k₀ = cls L hL := (cls_eq_iff _ _).2 i₀

  have z₀ : ∀ (T : Scheme.{0}) (s : T ⟶ X), (∀ z, s z ∈ U₀) → ∀ h : (L₀.pull (s ≫ e)).IsLB, cls _ h = 0 := by
    intro T s hs h
    let κ := IsOpenImmersion.lift j s (by rintro _ ⟨z, rfl⟩; exact hs z)
    have hκ : κ ≫ j = s := IsOpenImmersion.lift_fac _ _ _
    rw [cls_pull_comp h₀ a ha (κ ≫ eU) (by rw [Category.assoc, w, reassoc_of% hκ]) k₀, c₀, pull_comp,
      ← cls_pull hL eU (pull_isLB hL eU), (cls_eq_zero_iff _).2 hrig, map_zero]
  have hse : ∀ {T : Scheme.{0}} (s : T ⟶ X) {W : X.Opens}, (∀ z, s z ∈ W) → ∀ z, (s ≫ e) z ∈ p ⁻¹ᵁ W :=
    fun s W hs z ↦ by
      change p (e (s z)) ∈ W
      rw [hpe]
      exact hs z
  have t₀ : ∃ t : LB.Gen (L₀.pull (U₀.ι ≫ e)), t.IsGen :=
    (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ L₀ _ h₀ (hse U₀.ι fun z ↦ z.2))).1 (z₀ _ U₀.ι (fun z ↦ z.2) _)
  have key : ∀ o : Option X, ∃ (V : X.Opens) (M : LB P), (∀ y, o = some y → y ∉ U₀ → y ∈ V) ∧
      (o = none → V = U₀ ∧ M = L₀) ∧ IsOn (p ⁻¹ᵁ V) M ∧ (∃ t : LB.Gen (M.pull (V.ι ≫ e)), t.IsGen) ∧
      LBIso (M.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) (L₀.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) := fun o ↦ by
    by_cases ho : ∃ y, o = some y ∧ y ∉ U₀
    swap
    · have k := pull_isLB_of_isOn P _ _ L₀ (p ⁻¹ᵁ (U₀ ⊓ U₀)).ι h₀ fun z ↦ z.2.1
      exact ⟨U₀, L₀, fun y h h' ↦ (ho ⟨y, h, h'⟩).elim, fun _ ↦ ⟨rfl, rfl⟩, h₀, t₀, (cls_eq_iff k k).1 rfl⟩
    obtain ⟨y, rfl, hy⟩ := ho
    obtain ⟨V, hyV, M, hM, iM⟩ := H y hy
    obtain ⟨M', hM', hc⟩ := exists_rigidify p he hM
    have hb : ∀ z, ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
    have kb := pull_isLB_of_isOn P _ _ M _ hM hb
    have cmp : ∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀)) → ∀ (h₁ : (M.pull g).IsLB)
        (h₂ : (L₀.pull g).IsLB), cls _ h₁ = cls _ h₂ := fun T g hg h₁ h₂ ↦ by
      let t := IsOpenImmersion.lift ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) g (by
        rintro _ ⟨z, rfl⟩
        obtain ⟨q, hq⟩ : g z ∈ a.opensRange := hD ▸ (hg z).2
        exact ⟨⟨q, show a q ∈ p ⁻¹ᵁ V from hq ▸ (hg z).1⟩, hq⟩)
      have ht : t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a = g := IsOpenImmersion.lift_fac _ _ _
      rw [cls_pull_comp hM _ hb t ht kb, (cls_eq_iff kb (pull_isLB hL _)).2 iM,
        cls_pull_comp h₀ a ha (t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) (by rw [Category.assoc, ht]) k₀, c₀, pull_comp,
        cls_pull hL]
    refine ⟨V, M', fun y' h _ ↦ by cases h; exact hyV, fun h ↦ (by cases h), hM', ?_, ?_⟩
    · have hs := hse V.ι fun z ↦ z.2
      have k₂ := pull_isLB_of_isOn P _ _ M _ hM hs
      have e₁ : (V.ι ≫ e) ≫ p ≫ e = V.ι ≫ e := by rw [Category.assoc, reassoc_of% he]
      refine (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ M' _ hM' hs)).1 ?_
      rw [hc _ _ hs _ k₂ (e₁.symm ▸ k₂), sub_eq_zero]
      exact (cls_pull_comp hM _ hs (𝟙 _) (by rw [Category.id_comp, e₁]) k₂ _).trans (pull_id _) |>.symm
    · let g := (p ⁻¹ᵁ (V ⊓ U₀)).ι
      have hg : ∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀) := fun z ↦ z.2
      have hg' : ∀ z, ((g ≫ p) ≫ e) z ∈ p ⁻¹ᵁ (V ⊓ U₀) := hse (g ≫ p) hg
      have k₁ := pull_isLB_of_isOn P _ _ M' g hM' fun z ↦ (hg z).1
      have k₂ := pull_isLB_of_isOn P _ _ M g hM fun z ↦ (hg z).1
      have k₃ := pull_isLB_of_isOn P _ _ M _ hM fun z ↦ (hg' z).1
      have k₄ := pull_isLB_of_isOn P _ _ L₀ g h₀ fun z ↦ (hg z).2
      have k₅ := pull_isLB_of_isOn P _ _ L₀ _ h₀ fun z ↦ (hg' z).2
      refine (cls_eq_iff k₁ k₄).1 ?_
      rw [hc _ g (fun z ↦ (hg z).1) k₁ k₂ k₃, cmp _ g hg k₂ k₄]
      exact sub_eq_self.2 ((cmp _ _ hg' k₃ k₅).trans (z₀ _ (g ≫ p) (fun z ↦ (hg z).2) k₅))
  choose V M h₁ h₂ h₃ h₄ h₅ using key
  obtain ⟨N, hN, hv⟩ := exists_glue_of_rigid U₀ p he h₀ t₀ V (fun y ↦ by
    by_cases hy : y ∈ U₀
    · exact ⟨none, (h₂ none rfl).1 ▸ hy⟩
    · exact ⟨some y, h₁ _ y rfl hy⟩) M h₃ h₄ h₅
  obtain ⟨v, hv⟩ := hv none
  have i₁ := lbIso_pull_of_isoOn P Q _ N (M none) v a hv fun z ↦ (h₂ none rfl).1 ▸ ha z
  rw [(h₂ none rfl).2] at i₁
  exact ⟨N, hN, (cls_eq_iff (pull_isLB hN a) hL).1 (((cls_eq_iff _ k₀).2 i₁).trans c₀)⟩

end GlobalTheory.DenseGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem exists_fibrePow_point_of_polAV : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  intro n hn hodd V _ _ _ hV hD b PB r c hc
  obtain ⟨V₁, _, _, _, f₁, s, β, β₂, d, h1, h2, h3, h4, h5, hP, hpb, hsq, hlb, hd⟩ :=
    _root_.GlobalTheory.LevelAfterExt.exists_siegPre_divPoints n hn hodd V hV hD b PB r c
  have : CharZero V₁ := h1.2.2.2
  obtain ⟨F, x, hx, hpbF⟩ := _root_.GlobalTheory.LowChart.exists_sFam_point n hn hodd PB.g V₁ (f₁.comp b) s hP
  obtain ⟨v, hs, β₁, β₁₂, p1, p2, p3, p4⟩ :=
    _root_.GlobalTheory.LowChart.exists_siegAt_of_siegPB F (spMap f₁) (spMap (f₁.comp b)) x hx s hpbF PB.A (abelian₂ PB.A PB.L) β β₂ hpb hsq hlb r d
  refine ⟨F, V₁, inferInstance, inferInstance, inferInstance, f₁, v, hs, h1, h2, h3, h4, h5, β₁, β₁₂, p1, p2, p3,
    fun a => ?_⟩
  rw [p4]
  exact _root_.GlobalTheory.DivPush.push_div_pts (spMap f₁) s.A PB.A β hpb n r d c hc hd a

end GlobalTheory.LowChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUnitaryPointGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitSemi

theorem spMap_comp'' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem exists_int_map (F : Type) [Field F] [NumberField F] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (g : F →+* FractionRing V) :
    ∃ oV : 𝓞 F →+* V, (algebraMap V (FractionRing V)).comp oV = g.comp (algebraMap (𝓞 F) F) := by
  have hint : ∀ a : 𝓞 F, ∃ r : V, algebraMap V (FractionRing V) r = g a := fun a => by
    have h2 : IsIntegral V (g a) := by
      obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom V), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap V (FractionRing V)).comp (Int.castRingHom V))
        (g.comp (algebraMap ℤ F)), ← Polynomial.hom_eval₂, h0, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h2
  choose f hf using hint
  have hi := IsFractionRing.injective V (FractionRing V)
  let b : 𝓞 F →+* V :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun _ _ => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun _ _ => hi (by simp [hf]) }
  refine ⟨b, ?_⟩
  ext a
  exact hf a

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_genOf_of_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (y : Sp (FractionRing V) ⟶ Xo.XF c) : ∃ t : SAB H (Sp V), GenOf Xo c y t := by
  obtain ⟨g, hg⟩ := GlobalTheory.Models.RankZero.exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨oV, hoV⟩ := exists_int_map c.F V g
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, hG⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c (𝓞 c.F) _ Y V (FractionRing V) oV g y hoV hg
  obtain ⟨G, ⟨m⟩⟩ := hG yt
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull y Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hy' : y ≫ Y.jQ ≫ pullback.fst _ _ = jK V ≫ yt := hyt.symm
  rw [hy'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  exact ⟨G, _, ⟨mK⟩, ⟨mx⟩⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_finite_point' {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp'']

theorem exists_closure_finite (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, RingHom.finite_algebraMap.2 inferInstance, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

theorem finite_surjective_spMap {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F'] (h : F ≤ F') :
    IsFinite (spMap (IntermediateField.inclusion h).toRingHom) ∧
      Surjective (spMap (IntermediateField.inclusion h).toRingHom) := by
  have hq : (algebraMap ℚ F').Finite := RingHom.finite_algebraMap.2 inferInstance
  have he : algebraMap ℚ F' = (IntermediateField.inclusion h).toRingHom.comp (algebraMap ℚ F) := Subsingleton.elim _ _
  rw [he] at hq
  refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_comp_finite hq), ⟨fun x => ?_⟩⟩
  refine ⟨closedPoint F', Subsingleton.elim _ _⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_rankZero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : Dw.p + Dw.q = 0) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  have hz := (GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo).2
  refine ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, RingHom.id _, ⟨hV, hB.1.2.2.2, hB.2⟩,
    Function.injective_id, inferInstance, RingHom.Finite.id V, fun a => rfl, Inhab.zeroTriple H _,
    Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _)
      (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _,
    GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _) hz _⟩

theorem exists_pos {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  haveI := c.fin
  obtain ⟨l₂, hdvd, -, hgood⟩ := GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  obtain ⟨c₂, hle⟩ := GlobalTheory.TupleCover.exists_coeff_ge l₂ c.F
  haveI := c₂.fin
  let Xf : ∀ l' : Geo.Tor.Level H, Moduli Dw l' := fun l' => (GlobalTheory.moduliScheme_levelMaps_heckePoints.1 E H Dw l' hD).some
  obtain ⟨s, hs⟩ := GlobalTheory.GlobalAllLevels.exists_sys_global_models E H Dw hD Xf
  obtain ⟨Ygl, -⟩ := hs l₂ c₂ hgood
  obtain ⟨r, h, r₀, m, hr, hfin, -, hsurj⟩ :=
    GlobalTheory.LevelMapBase.levelMap_coeff_le E H Dw l l₂ Xo (Xf l₂) c c₂ hle hD hdvd
  obtain ⟨hF, hS⟩ := finite_surjective_spMap hle
  have hrl : pullback.lift r _ h ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  haveI : IsFinite r := hrl ▸ inferInstance
  have hrs : Surjective r := hrl ▸ inferInstance
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point' r (FractionRing V) y (hrs.surj _)
  haveI : IsAdicComplete (maximalIdeal V) V := hB.1.2.2.2
  haveI : CharZero V := hB.2
  obtain ⟨V₁, _, _, _, j, e, hB₁, hD₁, hj, hjl, hjf, he⟩ := exists_closure_finite V L
  obtain ⟨t, tK, ⟨mK⟩, ⟨mx⟩⟩ := exists_genOf_of_model Ygl V₁ (spMap e ≫ η)
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mx
  have key : ((spMap e ≫ η) ≫ pullback.fst _ _) ≫ r₀ =
      (spMap (e.comp (algebraMap (FractionRing V) L)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, ← hr, ← Category.assoc η, hη, ← spMap_comp'']
    simp only [Category.assoc]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, j, e.comp (algebraMap (FractionRing V) L),
    ⟨hD₁, hB₁.1.2.2.2, hB₁.2⟩, hj, hjl, hjf, fun a => he a, t, tK, ⟨mK⟩, ⟨?_⟩⟩
  rw [key] at mx'
  exact mx'

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_ext_semi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · exact exists_rankZero H Dw hD l Xo c V hB hV y
  · exact exists_pos H Dw hD l Xo c V hB hV y

end GlobalTheory.TraitSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatEpiLiftRaynaudExtensionFractionPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RayLift

theorem exists_flat_lift (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (z : (DegPre.BF Q (FractionRing R)).left) :
    ∃ (Z : Scheme.{0}) (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (w : Z) (y : Z ⟶ Y.H.left),
      p w = z ∧ Epi p ∧ Function.Injective (p.stalkMap w).hom ∧
        y ≫ Y.q.left = p ≫ (DegPre.prB Q (FractionRing R)).left := by
  obtain ⟨hF, hS, -⟩ := GlobalTheory.Heat.Descend.q_props Y
  let p := pullback.fst (DegPre.prB Q (FractionRing R)).left Y.q.left
  have hpF : Flat p := by haveI := hF; dsimp [p]; infer_instance
  have hpS : Surjective p := by haveI := hS; dsimp [p]; infer_instance
  obtain ⟨w, hw⟩ := p.surjective z
  refine ⟨_, p, w, pullback.snd _ _, hw, Flat.epi_of_flat_of_surjective p, ?_, pullback.condition.symm⟩
  let _ := (p.stalkMap w).hom.toAlgebra
  have : Module.Flat _ _ := Flat.stalkMap p w
  have : IsLocalHom (algebraMap ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap w).hom)
  have : Module.FaithfullyFlat ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective _ _

end GlobalTheory.RayLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  first | exact @GlobalTheory.HeatValues.heat_values_at_point | exact GlobalTheory.HeatValues.heat_values_at_point | (intros; apply GlobalTheory.HeatValues.heat_values_at_point <;> assumption)
end

