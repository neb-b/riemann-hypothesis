module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LBGerm

theorem ratMap_gs_appLE {Z S : Scheme.{0}} (r : Z ⟶ S) (U : S.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (w : Z) (a : Γ(S, U)) :
    gs r w U a = gs (𝟙 Z) w ⊤ ((r.appLE U ⊤ h).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Z) w h trivial, gs_pull (𝟙 Z) r w U (h trivial) a,
    Category.id_comp]

theorem ratMap_eq_of_gs_eq {T S : Scheme.{0}} (g₁ g₂ : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
    (h₁ : ∀ w, g₁ w ∈ U) (h₂ : ∀ w, g₂ w ∈ U) (h : ∀ (a : Γ(S, U)) (w : T), gs g₁ w U a = gs g₂ w U a) :
    g₁ = g₂ := by
  have hf : ⊤ ≤ g₁ ⁻¹ᵁ U := fun w _ => h₁ w
  have hg : ⊤ ≤ g₂ ⁻¹ᵁ U := fun w _ => h₂ w
  have key : ∀ (r : T ⟶ S) (hr : ⊤ ≤ r ⁻¹ᵁ U),
      (⊤ : T.Opens).ι ≫ r = (⊤ : T.Opens).toSpecΓ ≫ Spec.map (r.appLE U ⊤ hr) ≫ hU.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  have e : g₁.appLE U ⊤ hf = g₂.appLE U ⊤ hg := by
    ext a
    exact fn_ext fun w _ => (ratMap_gs_appLE g₁ U hf w a).symm.trans ((h a w).trans (ratMap_gs_appLE g₂ U hg w a))
  exact Scheme.hom_ext_of_forall g₁ g₂ fun w => ⟨⊤, trivial, by rw [key g₁ hf, key g₂ hg, e]⟩

theorem ratMap_gs_ofRingHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (θ : Γ(X, U) →+* Γ(Y, V)) {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z) :
    (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w ∈ U ∧ ∀ b : Γ(X, U),
      gs (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w U b = gs (u ≫ V.ι) w V (θ b) := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) z))
  have h : ⊤ ≤ (u ≫ V.ι) ⁻¹ᵁ V := fun z _ => (u z).2
  refine ⟨h' trivial, fun b => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop := by
    have e := Scheme.Hom.appLE_comp_appLE (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl
    rw [show (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop from Scheme.Hom.appLE_eq_app (f := u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) (U := ⊤)] at e
    simpa only [Category.assoc] using e.symm
  have h3 : (u ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ u.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE u V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
    exact Scheme.Hom.appLE_eq_app (f := u) (U := ⊤)
  have h4 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom θ ≫ (u ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  rw [ratMap_gs_appLE _ U h' w b, ratMap_gs_appLE _ V h w (θ b), h4]
  rfl

theorem ratMap_gs_eval₂ {K : Type} [CommRing K] {Z S S' : Scheme.{0}} {Idx : Type} (g₁ : Z ⟶ S) (g₂ : Z ⟶ S')
    {U₁ : S.Opens} {U₂ : S'.Opens} (w : Z) (hw₁ : g₁ w ∈ U₁) (hw₂ : g₂ w ∈ U₂) (f₁ : K →+* Γ(S, U₁))
    (f₂ : K →+* Γ(S', U₂)) (r₁ : Idx → Γ(S, U₁)) (r₂ : Idx → Γ(S', U₂))
    (hc : ∀ a, gs g₁ w U₁ (f₁ a) = gs g₂ w U₂ (f₂ a)) (hr : ∀ l, gs g₁ w U₁ (r₁ l) = gs g₂ w U₂ (r₂ l))
    (P : MvPolynomial Idx K) :
    gs g₁ w U₁ (MvPolynomial.eval₂Hom f₁ r₁ P) = gs g₂ w U₂ (MvPolynomial.eval₂Hom f₂ r₂ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂Hom_C]; exact hc a
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), gs_add _ _ _ hw₁, gs_add _ _ _ hw₂, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, gs_mul _ _ _ hw₁, gs_mul _ _ _ hw₂, hp, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', hr n]

theorem ratMap_gs_cst {K : Type} [CommRing K] {Z S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of K)) (g : Z ⟶ S)
    (U : S.Opens) (w : Z) (hw : g w ∈ U) (a : K) :
    gs g w U (AbLaw.cst p U a) = gs (g ≫ p) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  rw [AbLaw.cst, RingHom.comp_apply, RingHom.comp_apply, AbLaw.rs, gs_res g w le_top hw]
  exact gs_pull g p w ⊤ trivial _

theorem ratMap_key {A X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : A ⟶ X) {k k' m : ℕ}
    (σ : Fin (m + 1) → H0 L k) (hcov : ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) (s₀ : H0 L k) (t₀ : H0 L k')
    (t : Fin (m + 1) → H0 L k') (i₀ : Fin (m + 1)) (r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i₀)))
    (hr : ∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i₀) → π a ∈ secChart L c →
      secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r j) * secGerm π a (σ i₀) c)
    (c : Fin 1 → L.ι) (g z : Z ⟶ A) (w : Z) (hc : (g ≫ π) w ∈ secChart L c)
    (ht₀ : IsUnit (secGerm (g ≫ π) w t₀ c)) (hti : IsUnit (secGerm (g ≫ π) w (t i₀) c))
    (hrat : ∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) :
    z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ (l : Fin (m + 1)) (ρ : Z.presheaf.stalk w),
      ρ * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c →
        gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l) = ρ := by
  obtain ⟨l₀, hl₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z w ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := exists_chart hL (π (z w))
  let c' : Fin 1 → L.ι := fun _ => j
  have hc' : (z ≫ π) w ∈ secChart L c' := Set.mem_iInter.2 fun _ => hj
  have germ := fun i => secRatioEq_iff_germ.1 (hrat i) w c' c hc' hc
  have uσ : IsUnit (secGerm (z ≫ π) w (σ l₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ l₀) (z ≫ π) w hc').1 hl₀
  have us₀ : IsUnit (secGerm (z ≫ π) w s₀ c') := by
    have h := uσ.mul ht₀
    rw [germ l₀] at h
    exact isUnit_of_mul_isUnit_left h
  have uσi : IsUnit (secGerm (z ≫ π) w (σ i₀) c') := by
    have h := us₀.mul hti
    rw [← germ i₀] at h
    exact isUnit_of_mul_isUnit_left h
  have hD : z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (z ≫ π) w hc').2 uσi
  refine ⟨hD, fun l ρ hρ => ?_⟩
  have hrl := congrArg (z.stalkMap w).hom (hr l c' (z w) hD hc')
  rw [map_mul, ← secGerm_comp z π w _ hc', ← secGerm_comp z π w _ hc', ← gs_stalkMap z w _ hD] at hrl
  refine (us₀.mul hti).mul_right_cancel ?_
  linear_combination (-(gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l))) * germ i₀ + (-(secGerm (g ≫ π) w t₀ c)) * hrl +
    germ l + (-(secGerm (z ≫ π) w s₀ c')) * hρ

theorem exists_morphism_of_secRatio : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  intro K _ A _ X L hL π k k' m σ hva s₀ t₀ t ⟨a, ha⟩ Y x y hdom hrat
  haveI := hdom
  obtain ⟨hcov, hloc⟩ := hva
  obtain ⟨q, hq⟩ := x.left.denseRange.exists_mem_open (π ⁻¹ᵁ nonzeroLocus t₀).isOpen ⟨a, ha⟩
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show y.left q ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hloc i₀
  obtain ⟨jx, hjx⟩ := exists_chart hL (π (x.left q))
  obtain ⟨jy, hjy⟩ := exists_chart hL (π (y.left q))
  let c : Fin 1 → L.ι := fun _ => jx
  let c' : Fin 1 → L.ι := fun _ => jy
  have hcx : (x.left ≫ π) q ∈ secChart L c := Set.mem_iInter.2 fun _ => hjx
  have hcy : (y.left ≫ π) q ∈ secChart L c' := Set.mem_iInter.2 fun _ => hjy
  have e := secRatioEq_iff_germ.1 (hrat i₀) q c' c hcy hcx
  have u1 : IsUnit (secGerm (y.left ≫ π) q (σ i₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (y.left ≫ π) q hcy).1 hi₀
  have u2 : IsUnit (secGerm (x.left ≫ π) q t₀ c) := (GlobalTheory.mem_nonzeroLocus_iff_pull t₀ (x.left ≫ π) q hcx).1 hq
  have u3 : IsUnit (secGerm (x.left ≫ π) q (t i₀) c) := by
    have h := u1.mul u2
    rw [e] at h
    exact isUnit_of_mul_isUnit_right h
  let W₀ : A.left.Opens := π ⁻¹ᵁ secChart L c
  let b : H0 L k' → Γ(A.left, W₀) := fun s => (π.app (secChart L c)).hom (s.f c)
  let V : A.left.Opens := A.left.basicOpen (b t₀ * b (t i₀))
  have hVW : V ≤ W₀ := A.left.basicOpen_le _
  have hb : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ W₀) (s : H0 L k'),
      gs g w W₀ (b s) = secGerm (g ≫ π) w s c := fun g w hw s => gs_pull g π w _ hw _
  have memV : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z), g w ∈ V → (g ≫ π) w ∈ secChart L c ∧
      IsUnit (secGerm (g ≫ π) w t₀ c) ∧ IsUnit (secGerm (g ≫ π) w (t i₀) c) := by
    intro Z g w hw
    have hW : g w ∈ W₀ := hVW hw
    have h := (GlobalTheory.LBGerm.isUnit_gs_iff g w W₀ hW _).2 hw
    rw [gs_mul g w W₀ hW, hb g w hW, hb g w hW] at h
    exact ⟨hW, isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  have hxq : x.left q ∈ V :=
    (GlobalTheory.LBGerm.isUnit_gs_iff x.left q W₀ hcx (b t₀ * b (t i₀))).1
      (by rw [gs_mul _ q W₀ hcx, hb _ q hcx, hb _ q hcx]; exact u2.mul u3)
  have hu : IsUnit ((A.left.presheaf.map (homOfLE hVW).op).hom (b (t i₀))) := by
    have h := A.left.toRingedSpace.isUnit_res_basicOpen (b t₀ * b (t i₀))
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let ρ : Fin (m + 1) → Γ(A.left, V) := fun l =>
    (A.left.presheaf.map (homOfLE hVW).op).hom (b (t l)) * ↑hu.unit⁻¹
  have hρ : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ V) (l : Fin (m + 1)),
      gs g w V (ρ l) * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c := by
    intro Z g w hw l
    have hW : g w ∈ W₀ := hVW hw
    have one : gs g w V 1 = 1 := by rw [gs_eq g w V hw, map_one, map_one]
    rw [← hb g w hW, ← hb g w hW, ← gs_res g w hVW hw (b (t i₀)), ← gs_res g w hVW hw (b (t l)),
      gs_mul g w V hw, _root_.mul_assoc, ← gs_mul g w V hw, hu.val_inv_mul, one, _root_.mul_one]
  let ev := MvPolynomial.eval₂Hom (AbLaw.cst A.hom (π ⁻¹ᵁ nonzeroLocus (σ i₀))) r
  let ev' := MvPolynomial.eval₂Hom (AbLaw.cst A.hom V) ρ
  have transfer : ∀ {Z : Scheme.{0}} (g z : Z ⟶ A.left) (w : Z), g w ∈ V → g ≫ A.hom = z ≫ A.hom →
      (∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) →
      z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs g w V (ev' P) = gs z w _ (ev P) := by
    intro Z g z w hw hp hrt
    obtain ⟨hc, h0, hi⟩ := memV g w hw
    obtain ⟨hzD, hR⟩ := ratMap_key hL π σ hcov s₀ t₀ t i₀ r hr c g z w hc h0 hi hrt
    refine ⟨hzD, ratMap_gs_eval₂ g z w hw hzD _ _ ρ r (fun a => ?_) (fun l => (hR l _ (hρ g w hw l)).symm)⟩
    rw [ratMap_gs_cst A.hom g V w hw, ratMap_gs_cst A.hom z _ w hzD, hp]
  have hker : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    apply app_injective_of_isDominant x.left V
    rw [map_zero]
    refine fn_ext fun w hw => ?_
    have tr := transfer x.left y.left w hw ((Over.w x).trans (Over.w y).symm) hrat
    rw [gs_pull (𝟙 _) x.left w V hw, Category.id_comp, tr.2 P, hP, GlobalTheory.LBGerm.gs_zero _ _ _ tr.1,
      GlobalTheory.LBGerm.gs_zero _ _ _ hw]
  let θ := (RingHom.liftOfSurjective ev hsurj) ⟨ev', hker⟩
  have hθ : ∀ P, θ (ev P) = ev' P := RingHom.liftOfSurjective_comp_apply ev hsurj ⟨ev', hker⟩
  let f₀ : V.toScheme ⟶ A.left := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hD.fromSpec
  have hf₀ : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ f₀) w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧
      ∀ P, gs (u ≫ f₀) w _ (ev P) = gs (u ≫ V.ι) w V (ev' P) := fun u w => by
    obtain ⟨h1, h2⟩ := ratMap_gs_ofRingHom hD V θ u w
    exact ⟨h1, fun P => (h2 (ev P)).trans (by rw [hθ])⟩
  have hmem : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ V.ι) w ∈ V := fun u w => (u w).2
  have hover : f₀ ≫ A.hom = V.ι ≫ A.hom := by
    refine ratMap_eq_of_gs_eq _ _ (isAffineOpen_top (Sp K)) (fun _ => trivial) (fun _ => trivial) fun a w => ?_
    obtain ⟨a', rfl⟩ : ∃ a' : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a' = a :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, by simp⟩
    have h := hf₀ (𝟙 V.toScheme) w
    have hc := h.2 (MvPolynomial.C a')
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ratMap_gs_cst _ _ _ w h.1,
      ratMap_gs_cst _ _ _ w (hmem (𝟙 _) w)] at hc
    simpa only [Category.id_comp] using hc
  refine ⟨Over.mk (V.ι ≫ A.hom), Over.homMk V.ι rfl, Over.homMk f₀ hover, ?_, ⟨⟨x.left q, hxq⟩⟩, ?_⟩
  · exact (inferInstance : IsOpenImmersion V.ι)
  · intro Z u z hz
    apply Over.OverMorphism.ext
    change u.left ≫ f₀ = z.left
    have hz' : ∀ i, SecRatioEq L (z.left ≫ π) ((u.left ≫ V.ι) ≫ π) (σ i) s₀ (t i) t₀ := hz
    have hp : (u.left ≫ V.ι) ≫ A.hom = z.left ≫ A.hom := by
      rw [Category.assoc]
      exact (Over.w u).trans (Over.w z).symm
    refine ratMap_eq_of_gs_eq _ _ hD (fun w => (hf₀ u.left w).1)
      (fun w => (transfer _ _ w (hmem u.left w) hp hz').1) fun b' w => ?_
    obtain ⟨P, rfl⟩ := hsurj b'
    exact ((hf₀ u.left w).2 P).trans ((transfer _ _ w (hmem u.left w) hp hz').2 P)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.MulPull in
theorem mulPull_gen_labCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    (C : LabCover D) (m : ℕ) :
    ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      u.IsGen := by
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hcube : HasGen C.P.L.L (thφ C.G (x3 C.G)) thε := ⟨C.P.c.t, C.P.c.isGen⟩
  have hrig : HasGen C.P.L.L (K := PUnit) (fun _ => eSec C.G) (fun _ => 1) := ⟨C.P.L.rig, C.P.L.rigGen⟩
  have hone : HasGen C.P.L.L (K := Fin 1) ![(1 : C.G ⟶ C.G).left] ![1] := by
    refine (hrig.pull (toUnit C.G).left).of_formEq hL (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  have hsym0 : HasGen C.P.L.L (K := Fin 2) ![(ι[C.G]).left, 𝟙 C.G.left] ![1, -1] := ⟨C.P.sym, C.P.sym_gen⟩
  have e1 : ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left = (ι[C.G]).left := by
    show ((𝟙 C.G) ≫ ι[C.G]).left = _
    rw [Category.id_comp]
  have e2 : (𝟙 C.G : C.G ⟶ C.G).left = 𝟙 C.G.left := rfl
  have hsym : HasGen C.P.L.L (K := Fin 2) ![(𝟙 C.G : C.G ⟶ C.G).left, ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left] ![1, -1] := by
    refine hsym0.inv.of_formEq hL (fun U _ h => ?_)
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e1, e2]
    simp only [neg_neg, zpow_one, _root_.mul_one]
    exact mul_comm _ _
  have H := hasGen_pow hL hcube (𝟙 C.G) hone hsym m
  have e3 : ((𝟙 C.G) ^ m : C.G ⟶ C.G).left = (mulA C.G m).left := by
    rw [← GlobalTheory.ZH.TorsFrame.comp_mulA]
  refine H.of_formEq hL (fun U _ h => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e2, e3]
  push_cast
  rfl


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_mulSecK (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hR : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) (m : ℕ) (_hm : Odd m) (θ₀ : SecK C.P.L.L C.α 1) :
    ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  obtain ⟨u, hu⟩ := mulPull_gen_labCover C m
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hc : (mulA C.A.A m).left ≫ C.α = C.α ≫ (mulA C.G m).left := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  let S₀ := pullMulSec θ₀ (mulA C.A.A m).left (LB.pullGen C.P.L.L _ _ u C.α) (DVR.pullGen_isGen C.P.L.L _ _ u hu C.α)
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (mulA C.A.A m).left ≫ C.α)
      (fun k : Fin 2 => C.α ≫ (![𝟙 C.G.left, (mulA C.G m).left] : Fin 2 → _) k))
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) (![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] : Fin 2 → ℤ))
      (fun _ : Fin 1 => C.α) (fun _ => ((m ^ 2 : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Category.comp_id, hc]
    simp only [Nat.cast_one, zpow_one, zpow_neg, _root_.mul_one]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨S, hS⟩ := exists_sec hL hf S₀
  refine ⟨S, u, hu, fun Z p z J hJ => ?_⟩
  rw [hS Z p z J hJ, sval_pullMulSec θ₀ _ _ _ p z hJ, val_pull hJ, mul_comm]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationModelFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem isFinite_fromNormalization_fieldPt {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] {L : Type} [Field L] [CharZero L]
    (ψ : X.presheaf.stalk (genericPoint X) ⟶ .of L) (hψ : ψ.hom.Finite) :
    IsFinite (fieldPt ψ).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hne : (U : Set X).Nonempty
  · have hη := genericPoint_mem hne
    haveI : Nonempty U := hne.to_subtype
    letI : Algebra Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) :=
      ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    letI : Algebra Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      (normFun ψ hη).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.presheaf.germ U _ hη ≫ ψ).hom.toAlgebra
    letI : Algebra X.functionField L := ψ.hom.toAlgebra
    haveI : IsScalarTower Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (app_normFun ψ hη)).symm
    haveI := functionField_isFractionRing_of_isAffineOpen X U hU
    haveI : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : FiniteDimensional X.functionField L := hψ
    haveI : CharZero X.functionField := ψ.hom.charZero
    haveI : IsIntegralClosure Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) Γ(X, U) L :=
      ⟨(normFun_spec ψ hη hU).1, fun {x} => ((normFun_spec ψ hη hU).2 x).symm⟩
    exact IsIntegralClosure.finite Γ(X, U) X.functionField L _
  · haveI : Subsingleton Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) := by
      refine subsingleton_of_forall_eq 0 fun s => ?_
      rw [← basicOpen_eq_bot_iff]
      exact eq_bot_iff.2 fun z hz => (hne ⟨_, ((fieldPt ψ).normalization.basicOpen_le s hz :)⟩).elim
    letI := ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    change Module.Finite _ _
    infer_instance

end GlobalTheory.NormCover

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem exists_normalization_model : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω]
    (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω']
    [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z),
      Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ hN
  haveI : GlobalTheory.IsNormalScheme M.Z := GlobalTheory.IsNormalScheme.of_pred hN
  haveI := M.lft
  haveI := M.sep
  haveI := M.qc
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  let ρ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω :=
    M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z)) ≫
      Scheme.stalkClosedPointTo M.pt
  have hρ : fieldPt ρ = M.pt := by
    simp only [fieldPt, ρ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt
  let ψ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω' := ρ ≫ CommRingCat.ofHom (algebraMap Ω Ω')
  have hψ : fieldPt ψ = spMap (algebraMap Ω Ω') ≫ M.pt := by
    rw [← hρ]
    simp only [fieldPt, ψ, Spec.map_comp, Category.assoc]
  have hρs : Function.Surjective ρ.hom := by
    intro x
    obtain ⟨U, f, hU, rfl⟩ := M.onto x
    have hη := genericPoint_mem hU
    refine ⟨M.Z.presheaf.germ U _ hη f, ?_⟩
    have key : ∀ (g : Sp Ω ⟶ M.Z) (_ : fieldPt ρ = g) (e : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ e ≫ (Scheme.ΓSpecIso (.of Ω)).hom = M.Z.presheaf.germ U _ hη ≫ ρ := by
      rintro _ rfl e
      exact fieldPt_appLE ρ hη
    have e := M.top_le_preimage_pt hU
    rw [valF, dite_eq_left e]
    exact (congrArg (fun g => g.hom f) (key M.pt hρ e)).symm
  have hψfin : ψ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) (RingHom.Finite.of_surjective ρ.hom hρs)
  haveI hfin : IsFinite (fieldPt ψ).fromNormalization := isFinite_fromNormalization_fieldPt ψ hψfin

  have hgen : Set.range (fieldPt ψ).toNormalization = {genericPoint (fieldPt ψ).normalization} := by
    have hc : ∀ w : Sp Ω', w = IsLocalRing.closedPoint Ω' := fun w =>
      Subsingleton.elim (α := PrimeSpectrum Ω') _ _
    have hr : Set.range (fieldPt ψ).toNormalization = {(fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        rw [hc w]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hd : closure (Set.range (fieldPt ψ).toNormalization) = Set.univ := (fieldPt ψ).toNormalization.denseRange.closure_range
    rw [hr] at hd ⊢
    have hg : IsGenericPoint ((fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')) ⊤ := hd
    rw [hg.eq (genericPoint_spec (fieldPt ψ).normalization)]
  have hpts : (fieldPt ψ).toNormalization ≫ (fieldPt ψ).fromNormalization ≫ M.s = spMap (algebraMap k Ω') := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ, Category.assoc, M.pt_s, spMap, spMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have honto : ∀ x : Ω', ∃ (U : (fieldPt ψ).normalization.Opens) (f : Γ((fieldPt ψ).normalization, U)), (U : Set (fieldPt ψ).normalization).Nonempty ∧
      valF (fieldPt ψ).toNormalization U f = x := by
    intro x
    obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint M.Z) (U := ⊤) trivial
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    letI : Algebra Γ(M.Z, U) Ω' := (M.Z.presheaf.germ U _ hηU ≫ ψ).hom.toAlgebra
    letI : Algebra M.Z.functionField Ω' := ψ.hom.toAlgebra
    haveI := functionField_isFractionRing_of_isAffineOpen M.Z U hU
    haveI : IsScalarTower Γ(M.Z, U) M.Z.functionField Ω' := .of_algebraMap_eq' rfl
    haveI : FiniteDimensional M.Z.functionField Ω' := hψfin
    obtain ⟨⟨a, ha⟩, hax⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors Γ(M.Z, U)) x
      (Algebra.IsIntegral.isIntegral (R := M.Z.functionField) x)
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hηV : genericPoint M.Z ∈ M.Z.basicOpen a := by
      refine genericPoint_mem ?_
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => ha0 ((basicOpen_eq_bot_iff a).1 (SetLike.coe_injective h))
    have hV : IsAffineOpen (M.Z.basicOpen a) := hU.basicOpen a
    let r := M.Z.presheaf.map (homOfLE (M.Z.basicOpen_le a)).op
    letI : Algebra Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) := r.hom.toAlgebra
    letI : Algebra Γ(M.Z, M.Z.basicOpen a) Ω' := (M.Z.presheaf.germ _ _ hηV ≫ ψ).hom.toAlgebra
    haveI : IsScalarTower Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' := .of_algebraMap_eq' (by
      have e : r ≫ M.Z.presheaf.germ _ _ hηV = M.Z.presheaf.germ U _ hηU := TopCat.Presheaf.germ_res _ _ _ _
      change (M.Z.presheaf.germ U _ hηU ≫ ψ).hom = (r ≫ M.Z.presheaf.germ _ _ hηV ≫ ψ).hom
      simp only [← e, Category.assoc])
    have hunit : IsUnit (r.hom a) := M.Z.toRingedSpace.isUnit_res_basicOpen a
    have hxV : IsIntegral Γ(M.Z, M.Z.basicOpen a) x := by
      have h1 : IsIntegral Γ(M.Z, M.Z.basicOpen a) (algebraMap Γ(M.Z, U) Ω' a * x) := by
        have := hax.tower_top (A := Γ(M.Z, M.Z.basicOpen a))
        rwa [Submonoid.smul_def, Algebra.smul_def] at this
      have h2 : x = algebraMap Γ(M.Z, M.Z.basicOpen a) Ω' (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) *
          (algebraMap Γ(M.Z, U) Ω' a * x) := by
        rw [IsScalarTower.algebraMap_apply Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' a, ← _root_.mul_assoc, ← map_mul]
        have : (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) * algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) a = 1 :=
          hunit.val_inv_mul
        rw [this, map_one, _root_.one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    obtain ⟨c, hc⟩ := ((normFun_spec ψ hηV hV).2 x).2 hxV
    have hW : ⊤ ≤ (fieldPt ψ).toNormalization ⁻¹ᵁ ((fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a) := by
      intro w _
      show (fieldPt ψ).fromNormalization ((fieldPt ψ).toNormalization w) ∈ M.Z.basicOpen a
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, fieldPt_apply]
      exact hηV
    refine ⟨(fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a, c,
      ⟨_, hW (x := IsLocalRing.closedPoint Ω') trivial⟩, ?_⟩
    rw [valF, dite_eq_left hW]
    exact hc
  let M' : RatModel k Ω' :=
    { Z := (fieldPt ψ).normalization
      s := (fieldPt ψ).fromNormalization ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := (fieldPt ψ).toNormalization
      pt_s := hpts
      gen := hgen
      onto := honto }
  refine ⟨M', (fieldPt ψ).fromNormalization, (GlobalTheory.IsNormalScheme.normalization_of_isIntegral (fieldPt ψ)).pred _, hfin, ?_⟩
  exact (Scheme.Hom.toNormalization_fromNormalization (fieldPt ψ)).trans hψ

end GlobalTheory.NormCover
end
end

