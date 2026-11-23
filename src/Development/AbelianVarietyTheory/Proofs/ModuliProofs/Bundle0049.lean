module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationOfFibreOfKillsBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.VertFib

abbrev epsPt : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

abbrev epsStr : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ))

def ringVal {A : Type} [CommRing A] {X : Scheme.{0}} (v : Sp A ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((v.appLE W ⊤ h).hom f)

theorem epsPt_epsStr : epsPt ≫ epsStr = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem top_le_of_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W) : ⊤ ≤ v ⁻¹ᵁ W := by
  intro q _
  have hq : (q : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro x hx
    have hx0 : TrivSqZeroExt.fst x = 0 := hx
    apply q.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two]; ext <;> simp [hx0]
    rw [this]; exact q.asIdeal.zero_mem
  obtain ⟨s, rfl⟩ := hq
  exact h (Set.mem_univ s)

theorem top_le_epsPt {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) : ⊤ ≤ (epsPt ≫ v) ⁻¹ᵁ W := fun _ _ => h (Set.mem_univ _)

theorem ringVal_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (O : Y.Opens)
    (e : O ≤ m ⁻¹ᵁ W) (h : ⊤ ≤ v ⁻¹ᵁ O) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v O h ((m.appLE W O e).hom f) = ringVal (v ≫ m) W h' f := by
  rw [ringVal, ringVal, ← CommRingCat.comp_apply (m.appLE W O e), Scheme.Hom.appLE_comp_appLE]

theorem ringVal_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ (m ⁻¹ᵁ W)) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v (m ⁻¹ᵁ W) h ((m.app W).hom f) = ringVal (v ≫ m) W h' f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ringVal_appLE v m W _ _ h h' f

theorem ringVal_spMap {A R : Type} [CommRing A] [CommRing R] (φ : R →+* A) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (s : Γ(Sp R, ⊤)) :
    ringVal (spMap φ) ⊤ h s = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 := congrArg (fun g => g.hom s) h1
  have h3 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
  rw [ringVal, h3]
  exact h2

theorem ringVal_congr {A : Type} [CommRing A] {X : Scheme.{0}} {v v' : Sp A ⟶ X} (e : v = v') (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v' ⁻¹ᵁ W) (f : Γ(X, W)) : ringVal v W h f = ringVal v' W h' f := by
  subst e; rfl

theorem ringVal_constFn {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}} (v : Sp A ⟶ X) (p : X ⟶ Sp R)
    (φ : R →+* A) (hv : v ≫ p = spMap φ) (h : ⊤ ≤ v ⁻¹ᵁ ⊤) (r : R) :
    ringVal v ⊤ h (constFn p ⊤ r) = φ r := by
  refine (ringVal_appLE v p ⊤ ⊤ le_top h le_top _).trans ?_
  refine (ringVal_congr hv ⊤ _ le_top _).trans ((ringVal_spMap φ _ _).trans ?_)
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r

theorem snd_ringVal_const {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (W : X.Opens) (h : ⊤ ≤ (epsStr ≫ z) ⁻¹ᵁ W) (f : Γ(X, W)) :
    TrivSqZeroExt.snd (ringVal (epsStr ≫ z) W h f) = 0 := by
  have hz : ⊤ ≤ z ⁻¹ᵁ W := by
    have := top_le_epsPt _ W h
    rwa [← Category.assoc, epsPt_epsStr, Category.id_comp] at this
  exact congrArg TrivSqZeroExt.snd
    ((ringVal_appLE epsStr z W ⊤ hz le_top h f).symm.trans (ringVal_spMap _ _ _))

theorem comp_eq_const {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (v ≫ p)
  have hφ : v ≫ p = spMap ψ.hom := hψ.symm
  rw [hφ, ← Spec.map_comp] at h₁
  have h₃ := Spec.map_injective h₁
  rw [hφ, ← Spec.map_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  have h₄ : TrivSqZeroExt.snd (ψ.hom r : DualNumber ℂ) = 0 :=
    (congrArg TrivSqZeroExt.snd (ringVal_constFn v p ψ.hom hφ le_top r)).symm.trans (h₂ r)
  have h₅ : TrivSqZeroExt.fst (ψ.hom r : DualNumber ℂ) = x₀ r := congrArg (fun g => g.hom r) h₃
  exact TrivSqZeroExt.ext h₅ h₄

end GlobalTheory.KS.VertFib


open GlobalTheory.KS.VertFib in
theorem GlobalTheory.KS.ptDer_of_fibre : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  intro Y R _ x₀ X p m hP y hy
  constructor
  · intro δ hδ h0
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (_root_.GlobalTheory.KS.ptDer_iff_dualPoint X (y ≫ m)).1 δ hδ
    have hvp : v ≫ p = epsStr ≫ spMap x₀ := by
      refine comp_eq_const x₀ p v ?_ fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rw [← Category.assoc, hv, Category.assoc, hP.w, ← Category.assoc, hy, Category.id_comp]
    have hw₁ := hP.lift_fst v epsStr hvp
    have hw₂ := hP.lift_snd v epsStr hvp
    generalize hP.lift v epsStr hvp = w at hw₁ hw₂
    have hwy : epsPt ≫ w = y := by
      apply hP.hom_ext
      · rw [Category.assoc, hw₁, hv]
      · rw [Category.assoc, hw₂, epsPt_epsStr, hy]
    obtain ⟨δ₀, hδ₀, hw⟩ := (_root_.GlobalTheory.KS.ptDer_iff_dualPoint Y.left y).2 w hwy
    refine ⟨δ₀, hδ₀, fun a => ?_, fun W f hW => ?_⟩
    · refine (hw ⊤ le_top _).symm.trans ?_
      exact congrArg TrivSqZeroExt.snd (ringVal_constFn w Y.hom _ hw₂ le_top a)
    · have h1 : ⊤ ≤ v ⁻¹ᵁ W := top_le_of_epsPt v W (by rw [hv]; exact hW)
      have h2 : ⊤ ≤ (w ≫ m) ⁻¹ᵁ W := by rw [hw₁]; exact h1
      refine (hvδ W h1 f).symm.trans (Eq.trans ?_ (hw (m ⁻¹ᵁ W) h2 _))
      exact congrArg TrivSqZeroExt.snd
        ((ringVal_congr hw₁.symm W h1 h2 f).trans (ringVal_app w m W h2 h2 f).symm)
  · intro δ₀ hδ₀ h0 hm O f hO
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (_root_.GlobalTheory.KS.ptDer_iff_dualPoint Y.left y).1 δ₀ hδ₀
    have hvp : v ≫ Y.hom = epsStr := by
      have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
      have := comp_eq_const (RingHom.id ℂ) Y.hom v (by rw [← Category.assoc, hv, hy, hid])
        fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rwa [hid, Category.comp_id] at this
    have hz : PtDer (y ≫ m) (fun _ _ => 0) := ⟨by simp, by simp, by simp⟩
    have hvm : v ≫ m = epsStr ≫ y ≫ m := by
      refine ((_root_.GlobalTheory.KS.ptDer_iff_dualPoint X (y ≫ m)).1 _ hz).unique ⟨?_, fun W h g => ?_⟩ ⟨?_, fun W h g => ?_⟩
      · rw [← Category.assoc, hv]
      · have hW : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W := by
          have := top_le_epsPt _ W h
          rwa [← Category.assoc, hv] at this
        refine Eq.trans ?_ ((hvδ (m ⁻¹ᵁ W) h _).trans (hm W g hW))
        exact congrArg TrivSqZeroExt.snd (ringVal_app v m W h h g).symm
      · rw [← Category.assoc, epsPt_epsStr, Category.id_comp]
      · exact snd_ringVal_const (y ≫ m) W h g
    have hvc : v = epsStr ≫ y := by
      apply hP.hom_ext
      · rw [hvm, Category.assoc]
      · rw [hvp, Category.assoc, hy, Category.comp_id]
    have h1 : ⊤ ≤ v ⁻¹ᵁ O := top_le_of_epsPt v O (by rw [hv]; exact hO)
    refine (hvδ O h1 f).symm.trans ?_
    have h2 : ⊤ ≤ (epsStr ≫ y) ⁻¹ᵁ O := by rw [← hvc]; exact h1
    exact (congrArg TrivSqZeroExt.snd (ringVal_congr hvc O h1 h2 f)).trans (snd_ringVal_const y O h2 f)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.TangentAt

def dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    DualNumber ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)

theorem dval_comp {X Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (t : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (v ≫ t) ⁻¹ᵁ U) (V : X.Opens) (e : V ≤ t ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) (f : Γ(Y, U)) :
    dval (v ≫ t) U h f = dval v V hV ((t.appLE U V e).hom f) := by
  simp only [dval, ← Scheme.Hom.appLE_comp_appLE v t U V ⊤ e hV, CommRingCat.hom_comp, RingHom.comp_apply]

private theorem ΓSpecIso_appLE_spMap_top {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : (⊤ : (Sp S).Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Scheme.Hom.appLE (spMap φ) ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  rw [← key]
  rfl

theorem fst_dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    (dval v U h f).fst = valAt' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) U f := by
  have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := fun x _ =>
    h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  rw [valAt', dite_eq_left h', valAt, dval, ← Scheme.Hom.appLE_comp_appLE _ v U ⊤ ⊤ h (fun _ _ => trivial),
    CommRingCat.hom_comp, RingHom.comp_apply]
  exact (ΓSpecIso_appLE_spMap_top (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ _).symm

private theorem mem_prime_dualNumber_iff_fst_eq_zero (p : Ideal (DualNumber ℂ)) (hp : p.IsPrime) (x : DualNumber ℂ) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra hne
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx
      (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
  · intro h0
    have hsq : x * x = 0 := by
      ext <;> simp [h0]
    exact hp.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.zero_mem)

theorem top_le_iff_dual {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
  constructor
  · intro hv x _
    exact hv (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  · intro hv y _
    let x : ↥(Sp ℂ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have e : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x = y := by
      apply PrimeSpectrum.ext
      ext a
      exact (mem_prime_dualNumber_iff_fst_eq_zero _ (PrimeSpectrum.isPrime _) a).trans
        (mem_prime_dualNumber_iff_fst_eq_zero _ (show PrimeSpectrum (DualNumber ℂ) from y).isPrime a).symm
    have hx : v.base ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x) ∈ U := hv (Set.mem_univ x)
    rw [e] at hx
    exact hx

private theorem top_le_preimage_top' {X Y : Scheme.{0}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

theorem comp_eq_spMap {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ p = 𝟙 _)
    (h2 : ∀ a, (dval v ⊤ le_top (constFn p ⊤ a)).snd = 0) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) := by
  have hD : ∀ c : ℂ, dval (v ≫ p) ⊤ (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) =
      algebraMap ℂ (DualNumber ℂ) c := by
    intro c
    apply TrivSqZeroExt.ext
    · rw [fst_dval, h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
        show (𝟙 (Sp ℂ)) = spMap (RingHom.id ℂ) by simp [spMap],
        valAt', dite_eq_left (top_le_preimage_top' _), valAt]
      exact (ΓSpecIso_appLE_spMap_top (RingHom.id ℂ) _ _).trans (by simp)
    · rw [dval_comp v p ⊤ (top_le_preimage_top' _) ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _)]
      refine (h2 c).trans ?_
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (hD c).trans ?_
  have k := ΓSpecIso_appLE_spMap_top (algebraMap ℂ (DualNumber ℂ)) (top_le_preimage_top' _)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)
  rw [Iso.inv_hom_id_apply] at k
  exact k.symm

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

def tr (a : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex a) * 𝟙 A

theorem comp_tr {B : Over (Sp ℂ)} (x : B ⟶ A) (a : Fin g → ℂ) : x ≫ tr u a = (toUnit B ≫ u.ex a) * x := by
  rw [tr, comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit B), Category.comp_id]

theorem ex_tr (a z : Fin g → ℂ) : u.ex z ≫ tr u a = u.ex (a + z) := by
  rw [comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, u.ex_add]

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact _root_.mul_eq_left.mp h.symm

theorem tr_neg_tr (a : Fin g → ℂ) : tr u (-a) ≫ tr u a = 𝟙 A := by
  rw [comp_tr, tr, ← _root_.mul_assoc, ← comp_mul, ← u.ex_add, add_neg_cancel, ex_zero, comp_one, _root_.one_mul]

def DiffAt (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(A.left, U)),
    (dval v U h f).snd = fderiv ℂ (fun z' => valAt' (u.ex z').left U f) z w

theorem DiffAt.tr {v : Sp (DualNumber ℂ) ⟶ A.left} {z w : Fin g → ℂ} (h : DiffAt u v z w) (a : Fin g → ℂ) :
    DiffAt u (v ≫ (tr u a).left) (a + z) w := by
  have nat : ∀ {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
      (e : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)),
      valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
    intro X Y x φ U V e hx f
    have hxφ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun y hy => e (hx hy)
    rw [valAt', dite_eq_left hx, valAt', dite_eq_left hxφ, valAt, valAt, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ e hx,
      CommRingCat.hom_comp, RingHom.comp_apply]
  intro U h' f
  have hV : ⊤ ≤ v ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U) := h'
  rw [dval_comp v (TangentAt.tr u a).left U h' _ le_rfl hV f, h]
  have hfun : (fun z' => valAt' (u.ex z').left ((TangentAt.tr u a).left ⁻¹ᵁ U) (((TangentAt.tr u a).left.appLE U _ le_rfl).hom f)) =
      fun z' => valAt' (u.ex (a + z')).left U f := by
    funext z'
    by_cases hz : ⊤ ≤ (u.ex z').left ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)
    · rw [nat _ _ _ _ _ hz, ← Over.comp_left, ex_tr]
    · have hz' : ¬ ⊤ ≤ (u.ex (a + z')).left ⁻¹ᵁ U := by
        rw [← ex_tr, Over.comp_left]
        exact hz
      rw [valAt', dite_eq_right hz, valAt', dite_eq_right hz']
  rw [hfun]
  exact congrArg (fun L => L w) (fderiv_comp_add_left (𝕜 := ℂ) (f := fun y => valAt' (u.ex y).left U f) a)

theorem diffAt_iff (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) :
    DiffAt u v z w ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w := by
  constructor
  · intro h
    have h' := DiffAt.tr u h (-z)
    rwa [neg_add_cancel] at h'
  · intro h
    have h' := DiffAt.tr u h z
    rwa [add_zero, Category.assoc, ← Over.comp_left, tr_neg_tr, Over.id_left, Category.comp_id] at h'

theorem existsUnique_vector (htan : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (z : Fin g → ℂ)
    (δ : ∀ W : A.left.Opens, Γ(A.left, W) → ℂ) (hδ : PtDer (u.ex z).left δ)
    (hc : ∀ a, δ ⊤ (constFn A.hom ⊤ a) = 0) :
    ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  obtain ⟨v, ⟨hv0, hvd⟩, -⟩ := PtDual.existsUnique_point hδ
  have hv0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (u.ex z).left := hv0
  have hvd' : ∀ (W : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(A.left, W)), (dval v W h f).snd = δ W f := hvd
  have hone : (u.ex 0).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [ex_zero]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ (tr u (-z)).left =
      (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [← Category.assoc, hv0', ← Over.comp_left, ex_tr, neg_add_cancel, hone]
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ (tr u (-z)).left) ≫ A.hom = 𝟙 _ := by
    rw [← Category.assoc, h0]
    exact Over.w _
  have hc' : ∀ a, (dval (v ≫ (tr u (-z)).left) ⊤ (top_le_preimage_top' _) (constFn A.hom ⊤ a)).snd = 0 := by
    intro a
    rw [dval_comp v (tr u (-z)).left ⊤ _ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _), hvd']
    have e3 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE (tr u (-z)).left A.hom ⊤ ⊤ ⊤ (top_le_preimage_top' _)
        (top_le_preimage_top' _))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
    have key : ∀ (k : A.left ⟶ Sp ℂ) (_ : k = A.hom) (e : ⊤ ≤ k ⁻¹ᵁ ⊤),
        (k.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = constFn A.hom ⊤ a := by
      rintro _ rfl e
      rfl
    have e4 : ((tr u (-z)).left.appLE ⊤ ⊤ (top_le_preimage_top' _)).hom (constFn A.hom ⊤ a) =
        constFn A.hom ⊤ a := e3.trans (key _ (Over.w _) _)
    rw [e4]
    exact hc a
  let v'' : epsR ℂ ⟶ A := Over.homMk (v ≫ (tr u (-z)).left) (comp_eq_spMap A.hom _ h1 hc')
  have htv : IsTangent v'' := h0
  obtain ⟨w, hw, huniq⟩ := htan v'' htv
  have hdiff : ∀ w', u.IsDiff w' v'' ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w' := fun _ => Iff.rfl
  refine ⟨w, ?_, ?_⟩
  · intro O f hO
    have hv : ⊤ ≤ v ⁻¹ᵁ O := (top_le_iff_dual v O).2 (by rw [hv0']; exact hO)
    rw [← hvd' O hv f]
    exact ((diffAt_iff u v z w).2 ((hdiff w).1 hw)) O hv f
  · intro w' hw'
    apply huniq
    rw [hdiff, ← diffAt_iff]
    intro U h f
    rw [hvd' U h f]
    exact hw' U f (by rw [← hv0']; exact (top_le_iff_dual v U).1 h)

theorem tangent_at_point : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ z δ, PtDer (u.ex z).left δ → (∀ a, δ ⊤ (constFn P₀.A.hom ⊤ a) = 0) → ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hG z δ hδ hc
  obtain ⟨-, htan, -, -, -⟩ := hG
  exact existsUnique_vector u htan z δ hδ hc

end GlobalTheory.KS.TangentAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.openImmersion_comp_structure_eq_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}} {F O : Type}
    [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) :
    C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

private theorem spMap_comp_moduli_spaces {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (g : A →+* B) (g' : B →+* D) :
    spMap (g'.comp g) = spMap g' ≫ spMap g := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem Cpt.Above.exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf
    hD hβ hc hj hφ
  obtain ⟨⟨hdom, hDed⟩, -, hFrac⟩ := hD
  let _ : Algebra O'' F'' := β''.toAlgebra
  have := hdom
  have : IsDedekindDomain O'' := hDed
  have : IsFractionRing O'' F'' := hFrac
  obtain ⟨hN, -, -, hPre, hFl, hDom, hQC⟩ := GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat
    C''.proj C''.jQ_open C''.jQ_dense
  have : IsLocallyNoetherian C''.X := hN

  have hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b := by
    rw [hf, Category.assoc, spMap_comp_moduli_spaces]
  have hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over) := by
    have := a.fin
    infer_instance
  have hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, a.j_comm, hj]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ,
        spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal
    hPre hFl hDom hQC _ _ _ hq hsq
  have hπ : h ≫ a.π = f := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h2
  have hh : h ≫ C'.s = C''.s ≫ spMap b' := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h2
  clear h2 hsq hbase
  subst hπ
  obtain ⟨mu', hmu'⟩ := sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu
  refine ⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩
  · apply a.mu.2.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [← hmu', hφ, a.φ_comm]
    · have w1 := mu'.2.1.w
      have w2 := C''.m.2.1.w
      have w3 := ν'.2.1.w
      have w4 := C'.m.2.1.w
      have h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _ := by
        simpa only [Cpt.j, Category.assoc] using h1
      simp only [Category.assoc] at w1 w2 w3 w4 ⊢
      erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]
  · intro hfin
    have : IsProper C'.s := projProper O' C'.X C'.s C'.proj
    let p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b)) :=
      pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by
        rw [Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])
    have hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf := by
      apply pullback.hom_ext
      · simp only [p, Category.assoc]
        rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [p, Category.assoc]
        rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have : IsSeparated p := by
      have e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b') := pullback.lift_snd _ _ _
      have : IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b))) := by
        rw [e]
        infer_instance
      exact IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))
    rw [← hp] at hfin
    exact IsFinite.of_comp _ p

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.primeToPart_level_exists_unique_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by
  first | exact @GlobalTheory.Models.primeToPart_spec | exact GlobalTheory.Models.primeToPart_spec | (intros; apply GlobalTheory.Models.primeToPart_spec <;> assumption)
end

