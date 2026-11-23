module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.PtDual

variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

def ev (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) : Γ(X, W) →+* R :=
  (v.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec v hU (isAffineOpen_top _) h
  rw [ev, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ev_ext {v v' : Sp R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U)
    (e : ev v U h = ev v' U h') : v = v' := by
  rw [← ev_fromSpec v hU h, ← ev_fromSpec v' hU h', e]

theorem exists_ev {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* R) :
    ∃ (v : Sp R ⟶ X) (h : ⊤ ≤ v ⁻¹ᵁ U), ev v U h = φ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_top
  refine ⟨_, h, ?_⟩
  have := ev_fromSpec _ hU h
  rw [cancel_mono] at this
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem ev_res (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl

theorem ev_comp (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl

abbrev pt0 : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem le_preimage_iff (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ W ↔ ⊤ ≤ (pt0 ≫ v) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    refine (p : PrimeSpectrum (DualNumber ℂ)).isPrime.mem_of_pow_mem 2 ?_
    have : x ^ 2 = 0 := by
      ext <;> simp [pow_two, hx']
    rw [this]
    exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

theorem fst_ev {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm

def derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) :
    Γ(X, W) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' y W f) + TrivSqZeroExt.inr (δ W f)
  map_one' := by
    have := hδ.mul W h 1 1
    rw [_root_.mul_one, valAt'_one y h, _root_.one_mul, left_eq_add] at this
    ext <;> simp [valAt'_one y h, this]
  map_mul' a b := by
    ext
    · simp [valAt'_mul]
    · simp [hδ.mul W h, mul_comm]
  map_zero' := by
    have := hδ.add W h 0 0
    rw [add_zero, left_eq_add] at this
    ext <;> simp [valAt'_zero, this]
  map_add' a b := by
    ext
    · simp [valAt'_add]
    · simp [hδ.add W h]

theorem fst_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).fst = valAt' y W f := by
  simp [derHom]

theorem snd_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).snd = δ W f := by
  simp [derHom]

theorem derHom_res {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {W W' : X.Opens} (e : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : derHom hδ W' h' (resG X e f) = derHom hδ W h f := by
  ext
  · rw [fst_derHom, fst_derHom, valAt'_res y e f h']
  · rw [snd_derHom, snd_derHom, hδ.res W W' e h']

theorem exists_affine (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨U, hU, (top_le_preimage_iff_mem y U).2 hy⟩

theorem ev_eq_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]

open Classical in
theorem exists_ptDer {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add (f := _), TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]

theorem existsUnique_point {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]

end GlobalTheory.KS.PtDual

namespace GlobalTheory.KS

theorem ptDer_iff_dualPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCobOfIsAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecOn GlobalTheory.AbLaw.CechOne

private lemma resG_resG_divisors {Y : Scheme.{0}} {A B C : Y.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
    (s : Γ(Y, C)) : resG Y h₁ (resG Y h₂ s) = resG Y (h₁.trans h₂) s := by
  change _ = (Y.presheaf.map ((homOfLE h₂).op ≫ (homOfLE h₁).op)).hom s
  rw [Functor.map_comp]
  rfl

private lemma resG_self_moduli {Y : Scheme.{0}} {A : Y.Opens} (h : A ≤ A) (s : Γ(Y, A)) :
    resG Y h s = s := by
  change (Y.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma rsT_eq_resG {Y : Scheme.{0}} {A B : Y.Opens} (s : Γ(Y, A)) (h : B ≤ A) :
    rsT s B = resG Y h s := by
  unfold rsT
  rw [dite_eq_left h]

private lemma triv_secOn_ext {X : Scheme.{0}} {W : X.Opens} (σ τ : SecOn (LB.triv X) W)
    (h : (show LB.secGroup (LB.triv X) W from σ).1 PUnit.unit =
      (show LB.secGroup (LB.triv X) W from τ).1 PUnit.unit) : σ = τ :=
  Subtype.ext (funext fun _ => h)

theorem isCob_of_isAffineOpen : ∀ (X : Scheme.{0}) (J : Type) (U : J → X.Opens) (c : C1 U),
    IsAffineOpen (⨆ α, U α) → IsCoc U c → IsCob U c := by
  intro X J U c hA hc

  let φ : ∀ a b, SecOn (LB.triv X) (U a ⊓ U b) := fun a b =>
    show LB.secGroup (LB.triv X) (U a ⊓ U b) from
      ⟨fun _ => resG X inf_le_left (c a b), by
        simp only [LB.secGroup, LB.triv]
        show _ ∈ secOn _ _
        simp only [secOn, Set.mem_ofPred_eq]
        intro i j
        rw [Units.val_one, map_one, _root_.one_mul, resG_resG_divisors]⟩
  have hφ : IsCocycle (LB.triv X) U φ := by
    intro a b d W ha hb hd
    apply triv_secOn_ext
    have h0 := hc a b d
    rw [rsT_eq_resG (c a b) (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)),
      rsT_eq_resG (c b d) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_eq_resG (c a d) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)] at h0
    have e := congrArg (resG X (inf_le_left.trans (le_inf (le_inf ha hb) hd) :
      W ⊓ (LB.triv X).U PUnit.unit ≤ U a ⊓ U b ⊓ U d)) h0
    rw [map_add (f := _), resG_resG_divisors, resG_resG_divisors, resG_resG_divisors] at e
    change resG X _ (resG X _ (c a b)) + resG X _ (resG X _ (c b d)) = resG X _ (resG X _ (c a d))
    rw [resG_resG_divisors, resG_resG_divisors, resG_resG_divisors]
    exact e

  obtain ⟨ψ, hψ⟩ := cechHOneVanishesOnOpen_of_isAffineOpen (LB.isLB_triv X) hA J U (fun a => le_iSup U a) le_rfl φ hφ
  refine ⟨fun i => -resG X (le_inf le_rfl le_top : U i ≤ U i ⊓ (LB.triv X).U PUnit.unit)
    ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit), ?_⟩
  intro i j
  have e := congrArg (fun σ : SecOn (LB.triv X) (U i ⊓ U j) =>
    (show LB.secGroup (LB.triv X) (U i ⊓ U j) from σ).1 PUnit.unit) (hψ i j)
  change resG X inf_le_left (c i j) =
    resG X (inf_le_inf_right _ inf_le_left) ((show LB.secGroup (LB.triv X) (U i) from ψ i).1 PUnit.unit) -
      resG X (inf_le_inf_right _ inf_le_right)
        ((show LB.secGroup (LB.triv X) (U j) from ψ j).1 PUnit.unit) at e
  have e' := congrArg (resG X (le_inf le_rfl le_top :
    U i ⊓ U j ≤ U i ⊓ U j ⊓ (LB.triv X).U PUnit.unit)) e
  rw [map_sub, resG_resG_divisors, resG_resG_divisors, resG_resG_divisors, resG_self_moduli] at e'
  rw [rsT_eq_resG _ inf_le_right, rsT_eq_resG _ inf_le_left, map_neg, map_neg, resG_resG_divisors,
    resG_resG_divisors, e']
  abel

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem isFinite_lift_comp {X X' X'' S S' S'' : Scheme.{0}} {s : X ⟶ S} {s' : X' ⟶ S'} {s'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : S'' ⟶ S'} {g'' : S'' ⟶ S} (hg : g'' = g' ≫ g) {p : X' ⟶ X} {p' : X'' ⟶ X'}
    (w : p ≫ s = s' ≫ g) (w' : p' ≫ s' = s'' ≫ g') (w'' : (p' ≫ p) ≫ s = s'' ≫ g'')
    (h : IsFinite (pullback.lift p s' w)) (h' : IsFinite (pullback.lift p' s'' w')) :
    IsFinite (pullback.lift (p' ≫ p) s'' w'') := by
  subst hg
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback s' g' ⟶ pullback s (g' ≫ g),
      θ ≫ pullback.fst s (g' ≫ g) = pullback.fst s' g' ≫ p ∧ θ ≫ pullback.snd s (g' ≫ g) = pullback.snd s' g' :=
    ⟨pullback.lift (pullback.fst s' g' ≫ p) (pullback.snd s' g')
      (by rw [Category.assoc, w, pullback.condition_assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback s (g' ≫ g) ⟶ pullback s g,
      κ ≫ pullback.fst s g = pullback.fst s (g' ≫ g) ∧ κ ≫ pullback.snd s g = pullback.snd s (g' ≫ g) ≫ g' :=
    ⟨pullback.lift (pullback.fst s (g' ≫ g)) (pullback.snd s (g' ≫ g) ≫ g')
      (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hfac : pullback.lift (p' ≫ p) s'' w'' = pullback.lift p' s'' w' ≫ θ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hθ2, pullback.lift_snd]

  have hright : IsPullback (pullback.snd s (g' ≫ g)) κ g' (pullback.snd s g) := by
    refine IsPullback.of_bot ?_ hκ2.symm (IsPullback.of_hasPullback s g).flip
    rw [hκ1]
    exact (IsPullback.of_hasPullback s (g' ≫ g)).flip

  have hsq : IsPullback θ (pullback.fst s' g') κ (pullback.lift p s' w) := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [hθ2, pullback.lift_snd]
      exact (IsPullback.of_hasPullback s' g').flip
    · apply pullback.hom_ext
      · simp only [Category.assoc, hκ1, hθ1, pullback.lift_fst]
      · simp only [Category.assoc, hκ2, reassoc_of% hθ2, pullback.lift_snd, pullback.condition]
  have hfin : IsFinite θ := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip h
  rw [hfac]
  infer_instance

theorem above_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (r : U' ⟶ U) (ν : SABMap t' t r) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (ν'' : SABMap t'' t (r' ≫ r)) (a : C'.Above C b r ν) (a' : C''.Above C' b' r' ν'), ν''.φ = ν'.φ ≫ ν.φ → ∃ a'' : C''.Above C (b'.comp b) (r' ≫ r) ν'', a''.π = a'.π ≫ a.π ∧ a''.mu.φ = a'.mu.φ ≫ a.mu.φ := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' r ν r' ν' ν'' a a' hν
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ C.t C'.t C''.t a.π a'.π a.mu a'.mu
  have hsp : spMap (b'.comp b) = spMap b' ≫ spMap b := by
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hover : (a'.π ≫ a.π) ≫ C.s = C''.s ≫ spMap (b'.comp b) := by
    rw [hsp, Category.assoc, a.π_over, ← Category.assoc, a'.π_over, Category.assoc]
  refine ⟨⟨a'.π ≫ a.π, hover, isFinite_lift_comp hsp a.π_over a'.π_over hover a.fin a'.fin, mu, ?_, ?_⟩, rfl, hmu⟩
  · rw [← Category.assoc, a'.j_comm, Category.assoc, a.j_comm, Category.assoc]
  · rw [hmu, hν, ← Category.assoc, a'.φ_comm, Category.assoc, a.φ_comm, Category.assoc]

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.HomExt

theorem exists_lift_of_range_subset {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (x : T ⟶ X) (h : Set.range x ⊆ Set.range j) : ∃ y : T ⟶ U, y ≫ j = x := by
  have hs : Function.Surjective (pullback.fst x j) := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    exact fun t ↦ h ⟨t, rfl⟩
  have hp : IsPreimmersion (pullback.fst x j) := inferInstance
  have : IsIso (pullback.fst x j) := by
    rw [isIso_iff_isIso_stalkMap]
    refine ⟨?_, isIso_stalkMap_of_flat_of_surjectiveOnStalks _⟩
    exact TopCat.isIso_of_bijective_of_isOpenMap _ ⟨hp.isEmbedding.injective, hs⟩
      (hp.isEmbedding.isInducing.isOpenMap (by rw [hs.range_eq]; exact isOpen_univ))
  exact ⟨inv (pullback.fst x j) ≫ pullback.snd x j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem field_point_comp_eq_iff {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {k : Type} [Field k]
    (c : Spec (.of k) ⟶ Z) (z : Z) (hz : z ∈ Set.range c) :
    c ≫ g = c ≫ g' ↔ Z.fromSpecResidueField z ≫ g = Z.fromSpecResidueField z ≫ g' := by
  obtain ⟨⟨w, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective c
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz ⊢
  obtain rfl : z = w := by
    obtain ⟨t, rfl⟩ := hz
    exact (Scheme.Hom.comp_apply _ _ t).trans (Scheme.fromSpecResidueField_apply w _)
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨fun t ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective _
  rw [Category.assoc, Category.assoc, cancel_epi]

theorem finite_preimage_of_finite_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : (f ⁻¹' Set.range y).Finite := by
  have hP : Finite ↥(pullback f y) := by
    refine finite_of_finite_sections (pullback.snd f y) ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  rw [← Scheme.Pullback.range_fst]
  exact Set.finite_range _

theorem isIso_of_densePart_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  obtain ⟨w₀, hw₀⟩ := genericPoints_subset_range_of_isDominant (i ≫ p)
    (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])
  have hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← i.denseRange.closure_range]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have h : w₀ ⤳ w := by
      rw [← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]
      exact genericPoint_specializes _
    exact specializes_iff_mem_closure.mp (h.map i.continuous)
  have : IrreducibleSpace Γ := (irreducibleSpace_def Γ).mpr hgen.isIrreducible
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have he : i w₀ = genericPoint Γ := hgen.eq (genericPoint_spec Γ)
  have : IsIso (p.stalkMap (genericPoint Γ)) := by
    rw [← he]
    have h₁ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀
    have h₂ := isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀
    rw [Scheme.Hom.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁
  have := isOpenImmersion_of_quasiFinite_of_isIso_stalkMap p (fun y ↦ inferInstance)
  exact (isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, inferInstance⟩

theorem isIso_of_densePart {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [LocallyQuasiFinite p] [Surjective p]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsIso p := by
  let V : Y → Y.Opens := fun y ↦ ⟨irreducibleComponent y,
    IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents y)⟩
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    exact fun y _ ↦ Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    V hV).mpr fun y ↦ ?_
  have : IrreducibleSpace (V y).toScheme :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))
  have : IsIntegral (V y).toScheme := IsNormalScheme.isIntegral_of_irreducibleSpace _
  have e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y := morphismRestrict_comp _ _ _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : Surjective (p ∣_ V y) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : LocallyQuasiFinite (p ∣_ V y) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p (V y)).flip ‹_›
  exact isIso_of_densePart_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)

end GlobalTheory.HomExt
end

