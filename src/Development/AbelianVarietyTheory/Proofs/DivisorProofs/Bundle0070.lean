module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutThickeningsOfIsPullbackSections
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ThickPush

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem isUnit_germ_of_eq {T : Scheme.{0}} {p q : T} (hpq : p = q) (W : T.Opens) (hp : p ∈ W) (hq : q ∈ W)
    (t : Γ(T, W)) (h : IsUnit (T.presheaf.germ W p hp t)) : IsUnit (T.presheaf.germ W q hq t) := by
  subst hpq; exact h

section Desc
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def bse : (Y : TopCat) ⟶ (T : TopCat) :=
  TopCat.ofHom ⟨fun y => g₁ ((hj.homeomorph _).symm y),
    g₁.base.hom.continuous.comp (hj.homeomorph _).symm.continuous⟩

theorem bse_j₁ (x : Y₁) : bse hj g₁ (j₁ x) = g₁ x := by
  show g₁ ((hj.homeomorph _).symm (hj.homeomorph _ x)) = g₁ x
  rw [Homeomorph.symm_apply_apply]

include hw hi₂ hg in
theorem bse_j₂ (x : Y₂) : bse hj g₁ (j₂ x) = g₂ x := by
  obtain ⟨y, rfl⟩ := hi₂ x
  have h1 : j₂ (i₂ y) = j₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  have h2 : g₂ (i₂ y) = g₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  rw [h1, h2, bse_j₁]

theorem pre₁ (W : T.Opens) : j₁ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₁ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₁ x) ∈ W ↔ g₁ x ∈ W
  rw [bse_j₁]

include hw hi₂ hg in
theorem pre₂ (W : T.Opens) : j₂ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₂ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₂ x) ∈ W ↔ g₂ x ∈ W
  rw [bse_j₂ hw hi₂ hj g₁ g₂ hg]

end Desc

section Lift
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def liftApp (W : T.Opens) : Γ(T, W) ⟶ Γ(Y, (TopologicalSpace.Opens.map (bse hj g₁)).obj W) :=
  (hV _).lift (g₁.appLE W _ (pre₁ hj g₁ W).le) (g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le) (by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq hg _ _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm))

@[reassoc]
theorem liftApp_fst (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₁.app _ = g₁.appLE W _ (pre₁ hj g₁ W).le :=
  (hV _).lift_fst _ _ _

@[reassoc]
theorem liftApp_snd (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₂.app _ =
    g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le :=
  (hV _).lift_snd _ _ _

def psh : Y.toPresheafedSpace ⟶ T.toPresheafedSpace where
  base := bse hj g₁
  c :=
    { app := fun W => liftApp hw hi₂ hj hV g₁ g₂ hg W.unop
      naturality := fun W W' i => by
        apply (hV _).hom_ext
        · simp only [Category.assoc]
          erw [liftApp_fst, Scheme.Hom.naturality, liftApp_fst_assoc]
          simp
        · simp only [Category.assoc]
          erw [liftApp_snd, Scheme.Hom.naturality, liftApp_snd_assoc]
          simp }

end Lift

section Hom
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def desc : Y ⟶ T :=
  ⟨⟨psh hw hi₂ hj hV g₁ g₂ hg, fun x => ⟨fun a ha => by
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    obtain ⟨W, hW, t, rfl⟩ := T.presheaf.germ_exist (x := (psh hw hi₂ hj hV g₁ g₂ hg).base (j₁ x₁)) a
    have h1 := PresheafedSpace.stalkMap_germ_apply (psh hw hi₂ hj hV g₁ g₂ hg) W (j₁ x₁) hW t
    erw [h1] at ha
    have h2 : IsUnit ((Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t))) := by
      erw [← Scheme.Hom.germ_stalkMap_apply]; exact ha.map (j₁.stalkMap x₁).hom
    have h3 : (j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t) =
        (g₁.appLE W _ (pre₁ hj g₁ W).le).hom t := by
      rw [← CommRingCat.comp_apply, liftApp_fst]
    erw [h3] at h2
    have hx₁ : g₁ x₁ ∈ W := by rw [← bse_j₁ hj g₁ x₁]; exact hW
    have h4 : (Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((g₁.appLE W _ (pre₁ hj g₁ W).le).hom t) = g₁.stalkMap x₁ (T.presheaf.germ W (g₁ x₁) hx₁ t) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
    rw [h4] at h2
    exact isUnit_germ_of_eq (bse_j₁ hj g₁ x₁).symm W hx₁ hW t (isUnit_of_map_unit (g₁.stalkMap x₁).hom _ h2)⟩⟩⟩

theorem desc_app (W : T.Opens) : (desc hw hi₂ hj hV g₁ g₂ hg).app W = liftApp hw hi₂ hj hV g₁ g₂ hg W := rfl

end Hom

section Fac
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

theorem fac₁ : j₁ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₁ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₁ hj g₁ x
  · have hh : j₁.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₁ ⁻¹ᵁ W) e = j₁.app _ ≫ Y₁.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_fst_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem fac₂ : j₂ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₂ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₂ hw hi₂ hj g₁ g₂ hg x
  · have hh : j₂.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₂ ⁻¹ᵁ W) e = j₂.app _ ≫ Y₂.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_snd_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem uniq (m : Y ⟶ T) (h₁ : j₁ ≫ m = g₁) (h₂ : j₂ ≫ m = g₂) : m = desc hw hi₂ hj hV g₁ g₂ hg := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    show m (j₁ x₁) = bse hj g₁ (j₁ x₁)
    rw [bse_j₁, ← h₁, Scheme.Hom.comp_apply]
  · rw [desc_app]
    apply (hV _).hom_ext
    · refine Eq.trans ?_ (liftApp_fst hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₁]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₁ _ _ _ _)
    · refine Eq.trans ?_ (liftApp_snd hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₂]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₂ _ _ _ _)

end Fac

theorem isPushout_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ →
    ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂),
    IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ →
    (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
      (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) →
    IsPushout i₁ i₂ j₁ j₂ := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ hs₂ Y j₁ j₂ hw hc₁ _ hs₁ _ hV
  have hj : IsHomeomorph j₁ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j₁.isClosedEmbedding.isEmbedding, hs₁.surj⟩
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => desc hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₁ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₂ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s m h₁ h₂ => uniq hw hs₂.surj hj hV s.inl s.inr s.condition m h₁ h₂))

end GlobalTheory.ThickPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingTensorOfFibreLocalRings
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_tensor_of_fibre_localRings :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hQ hfrac hreg
  haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)
  let φ : Q.ResidueField →ₐ[S] K := Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hQ ▸ h0))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := hfrac y
    have hb0 : algebraMap S K b ≠ 0 := fun h0 => hb (hQ ▸ h0)
    refine ⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]
    rw [← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  let e : Q.ResidueField ≃ₐ[S] K := AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩
  let E : Q.Fiber T ≃ₐ[S] T ⊗[S] K :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)
  haveI : IsNoetherianRing (Q.Fiber T) := by
    letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra
    let Sp := Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)
    haveI : IsNoetherianRing Sp :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm
  haveI : IsRegularRing (Q.Fiber T) := by
    rw [isRegularRing_iff]
    intro q hq
    let n : Ideal T := q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)
    haveI : n.IsPrime := Ideal.comap_isPrime _ _
    have hn : n.comap (algebraMap S T) = Q := by
      change Ideal.comap (algebraMap S T) (Ideal.comap
        ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q
      rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
      exact (Ideal.over_def q Q).symm
    haveI := hreg n hn
    exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootCharpolyOfIsRootMinpoly
section
open Polynomial

namespace GlobalTheory.SumScalarVanishing

section
variable {F C E : Type} [Field F] [Ring C] [Algebra F C] [Field E] [Algebra F E]

theorem eq_zero_of_sum_smul [Algebra.IsCentral F C] [IsSimpleRing C] {n : ℕ} (hn : 0 < n)
    (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a))
    {ι : Type} (e : ι → E) (he : LinearIndependent F e) (s : Finset ι) :
    ∀ c : ι → C, ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
  classical
  have hmain : ∀ (k : ℕ) (c : ι → C), (s.filter (fun i => c i ≠ 0)).card = k →
      ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro c hk hsum i0 hi0
    by_contra hci0

    let I : TwoSidedIdeal C := TwoSidedIdeal.mk'
      {a | ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0}
      ⟨0, rfl, fun _ _ _ => rfl, by simp⟩
      (by
        rintro x y ⟨d, rfl, hd, hds⟩ ⟨d', rfl, hd', hds'⟩
        refine ⟨d + d', rfl, fun i hi hc => by simp [hd i hi hc, hd' i hi hc], ?_⟩
        simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib, hds, hds', add_zero])
      (by
        rintro x ⟨d, rfl, hd, hds⟩
        refine ⟨-d, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [Pi.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib, hds, neg_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => x * d i, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.mul_smul, ← Finset.mul_sum, hds, mul_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => d i * y, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.smul_mul, ← Finset.sum_mul, hds, zero_mul])
    have hmem : ∀ a, a ∈ I ↔
        ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0 :=
      fun a => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a
    have hI : I = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top I with h | h
      · exfalso
        have h' : c i0 ∈ I := (hmem _).2 ⟨c, rfl, fun i _ hc => hc, hsum⟩
        rw [h, TwoSidedIdeal.mem_bot] at h'
        exact hci0 h'
      · exact h
    have h1 : (1 : C) ∈ I := by rw [hI]; trivial
    obtain ⟨d, hd0, hdc, hds⟩ := (hmem 1).1 h1

    have hcen : ∀ i ∈ s, ∀ y : C, y * d i = d i * y := by
      intro i hi y
      let d' : ι → C := fun j => y * d j - d j * y
      have hs' : ∑ j ∈ s, e j • ρ (d' j) = 0 := by
        have hsplit : ∑ j ∈ s, e j • ρ (d' j) =
            ρ y * (∑ j ∈ s, e j • ρ (d j)) - (∑ j ∈ s, e j • ρ (d j)) * ρ y := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [d', map_sub, map_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
        rw [hsplit, hds, mul_zero, zero_mul, sub_zero]
      have hsub : s.filter (fun j => d' j ≠ 0) ⊂ s.filter (fun j => c j ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, Finset.mem_filter.2 ⟨hi0, hci0⟩, fun h => ?_⟩
          exact (Finset.mem_filter.1 h).2 (by simp [d', hd0])
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨hj.1, fun hc => hj.2 ?_⟩
          simp [d', hdc j hj.1 hc]
      have hlt := Finset.card_lt_card hsub
      rw [hk] at hlt
      have := ih _ hlt d' rfl hs' i hi
      exact sub_eq_zero.1 this
    have hex : ∀ i, ∃ a : F, i ∈ s → algebraMap F C a = d i := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, ha⟩ := Algebra.mem_bot.1
          (Algebra.IsCentral.out ((Subalgebra.mem_center_iff (R := F)).2 (hcen i hi)))
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose f hf using hex
    have hsum2 : ∑ i ∈ s, f i • e i = 0 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) E => M ⟨0, hn⟩ ⟨0, hn⟩) hds
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hf i hi, hρ]
      simp [Algebra.smul_def, mul_comm]
    have hf0 := linearIndependent_iff'.1 he s f hsum2 i0 hi0
    have := hf i0 hi0
    rw [hf0, map_zero, hd0] at this
    exact zero_ne_one this
  exact fun c hc => hmain _ c rfl hc

theorem exists_expansion {ι : Type} (b : Module.Basis ι F E) (p : E[X]) :
    ∃ q : ι →₀ F[X], p = q.sum (fun k r => b k • r.map (algebraMap F E)) := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨u, rfl⟩ := hp
    obtain ⟨v, rfl⟩ := hq
    refine ⟨u + v, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro k
      simp
    · intro k r r'
      rw [Polynomial.map_add (f := _), smul_add]
  | monomial j a =>
    refine ⟨(b.repr a).mapRange (fun c => Polynomial.monomial j c) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (by simp)]
    simp only [Polynomial.map_monomial, Polynomial.smul_monomial]
    rw [← map_finsuppSum (Polynomial.monomial j)]
    congr 1
    conv_lhs => rw [← b.linearCombination_repr a]
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]

end

theorem isRoot_charpoly_of_isRoot_minpoly {F C E : Type} [Field F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C] [Field E] (τ : F →+* E)
    {n : ℕ} (hn : 0 < n) (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (τ a)) (x : C) (μ : E)
    (hμ : ((minpoly F x).map τ).IsRoot μ) : (ρ x).charpoly.IsRoot μ := by
  classical
  let _ : Algebra F E := τ.toAlgebra
  have hρ' : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a) := hρ
  let b := Module.Basis.ofVectorSpace F E
  obtain ⟨q, hq⟩ := exists_expansion b (ρ x).charpoly

  have heval : ∀ r : F[X],
      Polynomial.aeval (ρ x) (r.map (algebraMap F E)) = ρ (Polynomial.aeval x r) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), hp, hq]
    | monomial j a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul, map_pow, hρ']
      congr 1

  have h0 : ∑ k ∈ q.support, b k • ρ (Polynomial.aeval x (q k)) = 0 := by
    have h := Matrix.aeval_self_charpoly (ρ x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hq, Finsupp.sum, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, heval]
  have hz := eq_zero_of_sum_smul hn ρ hρ' b b.linearIndependent q.support
    (fun k => Polynomial.aeval x (q k)) h0
  have hdvd : (minpoly F x).map (algebraMap F E) ∣ (ρ x).charpoly := by
    rw [hq, Finsupp.sum]
    refine Finset.dvd_sum fun k hk => ?_
    rw [Polynomial.smul_eq_C_mul]
    exact Dvd.dvd.mul_left (Polynomial.map_dvd _ (minpoly.dvd F x (hz k hk))) _
  exact Polynomial.IsRoot.dvd hμ hdvd

end GlobalTheory.SumScalarVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt
section
open NumberField

namespace GlobalTheory

theorem isTorsionFree_ringOfIntegers_of_isTorsionFree_int (E : Type) [Field E] [NumberField E]
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree (𝓞 E) N := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun c x hcx => ?_)
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have halg : IsAlgebraic ℤ c := (Algebra.IsIntegral.isIntegral (R := ℤ) c).isAlgebraic
    obtain ⟨m, hm, d, hd⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
    have h1 : m • x = 0 := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E)]
      have : ((m : ℤ) : 𝓞 E) = d * c := by
        rw [mul_comm, ← hd]; simp
      rw [this, mul_smul, hcx, smul_zero]
    exact (smul_eq_zero.mp h1).resolve_left hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfUnitMulComulEqTmulSelf
section
open scoped TensorProduct

namespace GlobalTheory


open TensorProduct in
theorem isUnit_of_unit_mul_comul_eq_tmul_self (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H]
    (c : H ⊗[K] H) (hc : IsUnit c) (u : H) (hu : u ≠ 0)
    (h : c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u) : IsUnit u := by

  let φ : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lid K H).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
  have hφΔ : φ (Coalgebra.comul (R := K) u) = u := by
    have e := congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)
    rw [TensorProduct.lid_tmul, one_smul] at e
    exact e
  have hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R := K) u • u := by
    simp [φ]
  have hε : Coalgebra.counit (R := K) u ≠ 0 := by
    intro h0
    have e := congrArg φ h
    rw [map_mul, hφΔ, hφuu, h0, zero_smul] at e
    exact hu ((hc.map φ).mul_right_eq_zero.mp e)

  let ψ : H ⊗[K] H →ₐ[K] H :=
    Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H)
      (fun _ _ => Commute.all _ _)
  have hψΔ : ψ (Coalgebra.comul (R := K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]
    induction Coalgebra.comul (R := K) u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u := by
    simp [ψ]
  have e := congrArg ψ h
  rw [map_mul, hψΔ, hψuu] at e
  have hU : IsUnit (u * HopfAlgebra.antipode K u) := by
    rw [← e]
    exact (hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))
  exact isUnit_of_mul_isUnit_left hU

end GlobalTheory
end

