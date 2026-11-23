module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDimUniq
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

private lemma relDim_eq_of_ringHom {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    {m n : ℕ} (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  letI := f.toAlgebra
  have e₁ : Module.rank S Ω[S⁄R] = m :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm
  have e₂ : Module.rank S Ω[S⁄R] = n :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn
  exact_mod_cast e₁.symm.trans e₂

private lemma exists_nontrivial_away {S : Type} [CommRing S] [Nontrivial S] (s : Set S)
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, Nontrivial (Localization.Away t) := by
  by_contra hne
  push_neg at hne
  have hsub : s ⊆ nilradical S := by
    intro t ht
    haveI : Subsingleton (Localization.Away t) := hne t ht
    have h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0 :=
      Subsingleton.elim _ _
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by simpa using hc'⟩
  have hle := Ideal.span_le.2 hsub
  rw [hs, top_le_iff] at hle
  have h1 : (1 : S) ∈ nilradical S := hle ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := h1
  simp at hk

private lemma relDim_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) (x : X) : m = n := by
  obtain ⟨U, hU, V, hV, hx, e, hmU⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hst⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨t, ht, hnt⟩ := exists_nontrivial_away s hs
  have hm' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
    (Localization.Away t) t _ hmU
  exact relDim_eq_of_ringHom _ hm' (hst t ht)

theorem dimUniq_of : DimUniq := by
  intro Z s d d' hd hd' hZ
  obtain ⟨z⟩ := hZ
  exact relDim_eq s hd hd' z

end UpperTheory.Gal.FixZ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PLegOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField

namespace UpperTheory.Gal.FixZ

theorem legOf_of : LegOf := by
  intro p _ D G L gb k T N' N h b
  obtain ⟨π, o, ψ, φ, hw, hs, htr, he⟩ := T.tr_eq N' N h b.1 b.2
  refine ⟨W2.Leg.mk π o ψ φ hs ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.2⟩, he, fun α => ?_⟩
  simp only [LocalSmoothExtension.leg, LocalSmoothExtension.al, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]
  rfl

end UpperTheory.Gal.FixZ

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PPowFEt
section
open AlgebraicGeometry CategoryTheory Limits

namespace UpperTheory.Gal.FixZ

section Coord

variable {C : Type*} [Category C] {A : C} {k : ℕ} [HasProduct (fun _ : Fin k => A)]

private noncomputable def coordMap (j : Fin k) (φ : A ⟶ A) :
    (∏ᶜ fun _ : Fin k => A) ⟶ ∏ᶜ fun _ : Fin k => A :=
  Pi.lift fun i => if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i

private lemma coordMap_π (j i : Fin k) (φ : A ⟶ A) :
    coordMap j φ ≫ Pi.π (fun _ : Fin k => A) i =
      if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i := by
  simp [coordMap]

private lemma coordMap_isPullback (j : Fin k) (φ : A ⟶ A) :
    IsPullback (coordMap j φ) (Pi.π (fun _ : Fin k => A) j) (Pi.π (fun _ : Fin k => A) j) φ := by
  refine ⟨⟨by simp [coordMap_π]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Pi.lift fun i => if i = j then s.snd else s.fst ≫ Pi.π (fun _ : Fin k => A) i)
    ?_ ?_ ?_⟩⟩
  · intro s
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, coordMap_π]
    by_cases h : i = j
    · subst h
      simpa using s.condition.symm
    · simp [h]
  · intro s
    simp
  · intro s m h₁ h₂
    refine Pi.hom_ext _ _ fun i => ?_
    by_cases h : i = j
    · subst h
      simpa using h₂
    · have := congrArg (· ≫ Pi.π (fun _ : Fin k => A) i) h₁
      simpa [coordMap_π, h] using this

end Coord

private lemma pow_prop (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{0}} (A : Over S) (k : ℕ) (f : Fin k → (A ⟶ A))
    (hf : ∀ i, P (f i).left) (g : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k)
    (hg : ∀ i, g ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ f i) : P g.left := by
  have step : ∀ j : ℕ, j ≤ k → ∃ h : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k, P h.left ∧
      ∀ i : Fin k, h ≫ GlobalTheory.KS.pr A i =
        if i.val < j then GlobalTheory.KS.pr A i ≫ f i else GlobalTheory.KS.pr A i := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨𝟙 _, by simpa using P.id_mem _, fun i => by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨h, hP, hh⟩ := ih (by omega)
      let j' : Fin k := ⟨j, by omega⟩
      have hb : IsPullback (coordMap j' (f j')).left (GlobalTheory.KS.pr A j').left
          (GlobalTheory.KS.pr A j').left (f j').left :=
        (coordMap_isPullback j' (f j')).map (Over.forget S)
      have he : P (coordMap j' (f j')).left := P.of_isPullback hb.flip (hf j')
      refine ⟨h ≫ coordMap j' (f j'), ?_, fun i => ?_⟩
      · rw [Over.comp_left]
        exact P.comp_mem _ _ hP he
      · rw [Category.assoc, GlobalTheory.KS.pr, coordMap_π]
        by_cases hi : i = j'
        · subst hi
          have h0 : h ≫ Pi.π (fun _ : Fin k => A) j' = Pi.π (fun _ : Fin k => A) j' := by
            have := hh j'
            simpa [GlobalTheory.KS.pr, j'] using this
          rw [if_pos rfl, if_pos (by simp [j']), ← Category.assoc, h0]
        · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
          have := hh i
          simp only [GlobalTheory.KS.pr] at this
          simp only [hi, if_false, this]
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨h, hP, hh⟩ := step k le_rfl
  have : g = h := Pi.hom_ext _ _ fun i => by
    have := hh i
    simp only [i.isLt, if_true] at this
    exact (hg i).trans this.symm
  rw [this]
  exact hP

theorem powFEt_of : PowFEt := by
  intro S A k f hf g hg
  exact ⟨pow_prop @IsFinite A k f (fun i => (hf i).1) g hg,
    pow_prop @Etale A k f (fun i => (hf i).2.1) g hg,
    pow_prop @Surjective A k f (fun i => (hf i).2.2) g hg⟩

end UpperTheory.Gal.FixZ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTanIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace UpperTheory.Gal.FixZ

private def secEquiv {Y Y' : Scheme.{0}} {t : Y ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (e : Y ≅ Y')
    (ht : e.hom ≫ t' = t) (V : Y'.Opens) : Sec t' V ≃ₐ[ℂ] Sec t (e.hom ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective
    { appSec t' t e.hom V with
      commutes' := fun r => (semiHom_appSec ht V).map_algebraMap r }
    (ConcreteCategory.bijective_of_isIso (e.hom.app V))

private theorem eq_self_of_fix_D_of_linear_kaehler {A : Type} [CommRing A] [Algebra ℂ A] (g : Ω[A⁄ℂ] →ₗ[ℂ] Ω[A⁄ℂ])
    (hD : ∀ a, g (D ℂ A a) = D ℂ A a) (hs : ∀ (a : A) (ω : Ω[A⁄ℂ]), g (a • ω) = a • g ω)
    (ω : Ω[A⁄ℂ]) : g ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero => exact map_zero g
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [hs, hx]

private theorem exists_kaehler_map_D_of_algHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] →ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : SMulCommClass ℂ A B := ⟨fun r a b => by
    change r • (f a * b) = f a * (r • b)
    rw [mul_smul_comm]⟩
  refine ⟨(KaehlerDifferential.map ℂ ℂ A B).restrictScalars ℂ, fun a => ?_, fun a ω => ?_⟩
  · exact KaehlerDifferential.map_D ℂ ℂ A B a
  · rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, ← algebraMap_smul (A := B) a]
    rfl

private theorem exists_kaehler_equiv_D_of_algEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A ≃ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] ≃ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  obtain ⟨Ψ, h1, h2⟩ := exists_kaehler_map_D_of_algHom (f : A →ₐ[ℂ] B)
  obtain ⟨Φ, g1, g2⟩ := exists_kaehler_map_D_of_algHom (f.symm : B →ₐ[ℂ] A)
  have l : ∀ ω, Φ (Ψ ω) = ω := eq_self_of_fix_D_of_linear_kaehler (Φ ∘ₗ Ψ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  have r : ∀ η, Ψ (Φ η) = η := eq_self_of_fix_D_of_linear_kaehler (Ψ ∘ₗ Φ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  exact ⟨LinearEquiv.ofLinear Ψ Φ (LinearMap.ext r) (LinearMap.ext l), h1, h2⟩

private theorem valR_comp_eq_valR_app {X W : Scheme} (x : Sp ℂ ⟶ X) (f : X ⟶ W) (V : W.Opens)
    (g : Γ(W, V)) :
    valR (x ≫ f) V g = valR x (f ⁻¹ᵁ V) (f.app V g) := by
  unfold valR
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_left h', dite_eq_left h]
    simp [Scheme.Hom.comp_appLE]
  · have h' : ¬ ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dite_eq_right h', dite_eq_right h]

private theorem preimage_le_preimage_preimage_of_comm_iso {Y Y' Z Z' : Scheme} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z)
    (c' : Y' ⟶ Z') (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens)
    (h : V' ≤ c' ⁻¹ᵁ U') : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U' := by
  rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  exact fun p hp => h hp

private theorem appSec_res_appSec_eq_of_comm_iso {Y Y' Z Z' : Scheme} {s : Z ⟶ Sp ℂ} {t : Y ⟶ Sp ℂ}
    {s' : Z' ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z) (c' : Y' ⟶ Z')
    (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens) (hV' : V' ≤ c' ⁻¹ᵁ U')
    (hV : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U') (τ : Sec s' U') :
    appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) := by
  have key : ∀ (g₁ g₂ : Y ⟶ Z') (_ : g₁ = g₂) (W : Y.Opens) (e₁ : W ≤ g₁ ⁻¹ᵁ U')
      (e₂ : W ≤ g₂ ⁻¹ᵁ U'), g₁.appLE U' W e₁ = g₂.appLE U' W e₂ := by
    rintro _ _ rfl _ _ _; rfl
  have e1 : eY.hom ⁻¹ᵁ V' ≤ (eY.hom ≫ c') ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact fun p hp => hV' hp
  have e2 : eY.hom ⁻¹ᵁ V' ≤ (c ≫ eZ.hom) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact hV
  have L : appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      (eY.hom ≫ c').appLE U' _ e1 τ := by
    change eY.hom.app V' (Y'.presheaf.map (homOfLE hV').op (c'.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE]
    simp only [CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have R : Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) =
      (c ≫ eZ.hom).appLE U' _ e2 τ := by
    change Y.presheaf.map (homOfLE hV).op (c.app _ (eZ.hom.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [L, R, key _ _ hc.symm]

theorem tanIso_of :
    UpperTheory.Gal.FixZ.TanIso := by
  intro Z Y Z' Y' s t s' t' eZ eY hs ht d c₁ c₂ c₁' c₂' h₁ h₂ h₁' h₂' hc₁ hc₂
  refine ⟨?E, ?_⟩
  case E =>
    unfold CxPts Points.PtsOver
    exact
      { toFun := fun x => ⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩
        invFun := fun y => ⟨y.1 ≫ eY.inv, by rw [Category.assoc, ← ht, eY.inv_hom_id_assoc]; exact y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  refine ⟨fun x => rfl, fun x => ?_, fun x A hT => ?_⟩
  · change x.1 ≫ c₁ = x.1 ≫ c₂ ↔ (x.1 ≫ eY.hom) ≫ c₁' = (x.1 ≫ eY.hom) ≫ c₂'
    rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, ← Category.assoc, ← Category.assoc x.1,
      cancel_mono]
  · obtain ⟨U', V', hV1', hV2', τ, hx, hU', hV', φ', hsm, hd1, hd2, hker⟩ := hT
    set σ := secEquiv eY ht V' with hσ
    have hσa : ∀ g, σ g = appSec t' t eY.hom V' g := fun g => rfl
    have EV : ∀ g : Sec t' V', CxPts.ev t' (RingHom.id ℂ) V' g
        (⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩ : CxPts t' (RingHom.id ℂ)) =
        CxPts.ev t (RingHom.id ℂ) (eY.hom ⁻¹ᵁ V') (σ g) x := fun g =>
      valR_comp_eq_valR_app x.1 eY.hom V' g
    obtain ⟨Ψ, hΨD, hΨs⟩ := exists_kaehler_equiv_D_of_algEquiv σ.symm
    have hW1 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1'
    have hW2 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2'
    have q1 : ∀ l, σ.symm (Sec.res t hW1 (appSec s t c₁ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV1' (appSec s' t' c₁' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1' hW1 (τ l)])
    have q2 : ∀ l, σ.symm (Sec.res t hW2 (appSec s t c₂ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV2' (appSec s' t' c₂' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2' hW2 (τ l)])
    refine ⟨eZ.hom ⁻¹ᵁ U', eY.hom ⁻¹ᵁ V', hW1, hW2, fun l => appSec s' s eZ.hom U' (τ l), hx,
      hU'.preimage_of_isIso eZ.hom, hV'.preimage_of_isIso eY.hom, φ' ∘ₗ Ψ.toLinearMap,
      ?_, ?_, ?_, ?_⟩
    · intro b ω
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨs, hsm]
      erw [EV]
      rw [AlgEquiv.apply_symm_apply]
    · intro l
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q1]
      exact hd1 l
    · intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q2]
      exact hd2 j
    · intro ω hω
      obtain ⟨m, b, ω', hb, hsum⟩ := hker (Ψ ω) hω
      refine ⟨m, fun i => σ (b i), fun i => Ψ.symm (ω' i), fun i => ?_, ?_⟩
      · rw [← EV]; exact hb i
      · apply Ψ.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hsum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hΨs, AlgEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

end UpperTheory.Gal.FixZ

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrFEt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Integ)

namespace UpperTheory.Gal.FixZ

private lemma tr_comp {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : G3.Tower B Γ) {i j m : X.ι} {h h' g : Γ} (a b a' b')
    (e : h' * h = g) (c d) : X.tr i j h a b ≫ X.tr j m h' a' b' = X.tr i m g c d := by
  subst e
  exact X.tr_mul i j m h h' a b a' b' c d

private lemma lofp_cancel {A B S : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ g ⁻¹ᵁ W⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open hxW (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (g.appLE W U hUW).hom ?_ (g.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ g).finitePresentation_appLE hW hV _

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {gb : GBase D.toG ℂ} {k : ℕ}

private lemma q_props (hP : G3.PowSm) (T : KS L gb k) (N : Lv p) :
    Smooth (T.X.q (T.lev N)) ∧ IsSeparated (T.X.q (T.lev N)) := by
  obtain ⟨h1, h2, -⟩ := hP p D ℂ gb N (T.M N) k
  rw [← T.e_q N]
  exact ⟨inferInstance, inferInstance⟩

private lemma tr_props (hP : G3.PowSm) (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (a b) :
    IsSeparated (T.X.tr (T.lev N') (T.lev N) h a b) ∧ LocallyOfFinitePresentation (T.X.tr (T.lev N') (T.lev N) h a b) := by
  obtain ⟨s1, s2⟩ := q_props hP T N'
  obtain ⟨s3, s4⟩ := q_props hP T N
  have e := T.X.tr_q (T.lev N') (T.lev N) h a b
  constructor
  · rw [← e] at s2
    exact IsSeparated.of_comp _ (T.X.q (T.lev N))
  · rw [← e] at s1
    exact lofp_cancel _ (T.X.q (T.lev N))

private lemma scal_fe (hS : TrScal) (T : KS L gb k) (P Q : Lv p) (d : ℕ) (z : G.GAf) (hd : 0 < d) (hc : d.Coprime p)
    (hz : IsScal L d z) (a b) (a₁ : (1 : G.GAf) ∈ T.X.Δ)
    (b₁ : ∀ u ∈ T.X.K (T.lev P), 1 * u * 1⁻¹ ∈ T.X.K (T.lev Q)) (a₂ : z ∈ T.X.Δ)
    (b₂ : ∀ u ∈ T.X.K (T.lev Q), z * u * z⁻¹ ∈ T.X.K (T.lev Q)) :
    IsFinite (T.X.tr (T.lev P) (T.lev Q) z a b) ∧ Etale (T.X.tr (T.lev P) (T.lev Q) z a b) := by
  have e := tr_comp T.X a₁ b₁ a₂ b₂ (mul_one z) a b
  obtain ⟨f1, f2⟩ := hS p D G L gb k T Q d z hd hc hz a₂ b₂
  have f3 := T.X.fin _ _ a₁ b₁
  have f4 := T.X.etale _ _ a₁ b₁
  rw [← e]
  exact ⟨inferInstance, inferInstance⟩

theorem trFEt_of : G3.PowSm → ScalEx → TrScal → EtCancel → DescEt → DescFin → TrFEt := by
  classical
  intro hP hSc hTS hEC hDE hDF p _ D G L gb k T N' N h a b
  obtain ⟨d, z, hd, hc, hz, hzi, hzh⟩ := hSc p D G L h ((T.Δ_eq h).1 a)
  have hcen := hz.1
  have zΔ : z ∈ T.X.Δ := (T.Δ_eq z).2 hzi
  have h'Δ : z * h⁻¹ ∈ T.X.Δ := (T.Δ_eq _).2 hzh
  have oΔ : (1 : G.GAf) ∈ T.X.Δ := one_mem _
  have zc : ∀ u : G.GAf, z * u * z⁻¹ = u := fun u => by rw [hcen u, mul_inv_cancel_right]
  have e1 : h * (z * h⁻¹) = z := by rw [← mul_assoc, ← hcen h, mul_inv_cancel_right]
  have e2 : z * h⁻¹ * h = z := by rw [inv_mul_cancel_right]

  obtain ⟨m, -, -, hm⟩ := T.X.deep (T.lev N') {(T.lev N, 1), (T.lev N', z * h⁻¹)}
  obtain ⟨m', -, -, hm'⟩ := T.X.deep (T.lev N') {(m, h), (T.lev N', 1)}
  obtain ⟨M, rfl⟩ := T.lev.surjective m
  obtain ⟨M', rfl⟩ := T.lev.surjective m'
  have b1 : ∀ u ∈ T.X.K (T.lev M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := hm (T.lev N, 1) (by simp)
  have b2 : ∀ u ∈ T.X.K (T.lev M), z * h⁻¹ * u * (z * h⁻¹)⁻¹ ∈ T.X.K (T.lev N') := hm (T.lev N', z * h⁻¹) (by simp)
  have b3 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev M) := hm' (T.lev M, h) (by simp)
  have b4 : ∀ u ∈ T.X.K (T.lev M'), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N') := hm' (T.lev N', 1) (by simp)
  have b5 : ∀ u ∈ T.X.K (T.lev M), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 u hu
    simpa [zc] using this
  have b6 : ∀ u ∈ T.X.K (T.lev M'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by
    have := b4 u hu
    simpa [zc] using this
  have b7 : ∀ u ∈ T.X.K (T.lev N), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by rwa [zc]
  have b8 : ∀ u ∈ T.X.K (T.lev N'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by rwa [zc]
  have b9 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 _ (b3 u hu)
    simpa using this

  have c1 : T.X.tr _ _ (z * h⁻¹) h'Δ b2 ≫ T.X.tr _ _ h a b = T.X.tr _ _ z zΔ b5 :=
    tr_comp T.X h'Δ b2 a b e1 zΔ b5
  have c2 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ (z * h⁻¹) h'Δ b2 = T.X.tr _ _ z zΔ b6 :=
    tr_comp T.X a b3 h'Δ b2 e2 zΔ b6
  obtain ⟨f1, f2⟩ := scal_fe hTS T M N d z hd hc hz zΔ b5 oΔ b1 zΔ b7
  obtain ⟨f3, f4⟩ := scal_fe hTS T M' N' d z hd hc hz zΔ b6 oΔ b4 zΔ b8
  rw [← c1] at f1 f2
  rw [← c2] at f3 f4
  obtain ⟨-, s1⟩ := tr_props hP T M N' (z * h⁻¹) h'Δ b2
  have t1 : LocallyOfFiniteType (T.X.tr _ _ (z * h⁻¹) h'Δ b2) := inferInstance
  obtain ⟨f5, f6⟩ := hEC _ _ _ _ (T.X.tr _ _ h a b3) (T.X.tr _ _ (z * h⁻¹) h'Δ b2) (T.X.tr _ _ h a b) t1 f3 f4 f1 f2

  have c3 : T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b = T.X.tr _ _ h a b9 :=
    tr_comp T.X oΔ b4 a b (mul_one h) a b9
  have c4 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ 1 oΔ b1 = T.X.tr _ _ h a b9 :=
    tr_comp T.X a b3 oΔ b1 (one_mul h) a b9
  have g1 := T.X.fin _ _ oΔ b1
  have g2 := T.X.etale _ _ oΔ b1
  have g3 : IsFinite (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  have g4 : Etale (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  obtain ⟨s2, s3⟩ := tr_props hP T N' N h a b
  have g5 := hDE _ _ _ _ _ (T.X.etale _ _ oΔ b4) (T.X.onto _ _ oΔ b4) s3 g4
  exact ⟨hDF _ _ _ _ _ (T.X.onto _ _ oΔ b4) s2 g5 g3, g5⟩

end UpperTheory.Gal.FixZ

end
end

