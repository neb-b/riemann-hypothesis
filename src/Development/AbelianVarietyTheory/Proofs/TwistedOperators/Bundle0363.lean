module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabGroupIsoOfGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem exists_appLE_ne_zero_of_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t₀ z J hJ hne
  refine ⟨fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left), ?_, ?_⟩
  · intro y _
    have hy : y = z := Subsingleton.elim _ _
    subst hy
    exact hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
  · intro hi
    have hz : w z ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) :=
      hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
    apply hne
    rw [sv, sval_of t₀ w z J (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) (fun _ => rfl)]
    erw [gs_eq w z _ hz]
    have hle : (⊤ : (Sp Ω).Opens) ≤ w ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) := by
      intro y _
      have hy : y = z := Subsingleton.elim _ _
      subst hy
      exact hz
    rw [← TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE hle) z trivial]
    refine (congrArg ((Sp Ω).presheaf.germ ⊤ z trivial).hom ?_).trans (map_zero _)
    exact hi

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem sabMap_exists_iso_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {j : S' ⟶ S} (m : SABMap s' s j) :
    ∃ e : s'.G ≅ (Over.pullback j).obj s.G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst s.G.hom j = m.φ ∧
      ∀ a, s'.act.act a ≫ e.hom = e.hom ≫ (Over.pullback j).map (s.act.act a) := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback s.G _)
  have hφ' : e.hom.left ≫ pullback.fst s.G.hom j = m.φ := hφ
  refine ⟨e, he, hφ', fun a => ?_⟩
  have A : ((Over.pullback j).map (s.act.act a)).left ≫ pullback.fst s.G.hom _ =
        pullback.fst s.G.hom _ ≫ (s.act.act a).left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, A]
    rw [reassoc_of% hφ', hφ', m.act a]
  · exact (Over.w _).trans (Over.w _).symm

theorem conj_comp_eq_id_pow {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (u : A ≅ B) (u' : A' ≅ B') [IsMonHom u.hom] (f : B ⟶ B') (f' : B' ⟶ B) (N : ℕ) (h : f ≫ f' = 𝟙 B ^ N) :
    (u.hom ≫ f ≫ u'.inv) ≫ (u'.hom ≫ f' ≫ u.inv) = 𝟙 A ^ N := by
  have : IsMonHom u.inv := inferInstance
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem pullback_map_id_pow {S S' : Scheme.{0}} (j : S' ⟶ S) (A : Over S) [GrpObj A] (N : ℕ) :
    (Over.pullback j).map (𝟙 A ^ N) = 𝟙 ((Over.pullback j).obj A) ^ N := by
  induction N with
  | zero => simpa using Functor.map_one (Over.pullback j)
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]; simp

theorem ext_of_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {T : CDVR} {x x' : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr)))
    (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] (F : G.G ⟶ G'.G)
    (d : t.G ≅ Fib Xo x) (d' : t'.G ≅ Fib Xo x') [IsMonHom d.hom] [IsMonHom d'.hom]
    (e : t.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G.G)
    (e' : t'.G ≅ (Over.pullback (spMap (algebraMap T.V T.Fr))).obj G'.G)
    (hd : d.hom.left ≫ pullback.fst _ _ = m₁.φ) (hd' : d'.hom.left ≫ pullback.fst _ _ = n₁.φ)
    (he : e.hom.left ≫ pullback.fst _ _ = m₂.φ) (he' : e'.hom.left ≫ pullback.fst _ _ = n₂.φ)
    (hF : (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) :
    Ext m₁ m₂ n₁ n₂ f F := by
  have A : ((Over.pullback (spMap (algebraMap T.V T.Fr))).map F).left ≫ pullback.fst G'.G.hom _ =
        pullback.fst G.G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  have B : (d.hom ≫ f ≫ d'.inv) ≫ e'.hom = e.hom ≫ (Over.pullback (spMap (algebraMap T.V T.Fr))).map F := by
    rw [hF]; simp
  refine ⟨d.hom ≫ f ≫ d'.inv, inferInstance, ?_, fun g g' h1 h2 h3 h4 => ?_⟩
  · rw [← he', ← he, Category.assoc, ← A, ← Category.assoc, ← Category.assoc e.hom.left, ← Over.comp_left,
      ← Over.comp_left, B]
  · obtain rfl : g = d.hom.left := pullback.hom_ext (h1.trans hd.symm) (h2.trans (Over.w d.hom).symm)
    obtain rfl : g' = d'.hom.left := pullback.hom_ext (h3.trans hd'.symm) (h4.trans (Over.w d'.hom).symm)
    have C : d.hom ≫ f = (d.hom ≫ f ≫ d'.inv) ≫ d'.hom := by simp
    exact congrArg (fun k => k.left) C

theorem conj_comm {C : Type*} [Category C] {A B P A' B' P' : C} (e : A ≅ P) (d : A ≅ B) (e' : A' ≅ P') (d' : A' ≅ B')
    (f : B ⟶ B') (a : A ⟶ A) (b : B ⟶ B) (p : P ⟶ P) (a' : A' ⟶ A') (b' : B' ⟶ B') (p' : P' ⟶ P')
    (hd : a ≫ d.hom = d.hom ≫ b) (he : a ≫ e.hom = e.hom ≫ p) (hd' : a' ≫ d'.hom = d'.hom ≫ b')
    (he' : a' ≫ e'.hom = e'.hom ≫ p') (h : b ≫ f = f ≫ b') :
    p ≫ (e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv = ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) ≫ p' := by
  have h1 : p ≫ e.inv = e.inv ≫ a := by rw [Iso.eq_inv_comp, ← reassoc_of% he]; simp
  have h2 : b' ≫ d'.inv = d'.inv ≫ a' := by rw [Iso.eq_inv_comp, ← reassoc_of% hd']; simp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hd, reassoc_of% h, reassoc_of% h2, he']

theorem exists_ext_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' hf hf'
  have hx := semiAbelian_hom_extends_uniquely_dvr T.V T.Fr
  have inj : ∀ (s s' : SAB H (Sp T.V)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T.V T.Fr))).map F = (Over.pullback (spMap (algebraMap T.V T.Fr))).map F' →
        F = F' := by
    intro s s' F F' hF hF' h
    exact (hx s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have hpow : ∀ (s : SAB H (Sp T.V)) (N : ℕ), IsMonHom (𝟙 s.G ^ N) := by
    intro s N
    induction N with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit s.G ≫ η[s.G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 s.G ^ n) (𝟙 s.G) ≫ μ[s.G]))
  obtain ⟨d, hd, hdφ, hda⟩ := sabMap_exists_iso_pullback m₁
  obtain ⟨e, he, heφ, hea⟩ := sabMap_exists_iso_pullback m₂
  obtain ⟨d', hd', hdφ', hda'⟩ := sabMap_exists_iso_pullback n₁
  obtain ⟨e', he', heφ', hea'⟩ := sabMap_exists_iso_pullback n₂
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx G.G G'.G G.semi G'.semi
    ((e.symm ≪≫ d).hom ≫ f ≫ (e'.symm ≪≫ d').inv) (by dsimp; infer_instance)
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx G'.G G.G G'.semi G.semi
    ((e'.symm ≪≫ d').hom ≫ f' ≫ (e.symm ≪≫ d).inv) (by dsimp; infer_instance)
  have : IsMonHom (e.symm ≪≫ d).hom := by dsimp; infer_instance
  have : IsMonHom (e'.symm ≪≫ d').hom := by dsimp; infer_instance
  refine ⟨F, F', hF, hF', ext_of_map_eq m₁ m₂ n₁ n₂ f F d d' e e' hdφ hdφ' heφ heφ' hFf,
    ext_of_map_eq n₁ n₂ m₁ m₂ f' F' d' d e' e hdφ' hdφ heφ' heφ hFf', fun N h => ?_, fun N h => ?_,
    fun h a => ?_, fun h a => ?_⟩
  · refine inj _ _ _ _ inferInstance (hpow G N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f f' N h
  · refine inj _ _ _ _ inferInstance (hpow G' N) ?_
    rw [Functor.map_comp, hFf, hFf', pullback_map_id_pow]
    exact conj_comp_eq_id_pow _ _ f' f N h
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf]
    exact conj_comm e d e' d' f _ _ _ _ _ _ (hda a) (hea a) (hda' a) (hea' a) (h a)
  · have := G.act.hom a
    have := G'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [Functor.map_comp, Functor.map_comp, hFf']
    exact conj_comm e' d' e d f' _ _ _ _ _ _ (hda' a) (hea' a) (hda a) (hea a) (h a)

end GlobalTheory.HkIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteEtaleAlgebraPullbackAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_finiteEtale_algebra_pullback : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X), IsFinite π → Etale π → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (h : Sp B ⟶ Y), Module.Finite R B ∧ Algebra.Etale R B ∧ h ≫ π = spMap (algebraMap R B) ≫ x ∧ (Surjective π → Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) ∧ ∀ (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (w : Sp Ω ⟶ Y), w ≫ π = spMap φ ≫ x → ∃! χ : B →+* Ω, χ.comp (algebraMap R B) = φ ∧ spMap χ ≫ h = w := by
  intro X Y π hfin het R _ x
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := S)
    (e.hom ≫ pullback.snd π x)
  letI : Algebra R S := f.hom.toAlgebra
  have hsp : spMap (algebraMap R S) = e.hom ≫ pullback.snd π x := hf
  refine ⟨S, inferInstance, inferInstance, e.hom ≫ pullback.fst π x, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  · have h1 : Etale (Spec.map f) := by rw [hf]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 h1)
  · rw [hsp, Category.assoc, Category.assoc, pullback.condition]
  · intro hs
    have h1 : Surjective (Spec.map f) := by rw [hf]; infer_instance
    exact h1.surj
  · intro Ω _ φ w hw
    obtain ⟨g, hg⟩ := Spec.map_surjective (R := S) (S := CommRingCat.of Ω)
      (pullback.lift w (spMap φ) hw ≫ e.inv)
    have key : ∀ χ : S →+* Ω, χ.comp (algebraMap R S) = φ ↔
        spMap χ ≫ e.hom ≫ pullback.snd π x = spMap φ := by
      intro χ
      rw [← hsp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      constructor
      · intro h; rw [h]
      · intro h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hg' : spMap g.hom = pullback.lift w (spMap φ) hw ≫ e.inv := hg
    refine ⟨g.hom, ⟨(key _).2 ?_, ?_⟩, ?_⟩
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    · rw [hg', Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]
    · rintro χ ⟨h1, h2⟩
      have h3 : spMap χ = spMap g.hom := by
        rw [hg', Iso.eq_comp_inv]
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.assoc]; exact h2
        · rw [pullback.lift_snd, Category.assoc]; exact (key _).1 h1
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.SmoothLocalDescent

theorem eq_of_forall_geom {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem exists_factor_pi {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [∀ i, CommRing (A i)] {k : Type} [CommRing k] [IsDomain k] (χ : (∀ i, A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ x, χ x = ψ (x i) := by
  first
  | exact @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | (apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection ..)


open scoped TensorProduct in
theorem exists_lift_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (k ⊗[R] S) := inferInstance
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)


open scoped TensorProduct in
theorem exists_preimage_of_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R S
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_forall_geom _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_finite_cover (K B : Type) [CommRing K] [CommRing B] [Algebra K B]
    [_root_.IsReduced B]
    (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω)
    {J : Type} [Fintype J] [DecidableEq J] (A : J → Type) [∀ i, CommRing (A i)]
    [∀ i, Algebra B (A i)] [∀ i, Algebra K (A i)] [∀ i, IsScalarTower K B (A i)]
    [∀ i, Algebra.Smooth B (A i)] (a : ∀ i, A i)
    (hcov : ∀ q : PrimeSpectrum B, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (A i))))
    (hval : ∀ i (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : A i →ₐ[K] Ω),
      χ' (a i) = F Ω (χ'.comp (IsScalarTower.toAlgHom K B (A i)))) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  haveI : Algebra.Smooth B (∀ i, A i) := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat B (∀ i, A i) := inferInstance
  haveI : Module.FaithfullyFlat B (∀ i, A i) := by
    refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, Q, hQ⟩ := hcov p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) Q, ?_⟩
    rw [← hQ]
    rfl

  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : (∀ i, A i) →+* Ω),
      (∀ x : K, χ' (algebraMap B (∀ i, A i) (algebraMap K B x)) = algebraMap K Ω x) →
      ∃ ρ : B →ₐ[K] Ω, (∀ y, ρ y = χ' (algebraMap B (∀ i, A i) y)) ∧ χ' a = F Ω ρ := by
    intro Ω _ _ _ χ' hK
    obtain ⟨i, ψ, hψ⟩ := exists_factor_pi A χ'
    have hB : ∀ y, ψ (algebraMap B (A i) y) = χ' (algebraMap B (∀ i, A i) y) := fun y => by
      rw [hψ]; rfl
    have hc : ∀ x : K, ψ (algebraMap K (A i) x) = algebraMap K Ω x := fun x => by
      rw [IsScalarTower.algebraMap_apply K B (A i), hB, hK]
    let ψa : A i →ₐ[K] Ω := { ψ with commutes' := hc }
    refine ⟨ψa.comp (IsScalarTower.toAlgHom K B (A i)), fun y => hB y, ?_⟩
    rw [hψ]
    exact hval i Ω ψa
  obtain ⟨b, hb⟩ := exists_preimage_of_geom B (∀ i, A i) a fun k _ _ χ₁ χ₂ h12 => by
    letI : Algebra K k := (χ₁.comp ((algebraMap B (∀ i, A i)).comp (algebraMap K B))).toAlgebra
    have h12' : ∀ y, χ₁ (algebraMap B (∀ i, A i) y) = χ₂ (algebraMap B (∀ i, A i) y) :=
      fun y => RingHom.congr_fun h12 y
    obtain ⟨ρ₁, hρ₁, e₁⟩ := key k χ₁ fun x => rfl
    obtain ⟨ρ₂, hρ₂, e₂⟩ := key k χ₂ fun x => (h12' _).symm
    have : ρ₁ = ρ₂ := AlgHom.ext fun y => by rw [hρ₁, hρ₂, h12']
    rw [e₁, e₂, this]
  refine ⟨b, fun Ω _ _ _ χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_lift_geom B (∀ i, A i) Ω χ.toRingHom
  have hχ'y : ∀ y, χ' (algebraMap B (∀ i, A i) y) = χ y := fun y => RingHom.congr_fun hχ' y
  obtain ⟨ρ, hρ, e⟩ := key Ω χ' fun x => by rw [hχ'y]; exact χ.commutes x
  have : ρ = χ := AlgHom.ext fun y => by rw [hρ, hχ'y]
  rw [← this, ← e, ← hb, hρ]

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_smooth_locally : ∀ (K B : Type) [CommRing K] [CommRing B] [Algebra K B] [IsReduced B] (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω), (∀ q : PrimeSpectrum B, ∃ (B' : Type) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra K B') (_ : IsScalarTower K B B') (b' : B'), Algebra.Smooth B B' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : B' →ₐ[K] Ω), χ' b' = F Ω (χ'.comp (IsScalarTower.toAlgHom K B B'))) → ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  intro K B _ _ _ _ F h
  choose B' iR iB iK iT b' hsm hq hval using h
  letI : ∀ q, CommRing (B' q) := iR
  letI : ∀ q, Algebra B (B' q) := iB
  letI : ∀ q, Algebra K (B' q) := iK
  haveI : ∀ q, IsScalarTower K B (B' q) := iT
  haveI : ∀ q, Algebra.Smooth B (B' q) := hsm
  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun q =>
    Set.range (PrimeSpectrum.comap (algebraMap B (B' q)))
  have hopen : ∀ q, IsOpen (U q) := fun q => by
    have := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := B) (S := B' q) _ isOpen_univ
    rwa [Set.image_univ] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen
    (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  classical
  exact exists_of_finite_cover K B F (J := t) (fun i => B' i.1) (fun i => b' i.1)
    (fun q => by
      obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      exact ⟨⟨i, hi⟩, hqi⟩)
    (fun i => hval i.1)

end GlobalTheory.SmoothLocalDescent
end

