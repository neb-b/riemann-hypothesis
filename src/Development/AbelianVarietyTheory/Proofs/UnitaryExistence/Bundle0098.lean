module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ringHom_ext {l : Level H} (hA : l.A = 1) {f f' : KA l →+* ℂ} (h : f (baseKA l).ρ = f' (baseKA l).ρ) :
    f = f' := by
  have hz : zeta l.A = 1 := by
    unfold zeta
    rw [hA]
    simp
  suffices key : ∀ (x : ℂ) (hx : x ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ)),
      f ⟨x, hx⟩ = f' ⟨x, hx⟩ by
    ext y
    exact key y.1 y.2
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h
    · exact (congrArg f (Subtype.ext hz)).trans ((map_one f).trans
        ((map_one f').symm.trans (congrArg f' (Subtype.ext hz)).symm))
  | algebraMap r =>
    show f (algebraMap ℚ (KA l) r) = f' (algebraMap ℚ (KA l) r)
    rw [eq_ratCast (algebraMap ℚ (KA l)) r, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ + ⟨y, hy⟩) = f' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add (f := _), map_add (f := _), ihx, ihy]
  | inv x hx ih =>
    show f (⟨x, hx⟩⁻¹) = f' (⟨x, hx⟩⁻¹)
    rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ * ⟨y, hy⟩) = f' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

theorem valAt'_top {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' x ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom f) := by
  unfold valAt'
  rw [dite_eq_left (by simp)]
  unfold valAt
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_spMap_comp {X : Scheme.{0}} (τ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' (spMap τ ≫ x) ⊤ f = τ (valAt' x ⊤ f) := by
  rw [valAt'_top, valAt'_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ)
  have h2 := congrArg (fun φ => φ.hom (x.appTop.hom f)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [spMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  exact h2

theorem valAt'_idem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {e : Γ(X, ⊤)} (he : e * e = e) :
    valAt' x ⊤ e ∈ ({0, 1} : Set ℂ) := by
  rw [valAt'_top]
  have h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) *
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) := by
    rw [← map_mul, ← map_mul, he]
  generalize (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) = v at h ⊢
  have h2 : v * (v - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.1 h1]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_period (F : FamilyUnif Xo σ ty) (hty : IsTypeFn H D.p D.q ty) (i : Fin F.n) :
    ∃ P, IsPeriod (F.Di i) ty P := by
  obtain ⟨hp, hq⟩ := F.sig i
  exact GlobalTheory.PeriodNonempty.exists_isPeriod E H (F.Di i) g ty (by rw [hp, hq]; exact hty)

private theorem key_lemma' (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0)
    (i k k' : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (Q : (F.Di k).La →+ (Fin g → ℂ))
    (Q' : (F.Di k').La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hQ : IsPeriod (F.Di k) ty Q) (hQ' : IsPeriod (F.Di k') ty Q')
    (h1 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u k Q) (h2 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P' = F.u k' Q') :
    k' = k := by
  classical
  obtain ⟨c, -, he⟩ := _root_.GlobalTheory.CompRat.exists_coeff_idempotent_functions E H D l Xo σ g ty F hD hσ hty hA (Classical.arbitrary _)
  obtain ⟨e, hee, hev⟩ := he k
  have hs : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  have hjc : σ = ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom).comp
      (IntermediateField.inclusion c.le).toRingHom :=
    ringHom_ext hA (hσ.trans hs.symm)
  have hw : F.u i P ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P hP, spMap_comp, ← hjc]
  have hw' : F.u i P' ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P' hP', spMap_comp, ← hjc]
  have hsnd : spMap (τ : ℂ →+* ℂ) ≫ spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) =
      spMap c.F.val.toRingHom := by
    rw [spMap_comp]
    congr 1
    ext z
    simp
  have hv1 := hev k Q hQ (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P) _ hw)
    (by rw [Category.assoc, pullback.lift_fst]; exact h1)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have hv2 := hev k' Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P') _ hw')
    (by rw [Category.assoc, pullback.lift_fst]; exact h2)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values E H D l Xo σ g ty F hD hσ hty hA c
    ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) e {0, 1}
    (Set.toFinite _) (fun y _ => valAt'_idem y hee) i P P' hP hP'
    (pullback.lift (F.u i P) _ hw) (pullback.lift (F.u i P') _ hw')
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [valAt'_spMap_comp, if_pos rfl] at hv1
  rw [valAt'_spMap_comp, ← heq, hv1] at hv2
  by_contra hne
  rw [if_neg hne] at hv2
  exact one_ne_zero hv2

private theorem spMap_comp_u_comp_s_eq_of_fixes_rt0 (F : FamilyUnif Xo σ ty) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1)
    (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : (spMap (τ : ℂ →+* ℂ) ≫ F.u i P) ≫ Xo.s = spMap σ := by
  rw [Category.assoc, F.10 i P hP, spMap_comp]
  congr 1
  exact ringHom_ext hA (by rw [RingHom.comp_apply, hσ]; exact hτ)

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  classical
  choose P0 hP0 using fun i => exists_period F hty i
  choose k Q hQ hkQ using fun i => F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i (P0 i) (hP0 i))
  refine ⟨k, fun i P hP => ?_⟩
  obtain ⟨k', Q', hQ', hk'⟩ := F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i P hP)
  have hkk := key_lemma' F hD hσ hty hA τ hτ i (k i) k' (P0 i) P (Q i) Q' (hP0 i) hP (hQ i) hQ'
    (hkQ i).symm hk'.symm
  subst hkk
  exact ⟨Q', hQ', hk'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  have hτ' : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm hτ'
  have hinv : ∀ i, π' (π i) = i := by
    intro i
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨Q, hQ, h1⟩ := hπ i P hP
    obtain ⟨R, hR, h2⟩ := hπ' (π i) Q hQ
    have h3 : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
      rw [← Category.assoc, spMap_comp]
      have hid : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by
        ext z
        simp
      rw [hid]
      unfold spMap
      simp
    rw [h1, h2] at h3
    exact F.19 _ _ _ _ hR hP h3
  have hinj : Function.Injective π := fun a b hab => by rw [← hinv a, ← hinv b, hab]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, hπ⟩

end GlobalTheory.ConjPermutes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem rt0_im_ne_zero (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0.im ≠ 0 := by
  intro h
  have hd : H.d ≠ 0 := by
    have := H.2
    omega
  have hpos : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have := congrArg Complex.re H.sqrt_neg_disc_sq
  simp [sq, Complex.mul_re, h] at this
  nlinarith [mul_self_nonneg H.rt0.re]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem embedding_rt_eq_or_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ H.rt = H.rt0 ∨ τ H.rt = -H.rt0 := by
  have hsq : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    push_cast at this
    exact this
  have h2 : (τ H.rt) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsq, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem exists_pos_form_rt_eq_im_mul {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ}
    {P : D.La →+ (Fin g → ℂ)} (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (c : ℂ)
    (hc : ∀ x, P (H.rt • x) = c • P x) {a : D.La} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (((D.EF (H.rt • a)) a : ℤ) : ℝ) = c.im * r := by
  obtain ⟨-, hinj, -, -, Hm, -, hpos, hform⟩ := hP
  have hPa : P a ≠ 0 := fun h => ha (hinj (h.trans (map_zero P).symm))
  refine ⟨(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).re, hpos _ hPa, ?_⟩
  have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).im = 0 := by
    rw [hform, D.alt, Int.cast_zero]
  rw [← hform, hc]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm] at h0 ⊢
  rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, h0]
  ring


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.CompRat.splitLat_of_definite : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H),
    D.p = 0 ∨ D.q = 0 → _root_.GlobalTheory.CompRat.SplitLat D := by
  intro E _ _ _ H D hpq
  obtain ⟨g, ty, hty⟩ := _root_.GlobalTheory.PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  have hscal : ∀ c : ℂ, (∀ i, ty i H.rt = c) → ∀ x, P (H.rt • x) = c • P x := by
    intro c hc x
    funext i
    rw [hP.1, hc]
    rfl
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := by
    intro i
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne'
  have him := rt0_im_ne_zero H
  have hsq := mul_self_pos.2 him
  unfold _root_.GlobalTheory.CompRat.SplitLat
  rcases hpq with hp | hq
  · have hc : ∀ i, ty i H.rt = -H.rt0 := by
      intro i
      rcases embedding_rt_eq_or_eq_neg H (ty i) with h | h
      · exact absurd ((hty (ty i)).1 h) (by rw [hp]; exact hcard i)
      · exact h
    refine ⟨⊥, ⊤, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b _
      rw [(Submodule.mem_bot _).1 ha]
      simp
    · rw [finrank_bot, hp]
    · rw [finrank_top, D.rank, hp, zero_add]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he, Complex.neg_im]
      nlinarith [mul_pos hsq hr]
  · have hc : ∀ i, ty i H.rt = H.rt0 := by
      intro i
      by_contra h
      exact absurd ((hty (ty i)).2 h) (by rw [hq]; exact hcard i)
    refine ⟨⊤, ⊥, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a _ b hb
      rw [(Submodule.mem_bot _).1 hb]
      simp
    · rw [finrank_top, D.rank, hq, add_zero]
    · rw [finrank_bot, hq]
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he]
      nlinarith [mul_pos hsq hr]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dict_invariant : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  have last : ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
    intro g k γ hm
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hu := _root_.GlobalTheory.MarkUniq.mark_unique D H Dw l Xo c σ V r C hC g
    have hk : (dict g).1 = k := hu.1 _ _ _ _ hm₀ hm
    subst hk
    obtain ⟨δ, hδ, he⟩ := hu.2 _ γ γ₀ hm hm₀
    refine ⟨δ, hδ, ?_⟩
    rw [← he, ← hf]
  refine ⟨?_, ?_, ?_, ?_, last⟩
  · intro γ hγ g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hm := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).1 γ hγ
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, mul_assoc, inv_mul_cancel_left]
  · intro k hk g
    obtain ⟨γ₀, hm₀, hf⟩ := hd.1 g
    have hk' := (hK k).1 hk
    have hm := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ₀ hm₀).2.1 k hk'.2
    obtain ⟨δ, hδ, he⟩ := last _ _ _ hm
    refine ⟨δ, hδ, ?_⟩
    rw [he, hf, ← mul_assoc,
      (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.2.2.1 k hk'.1]
  · intro g
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.1
  · intro g τ i
    obtain ⟨γ₀, -, hf⟩ := hd.1 g
    rw [hf]
    exact (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ₀ * g) (dict g).1).2.2.1 τ i

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryRealEquivariantOntoTriangular
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem frame_rmul_lact {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (γ : GL (Fin r) E) (x b : Frame Ψ r) : rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  exact Matrix.mul_assoc (α := ℂ) _ (mat x τ) (mat b τ)

theorem dict_eq_of_mark (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) (hd : C.IsDict dict) (g : GA D V) (k : Fin C.F.n)
    (γ : GA D V) (hm : C.Mark g k γ) :
    ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  obtain ⟨γ', hm', he⟩ := hd.1 g
  have hu := _root_.GlobalTheory.MarkUniq.mark_unique D H Dw l Xo c σ V r C hC g
  have hk : k = (dict g).1 := hu.1 _ _ _ _ hm hm'
  subst hk
  obtain ⟨δ, hδ, e⟩ := hu.2 _ _ _ hm hm'
  refine ⟨δ, hδ, ?_⟩
  rw [← e, ← he]

theorem dict_real_equivariant_onto : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V C.th C.hr (fun k => C.fr 1 k) h (dict g).1))⟩) ∧ ∀ k, ∀ x ∈ (C.M.X k).dom, ∃ g, ∃ γ ∈ (C.M.X k).Γ, ∃ b ∈ Bor (C.M.X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd
  refine ⟨fun g h hh => ?_, fun k x hx => ?_⟩
  · obtain ⟨γ, hm, he⟩ := hd.1 g
    have hm2 := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC g _ γ hm).2.2.1 h hh
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (g * h) _ γ hm2
    refine ⟨δ, hδ, ?_⟩
    rw [e, ← mul_assoc, (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC (γ * g) _).2.2.2.2.2.1 h, ← he]
  · obtain ⟨x₀, b, hb, ho, hx₀⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E r
      (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm).1 x hx
    obtain ⟨u, hu, hux⟩ := (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.2.2 x₀ ho
    obtain ⟨f, hf, hm⟩ := _root_.GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC k
    have hm2 := (_root_.GlobalTheory.Member.mark_move D H Dw l Xo c σ V r C hC f k 1 hm).2.2.1 u hu
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (f * u) k 1 hm2
    refine ⟨f * u, δ, hδ, b, hb, ?_⟩
    rw [e, one_mul, ← (_root_.GlobalTheory.UnitarySplit.real_finite_split D V).2.1 u hu f hf,
      (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC u k).2.2.2.2.1 f hf, hux, hx₀, frame_rmul_lact]

end GlobalTheory.Member
end

