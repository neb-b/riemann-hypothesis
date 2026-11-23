module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerOfIsPushout
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.ProdLift

def derHom {S B : Type} [CommRing S] [CommRing B] (a : S →+* B) (δ : S → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = a x * δ y + a y * δ x) :
    S →+* DualNumber B where
  toFun x := TrivSqZeroExt.inl (a x) + TrivSqZeroExt.inr (δ x)
  map_one' := by
    have h' := hmul 1 1
    rw [_root_.mul_one, map_one, _root_.one_mul] at h'
    have h : δ 1 = 0 := left_eq_add.mp h'
    ext <;> simp [h]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero, left_eq_add] at h
    ext <;> simp [h]
  map_add' x y := by ext <;> simp [hadd]
  map_mul' x y := by ext <;> simp [hmul, mul_comm]

theorem exists_der_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (δ : S → B) (δ' : T → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = a (u.hom x) * δ y + a (u.hom y) * δ x)
    (hadd' : ∀ x y, δ' (x + y) = δ' x + δ' y)
    (hmul' : ∀ x y, δ' (x * y) = a (v.hom x) * δ' y + a (v.hom y) * δ' x)
    (hR : ∀ r, δ (i.hom r) = δ' (j.hom r)) :
    ∃ d : P → B, (∀ x y, d (x + y) = d x + d y) ∧ (∀ x y, d (x * y) = a x * d y + a y * d x) ∧
      (∀ x, d (u.hom x) = δ x) ∧ ∀ x, d (v.hom x) = δ' x := by
  let φ₁ : S →+* DualNumber B := derHom (a.comp u.hom) δ hadd hmul
  let φ₂ : T →+* DualNumber B := derHom (a.comp v.hom) δ' hadd' hmul'
  have hw : i ≫ CommRingCat.ofHom φ₁ = j ≫ CommRingCat.ofHom φ₂ := by
    ext r
    have e : u.hom (i.hom r) = v.hom (j.hom r) := by
      rw [← CommRingCat.comp_apply, po.w, CommRingCat.comp_apply]
    · simp [φ₁, φ₂, derHom, e]
    · simp [φ₁, φ₂, derHom, hR]
  let Φ := po.desc (CommRingCat.ofHom φ₁) (CommRingCat.ofHom φ₂) hw
  have hΦu : ∀ x, Φ.hom (u.hom x) = φ₁ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inl_desc]
    rfl
  have hΦv : ∀ x, Φ.hom (v.hom x) = φ₂ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inr_desc]
    rfl
  have hfst : Φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom = CommRingCat.ofHom a := by
    apply po.hom_ext
    · ext x
      simp [hΦu, φ₁, derHom]
    · ext x
      simp [hΦv, φ₂, derHom]
  have hf : ∀ x, (Φ.hom x).fst = a x := fun x => by
    have := congrArg (fun g => g.hom x) hfst
    simpa using this
  refine ⟨fun x => (Φ.hom x).snd, fun x y => ?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · simp
  · simp only [map_mul, TrivSqZeroExt.snd_mul, hf, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring
  · simp [hΦu, φ₁, derHom]
  · simp [hΦv, φ₂, derHom]

theorem der_eq_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (d d' : P → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = a x * d y + a y * d x)
    (hadd' : ∀ x y, d' (x + y) = d' x + d' y)
    (hmul' : ∀ x y, d' (x * y) = a x * d' y + a y * d' x)
    (hu : ∀ x, d (u.hom x) = d' (u.hom x)) (hv : ∀ x, d (v.hom x) = d' (v.hom x)) : d = d' := by
  have hext : u ≫ CommRingCat.ofHom (derHom a d hadd hmul) = u ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') ∧
      v ≫ CommRingCat.ofHom (derHom a d hadd hmul) = v ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') := by
    constructor
    · ext x
      · simp [derHom]
      · simp [derHom, hu]
    · ext x
      · simp [derHom]
      · simp [derHom, hv]
  have hφ := po.hom_ext hext.1 hext.2
  funext x
  have := congrArg (fun g => (g.hom x).snd) hφ
  simpa [derHom] using this

theorem pbT_eq {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  rw [dite_eq_left h]

theorem appLE_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R)
    (f : Y ⟶ X) (hf : f ≫ q = q') {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  unfold constFn
  have e := Scheme.Hom.appLE_comp_appLE f q ⊤ U V (by simp) h
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

theorem app_appLE {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W)
    (h' : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W) (f : Γ(X, W)) :
    (m₂.app Q).hom ((p.appLE W Q h).hom f) = (p₀.appLE _ _ h').hom ((m.app W).hom f) := by
  have key : ∀ (g g' : Z₀ ⟶ X) (e : g = g') (h₁ : m₂ ⁻¹ᵁ Q ≤ g ⁻¹ᵁ W) (h₂ : m₂ ⁻¹ᵁ Q ≤ g' ⁻¹ᵁ W),
      (g.appLE W (m₂ ⁻¹ᵁ Q) h₁).hom f = (g'.appLE W (m₂ ⁻¹ᵁ Q) h₂).hom f := by
    rintro g _ rfl _ _
    rfl
  have e₁ := Scheme.Hom.appLE_comp_appLE m₂ p W Q (m₂ ⁻¹ᵁ Q) h le_rfl
  have e₂ := Scheme.Hom.appLE_comp_appLE p₀ m W (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) le_rfl h'
  rw [Scheme.Hom.app_eq_appLE m₂, Scheme.Hom.app_eq_appLE m]
  have l₁ := congrArg (fun g => g.hom f) e₁
  have l₂ := congrArg (fun g => g.hom f) e₂
  simp only [CommRingCat.comp_apply] at l₁ l₂
  rw [l₁, l₂]
  exact key _ _ hp _ _

theorem preimage_le {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W) :
    m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := by
  intro x hx
  have h₁ : p (m₂ x) ∈ W := h hx
  change m (p₀ x) ∈ W
  rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
  exact h₁

theorem finiteRing_sq_sub_mul_sq_eq_of_card {K : Type} [Field K] {R : Type} [CommRing R] {Z Z₀ X Y : Scheme.{0}}
    {p q : Z ⟶ X} {s : X ⟶ Sp R} (H : IsPullback p q s s) {z : Z ⟶ Sp R} (hz : p ≫ s = z)
    {p₀ q₀ : Z₀ ⟶ Y} {s₀ : Y ⟶ Sp K} {z₀ : Z₀ ⟶ Sp K} (hp₀ : p₀ ≫ s₀ = z₀) (hq₀ : q₀ ≫ s₀ = z₀)
    {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z} (hp : m₂ ≫ p = p₀ ≫ m) (hq : m₂ ≫ q = q₀ ≫ m) (D : R → K)
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (Q : Z.Opens)
    (hQ : Q = p ⁻¹ᵁ W ⊓ q ⁻¹ᵁ W') :
    (∀ d d', LocDerK s₀ s m D W d → LocDerK s₀ s m D W' d' → ∃ d₂, LocDerK z₀ z m₂ D Q d₂ ∧
      (∀ f, d₂ Q (pbT p f Q) = pbT p₀ (d W f) _) ∧ ∀ f, d₂ Q (pbT q f Q) = pbT q₀ (d' W' f) _) ∧
    ∀ d₂ d₂', LocDerK z₀ z m₂ D Q d₂ → LocDerK z₀ z m₂ D Q d₂' →
      (∀ f : Γ(X, W), d₂ Q (pbT p f Q) = d₂' Q (pbT p f Q)) →
      (∀ f : Γ(X, W'), d₂ Q (pbT q f Q) = d₂' Q (pbT q f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  have hWQ : Q ≤ p ⁻¹ᵁ W := by rw [hQ]; exact inf_le_left
  have hW'Q : Q ≤ q ⁻¹ᵁ W' := by rw [hQ]; exact inf_le_right
  have h₁ : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := preimage_le hp hWQ
  have h₂ : m₂ ⁻¹ᵁ Q ≤ q₀ ⁻¹ᵁ m ⁻¹ᵁ W' := preimage_le hq hW'Q
  have hz' : q ≫ s = z := H.w.symm.trans hz
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have : IsAffine (⊤ : (Sp R).Opens).toScheme := isAffineOpen_top (Sp R)
  have hPb := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W') (UX := W) (by simp) (by simp) hQ
  have : IsAffine Q.toScheme := IsAffine.of_isPullback hPb
  have hQa : IsAffineOpen Q := this
  have hPo : IsPushout (s.appLE ⊤ W (by simp)) (s.appLE ⊤ W' (by simp)) (p.appLE W Q hWQ)
      (q.appLE W' Q hW'Q) :=
    (isPushout_appTop_of_isPullback hPb).of_iso (Scheme.Opens.topIso ⊤) W.topIso W'.topIso Q.topIso
      (Arrow.w (arrowResLEAppIso s ⊤ W _).hom).symm (Arrow.w (arrowResLEAppIso s ⊤ W' _).hom).symm
      (Arrow.w (arrowResLEAppIso p W Q _).hom).symm (Arrow.w (arrowResLEAppIso q W' Q _).hom).symm
  refine ⟨fun d d' hd hd' => ?_, fun d₂ d₂' e₁ e₂ ef ef' O hO => ?_⟩
  · let δ : Γ(X, W) → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (p₀.appLE (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) h₁).hom (d W f)
    let δ' : Γ(X, W') → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (q₀.appLE (m ⁻¹ᵁ W') (m₂ ⁻¹ᵁ Q) h₂).hom (d' W' f)
    have hb : ∀ r, δ (constFn s W r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ]
      rw [hd.base W le_rfl r]
      exact appLE_constFn s₀ z₀ p₀ hp₀ h₁ (D r)
    have hb' : ∀ r, δ' (constFn s W' r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ']
      rw [hd'.base W' le_rfl r]
      exact appLE_constFn s₀ z₀ q₀ hq₀ h₂ (D r)
    have hR : ∀ r, δ ((s.appLE ⊤ W (by simp)).hom r) = δ' ((s.appLE ⊤ W' (by simp)).hom r) := by
      intro r
      obtain ⟨r', rfl⟩ : ∃ r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r' = r :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, by simp⟩
      change δ (constFn s W r') = δ' (constFn s W' r')
      rw [hb, hb']
    obtain ⟨d0, hadd0, hmul0, hu0, hv0⟩ := exists_der_of_isPushout hPo (m₂.app Q).hom δ δ'
      (fun x y => by simp only [δ]; rw [hd.add W le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ]
        rw [hd.mul W le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hp hWQ h₁ x, app_appLE hp hWQ h₁ y])
      (fun x y => by simp only [δ']; rw [hd'.add W' le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ']
        rw [hd'.mul W' le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hq hW'Q h₂ x, app_appLE hq hW'Q h₂ y])
      hR
    have hbQ : ∀ r, d0 (constFn z Q r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      rw [← appLE_constFn s z p hz hWQ r, hu0, hb]
    obtain ⟨d₂, hd₂, hd₂Q⟩ := GlobalTheory.LocDerExtK.exists_locDerK K R Z₀ Z z₀ z m₂ D Q hQa d0 hadd0 hmul0 hbQ
    refine ⟨d₂, hd₂, fun f => ?_, fun f => ?_⟩
    · rw [hd₂Q, pbT_eq p f hWQ, hu0, pbT_eq p₀ _ h₁]
    · rw [hd₂Q, pbT_eq q f hW'Q, hv0, pbT_eq q₀ _ h₂]
  · refine GlobalTheory.LocDerExtK.locDerK_unique hQa d₂ d₂' e₁ e₂ ?_ O hO
    exact der_eq_of_isPushout hPo (m₂.app Q).hom (d₂ Q) (d₂' Q) (e₁.add Q le_rfl) (e₁.mul Q le_rfl)
      (e₂.add Q le_rfl) (e₂.mul Q le_rfl)
      (fun x => by rw [← pbT_eq p x hWQ]; exact ef x) (fun x => by rw [← pbT_eq q x hW'Q]; exact ef' x)

theorem main : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (A : Over (Sp R)) (A₀ : Over (Sp K)) (m : A₀.left ⟶ A.left) (m₂ : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left) (D : R → K) (W W' : A.left.Opens), m ≫ A.hom = A₀.hom ≫ spMap x₀ → IsSquare m m₂ → IsAffineOpen W → IsAffineOpen W' → ∀ Q, Q = (fst A A).left ⁻¹ᵁ W ⊓ (snd A A).left ⁻¹ᵁ W' → (∀ d d', LocDerK A₀.hom A.hom m D W d → LocDerK A₀.hom A.hom m D W' d' → ∃ d₂, LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ ∧ (∀ f, d₂ Q (pbT (fst A A).left f Q) = pbT (fst A₀ A₀).left (d W f) _) ∧ ∀ f, d₂ Q (pbT (snd A A).left f Q) = pbT (snd A₀ A₀).left (d' W' f) _) ∧ ∀ d₂ d₂', LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ → LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂' → (∀ f : Γ(A.left, W), d₂ Q (pbT (fst A A).left f Q) = d₂' Q (pbT (fst A A).left f Q)) → (∀ f : Γ(A.left, W'), d₂ Q (pbT (snd A A).left f Q) = d₂' Q (pbT (snd A A).left f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  intro K _ R _ x₀ A A₀ m m₂ D W W' _ hsq hW hW' Q hQ
  obtain ⟨hs₁, hs₂⟩ := hsq
  exact finiteRing_sq_sub_mul_sq_eq_of_card (Over.isPullback_of_binaryFan_isLimit _
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A A))
    (Over.w (fst A A)) (Over.w (fst A₀ A₀)) (Over.w (snd A₀ A₀)) hs₁ hs₂ D hW hW' Q hQ

end GlobalTheory.KS.ProdLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem finrank_int_eq_mul (O M : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := M) le_rfl
  let F : Submodule O M := Submodule.span O (Set.range f)
  let bF : Module.Basis (Fin (Module.finrank O M)) O F := Module.Basis.span hf
  have : Module.Free O F := Module.Free.of_basis bF
  have h1 : Module.finrank O F = Module.finrank O M := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have h2 : Module.finrank O (M ⧸ F) = 0 := by
    have := Submodule.finrank_quotient_add_finrank F
    omega
  have h3 : Module.finrank ℤ (M ⧸ F.restrictScalars ℤ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h2 ⊢
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hax⟩ := h2 (Submodule.Quotient.mk x)
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨r, hr, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax ⊢
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul O r x, hc, mul_comm, mul_smul]
    exact F.smul_mem c hax
  have h4 := Submodule.finrank_quotient_add_finrank (F.restrictScalars ℤ)
  have h5 : Module.finrank ℤ (F.restrictScalars ℤ) = Module.finrank ℤ O * Module.finrank O F :=
    (Module.finrank_mul_finrank ℤ O F).symm
  rw [← h4, h3, zero_add, h5, h1]

theorem finrank_int_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  have := D.fin
  rw [finrank_int_eq_mul (𝓞 E) D.La, D.rank, RingOfIntegers.rank, IsTotallyComplex.finrank E,
    Nat.mul_div_cancel_left _ two_pos, Nat.mul_assoc]

theorem exists_equiv_stdSymp {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hp : Function.Bijective B) {g : ℕ}
    (hg : Module.finrank ℤ M = 2 * g) :
    ∃ bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M,
      ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j := by
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  have hl : ∀ i, ((e (Sum.inl i) : Fin (2 * g)) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e (Sum.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => by simp [e]; omega
  refine ⟨(b.reindex e).equivFun.symm, fun i j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have hs : ∀ k, (b.reindex e).equivFun.symm (Pi.single (e k) 1) = b k := fun k => by
    rw [Module.Basis.equivFun_symm_apply]; simp [Pi.single_apply]
  rw [hs, hs, Out.stdSymp]
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2
  · rw [hb.left_left, hl, hl, if_neg (by omega), if_neg (by omega)]
  · rw [hb.left_right, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_left hB, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_right, hr, hr, if_neg (by omega), if_neg (by omega)]

theorem exists_isSympBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    ∃ bas : (Fin (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La, IsSympBasis D bas := by
  intro E _ _ _ H D
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  exact exists_equiv_stdSymp D.alt D.unimod (finrank_int_lattice D)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.FibreAct

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G' ⟶ G) [IsIso ψ]
    [IsMonHom ψ] : IsGrpPullback G' G (𝟙 S) ψ.left := by
  haveI : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget S).map ψ))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let U : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = U ≫ x ≫ ψ := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have ey : y₀ = U ≫ y ≫ ψ := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem exists_lift_act {O : Type} [CommRing O] {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  have w : ∀ c, (φ ≫ (a.act c).left) ≫ G.hom = G'.hom ≫ f := fun c => by
    rw [Category.assoc, Over.w, h.1.w]
  let r : O → (G' ⟶ G') := fun c => Over.homMk (h.1.lift (φ ≫ (a.act c).left) G'.hom (w c)) (h.1.lift_snd _ _ _)
  have hr : ∀ c, (r c).left ≫ φ = φ ≫ (a.act c).left := fun c => h.1.lift_fst _ _ _
  have key : ∀ T : Over S', ∃ e : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G),
      ∀ x c, e (x ≫ r c) = e x ≫ a.act c := fun T => by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h T _ rfl
    exact ⟨e, fun x c => Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hr, Category.assoc])⟩
  obtain ⟨e, he⟩ := key G'
  have he' : ∀ c, e (r c) = e (𝟙 G') ≫ a.act c := fun c => by rw [← he, Category.id_comp]
  refine ⟨⟨r, fun c => ?_, e.injective ?_, fun c d => e.injective ?_, fun c d => e.injective ?_⟩, hr⟩
  · haveI := a.hom c
    refine ⟨?_, ?_⟩
    · obtain ⟨e₁, he₁⟩ := key (𝟙_ (Over S'))
      have o : η[G'] = (1 : 𝟙_ (Over S') ⟶ G') := by rw [Hom.one_def]; simp
      apply e₁.injective
      rw [he₁, o, map_one, MonObj.one_comp]
    · obtain ⟨e₂, he₂⟩ := key (G' ⊗ G')
      have m₁ : μ[G'] = fst G' G' * snd G' G' := by rw [Hom.mul_def]; simp
      have m₂ : (r c ⊗ₘ r c) ≫ μ[G'] = (fst G' G' ≫ r c) * (snd G' G' ≫ r c) := by
        rw [Hom.mul_def]; congr 1
      apply e₂.injective
      rw [m₂, he₂, m₁, map_mul, map_mul, he₂, he₂, MonObj.mul_comp]
  · rw [he', a.one, Category.comp_id]
  · rw [he, he', he', a.mul, Category.assoc]
  · rw [map_mul, he', he', he', a.add, MonObj.comp_mul]

theorem exists_fibre_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (τ : SAB H S) (x : Sp ℂ ⟶ S) (β : o →+* ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (m : A₀.left ⟶ t.A.left), IsPEL D a bas ρ t τ → x ≫ s = spMap β → IsGrpPullback A₀ t.A x m → ∃ (act : OAct (𝓞 E) t.A) (act₀ : OAct (𝓞 E) A₀), (∀ c, (act₀.act c).left ≫ m = m ≫ (act.act c).left) ∧ DetCond D act₀ (𝟙 _) (β ρ) := by
  intro E _ _ _ H D g k J a bas o _ b ρ S s t τ x β A₀ _ m hP hx hm
  obtain ⟨φ, hφ, -, -, hd⟩ := hP
  haveI := hφ
  have hi : IsGrpPullback t.A τ.G (𝟙 S) φ.inv.left := isGrpPullback_of_iso φ.inv
  obtain ⟨act, hact⟩ := exists_lift_act hi τ.act
  obtain ⟨act₀, hact₀⟩ := exists_lift_act hm act
  refine ⟨act, act₀, hact₀, fun σ => ?_⟩
  have L : ∀ n, LieMult act₀ (𝟙 _) σ n ↔ LieMult τ.act x σ n := fun n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hm hact₀ ℂ (𝟙 _) σ n,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.id_comp, Category.comp_id]
  rw [L, L]
  exact (hd ℂ x β hx).1 σ

end GlobalTheory.FibreAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteTypeModelOfSmoothAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem GlobalTheory.exists_finiteType_model_of_smooth_affine :
    ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  intro V _ X p _ _
  let B : CommRingCat.{0} := Γ(X, ⊤)
  let g : CommRingCat.of V ⟶ B := (Scheme.Spec.preimage (X.isoSpec.inv ≫ p)).unop
  have hg : Spec.map g = X.isoSpec.inv ≫ p := Scheme.Spec.map_preimage _
  have hpg : p = X.isoSpec.hom ≫ Spec.map g := by rw [hg, Iso.hom_inv_id_assoc]
  have hsg : Smooth (Spec.map g) := by rw [hg]; infer_instance
  have hgs : g.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsg
  let _ : Algebra V B := g.hom.toAlgebra
  have : Algebra.Smooth V B := hgs
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨ψe⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ V B
  let T : CommRingCat.{0} := CommRingCat.of (TensorProduct A₀ V B₀)
  let inl : CommRingCat.of V ⟶ T := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B₀ ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A₀) (A := V)).toRingHom
  let jIso : T ≅ B :=
    { hom := CommRingCat.ofHom ψe.symm.toRingHom
      inv := CommRingCat.ofHom ψe.toRingHom
      hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.apply_symm_apply x)
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.symm_apply_apply x) }
  have hj : inl ≫ jIso.hom = g := by
    ext v
    exact ψe.symm.commutes v
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ V B₀)).flip
  let e : X ≅ Spec T := X.isoSpec ≪≫ Scheme.Spec.mapIso jIso.op
  refine ⟨A₀, inferInstance, algebraMap A₀ V, Spec (CommRingCat.of B₀),
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)), e.hom ≫ Spec.map inr, ?_, ?_,
    inferInstance, ?_⟩
  · convert (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  · exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)
  · refine IsPullback.of_iso hpb e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, hpg]
      change (X.isoSpec.hom ≫ Spec.map jIso.hom) ≫ Spec.map inl = _
      rw [Category.assoc, ← Spec.map_comp, hj]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationLiftSmoothOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHomK {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHomK_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHomK p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_commK {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDerK_of_smooth : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  intro K _ R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHomK p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHomK_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHomK q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_commK x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHomK q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add (f := _)])
    (fun a b => by rw [hD.2, hc, hc, map_add (f := _), map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := (_root_.GlobalTheory.LocDerExtK.exists_unique_locDerK K R Y X q p m D W₀ hW).1 d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

