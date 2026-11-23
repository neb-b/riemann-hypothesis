module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

namespace LieModel

def Extends (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G) : Prop :=
  IsTanAt G _ v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ v.left

def lat (M : LieModel G ξ E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}

def omLat (M : LieModel G ξ E) : Lat ξ (Module.Dual Ω E) := M.lat.dual

def eigLat (M : LieModel G ξ E) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) (σ : O →+* Ω) : Lat ξ E :=
  M.lat.inter (eigSp ρ σ)

variable {R : Type} [CommRing R] [IsLocalRing R]

def ValAt (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) (w : epsAt z ⟶ G) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧
      w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left

def fibAt (M : LieModel G ξ E) (L : Lat ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C]
    {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) : Submodule R EC :=
  Submodule.span R {w | ∃ (h : genPt ξ ⤳ centre z) (e : E), e ∈ L ⟨centre z, h⟩ ∧
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt w)}

end LieModel

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def NormalCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop :=
  ∀ (p : Cpt ξ) (a : Ω), IsIntegral (regAt ξ p) a → a ∈ regAt ξ p

def zeroSet (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) : Set X :=
  {q | ∃ h : genPt ξ ⤳ q, ¬ unitAt ξ ⟨q, h⟩ ϖ}

def TrivMod (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧ ∃ y ∈ L q, t p - t q = ϖ • y

def TrivRed (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧
        ∃ c ∈ regAt ξ q, ¬ unitAt ξ q c ∧ t p - t q = c • t p

def OrderAt (L : Lat ξ E) (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : Prop :=
  ∃ (e : E) (c : Ω), e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ σ = c • e ∧ unitAt ξ p (c ^ M / ϖ ^ a)

namespace ZUnit

variable {p : Cpt ξ} {a b : Ω}

theorem one : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp⟩

theorem mul (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem inv (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem pow (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem of_mul (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p) (h : unitAt ξ p (a * b)) : unitAt ξ p a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact mul_mem hb h.2.2

theorem of_pow (ha : a ∈ regAt ξ p) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact of_mul ha (pow_mem ha m) (by rwa [← pow_succ'])

theorem mem_of_pow_mem (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ regAt ξ p) : a ∈ regAt ξ p :=
  hN p a (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (isIntegral_algebraMap (x := (⟨a ^ n, h⟩ : regAt ξ p))))

theorem of_pow_of_normal (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a :=
  of_pow (mem_of_pow_mem hN hn h.2.1) hn h

theorem exists_of_span_eq {e e' : E} (he : e ≠ 0)
    (h : Submodule.span (regAt ξ p) {e} = Submodule.span (regAt ξ p) {e'}) :
    ∃ u : Ω, unitAt ξ p u ∧ e = u • e' := by
  have h1 : e ∈ Submodule.span (regAt ξ p) {e'} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  have h2 : e' ∈ Submodule.span (regAt ξ p) {e} := by
    rw [h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 h2
  replace hu : (u : Ω) • e' = e := hu
  replace hv : (v : Ω) • e = e' := hv
  have huv : (u : Ω) * v = 1 := by
    apply smul_left_injective Ω he
    simp only [mul_smul, hv, hu, one_smul]
  exact ⟨u, of_mul u.2 v.2 (by rw [huv]; exact one), hu.symm⟩

end ZUnit

theorem coe_mem_zeroSet {ϖ : Ω} (p : Cpt ξ) : p.1 ∈ zeroSet ξ ϖ ↔ ¬ unitAt ξ p ϖ :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩

section Order

variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}

theorem OrderAt.unitAt (h : OrderAt L σ ϖ M a p) {e : E} {c : Ω} (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : unitAt ξ p (c ^ M / ϖ ^ a) := by
  obtain ⟨e₀, c₀, he₀, hL₀, hσ₀, h⟩ := h
  obtain ⟨u, hu, e'⟩ := ZUnit.exists_of_span_eq he₀ (hL₀.symm.trans hL)
  have he : e ≠ 0 := by rintro rfl; exact he₀ (by rw [e', smul_zero])
  have hc : c = c₀ * u := by
    apply smul_left_injective Ω he
    simp only [mul_smul, ← e', ← hσ, ← hσ₀]
  have : c ^ M / ϖ ^ a = c₀ ^ M / ϖ ^ a * u ^ M := by rw [hc, mul_pow]; ring
  rw [this]
  exact ZUnit.mul h (ZUnit.pow hu M)

theorem orderAt_iff_of_gen {e : E} {c : Ω} (he : e ≠ 0) (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : OrderAt L σ ϖ M a p ↔ unitAt ξ p (c ^ M / ϖ ^ a) :=
  ⟨fun h => h.unitAt hL hσ, fun h => ⟨e, c, he, hL, hσ, h⟩⟩

theorem orderAt_iff_div {Λ : Lat ξ Ω} {s e : Ω} (he : e ≠ 0) (hΛ : Λ p = Submodule.span (regAt ξ p) {e}) :
    OrderAt Λ s ϖ M a p ↔ unitAt ξ p ((s / e) ^ M / ϖ ^ a) :=
  orderAt_iff_of_gen he hΛ (by rw [smul_eq_mul, div_mul_cancel₀ _ he])

theorem exists_gen_of_isVB_one {V : Submodule Ω E} (hL : L.IsVB 1 V) (p : Cpt ξ) :
    ∃ e : E, e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ V = Submodule.span Ω {e} := by
  obtain ⟨U, hU, b, hb, h⟩ := hL p trivial
  obtain ⟨h1, h2⟩ := h p trivial hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  exact ⟨b 0, h1.ne_zero 0, by rw [h2, hr], by rw [← hb, hr]⟩

theorem OrderAt.ne_zero (h : OrderAt L σ ϖ M a p) (hM : M ≠ 0) : σ ≠ 0 := by
  obtain ⟨e, c, he, -, rfl, h⟩ := h
  refine smul_ne_zero ?_ he
  rintro rfl
  exact h.1 (by rw [zero_pow hM, zero_div])

theorem orderAt_one_zero : OrderAt L σ ϖ 1 0 p ↔ σ ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {σ} := by
  refine ⟨fun h => ⟨h.ne_zero one_ne_zero, ?_⟩, fun ⟨h0, h⟩ => ⟨σ, 1, h0, h, (one_smul _ _).symm, by
    simpa using ZUnit.one⟩⟩
  obtain ⟨e, c, -, hL, rfl, h⟩ := h
  rw [pow_one, zpow_zero, div_one] at h
  rw [hL]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨c⁻¹, h.2.2⟩, by
      change c⁻¹ • c • e = e
      rw [inv_smul_smul₀ h.1]⟩
  · exact ⟨⟨c, h.2.1⟩, rfl⟩

end Order

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

abbrev evC (z : (Σ k, ι k) → ℂ) (g : MRing ι) : ℂ := eval z (map (Int.castRingHom ℂ) g)

def OverInt (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) : Prop :=
  (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ a : 𝓞 F, φ (a : F) ∈ chartRingZ y c

def PtOver (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ) : Prop :=
  z ∈ mcPts (mCoordIdeal y) ∧ ∀ (a : F) (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = φ a * aeval y h → evC z g = σ a * evC z h

def IsUnitSec (P : Ideal (MRing ι)) (f g : MRing ι) : Prop :=
  ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

structure IsPlaceWeight (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop where
  inv : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  near : ∀ σ z, PtOver y φ σ z → ∀ᶠ z' in nhds z, u z' = t σ

def IsPlaceWeight.shift {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {s : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsPlaceWeight y φ s u) (A : HermLine ι) : HermLine ι :=
  A.tensor (HermLine.ofWeight u hu.inv)

def meanEmb (t : (F →+* ℂ) → ℝ) : ℝ := (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ)

structure FlatHerm (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) where
  M : ℕ
  M_pos : 0 < M
  f : MRing ι
  g : MRing ι
  df : K → ℕ
  dg : K → ℕ
  hf : IsMultiHomog f df
  hg : IsMultiHomog g dg
  deg : ∀ k, (df k : ℤ) - dg k = M * A.a k
  f_ne : f ∉ mCoordIdeal y
  g_ne : g ∉ mCoordIdeal y
  unit : IsUnitSec (mCoordIdeal y) f g
  κ : (F →+* ℂ) → ℝ
  κ_pos : ∀ σ, 0 < κ σ
  κ_conj : ∀ σ, κ (ComplexEmbedding.conjugate σ) = κ σ
  norm : ∀ σ z, PtOver y φ σ z → ‖evC z f‖ = (κ σ * A.h z) ^ M * ‖evC z g‖

def FlatHerm.ht {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {A : HermLine ι} (S : FlatHerm y φ A) : ℝ :=
  -meanEmb fun σ => Real.log (S.κ σ)

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.Inh

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

variable (F : Type) [Field F] [NumberField F]

end GlobalTheory.CompanionTheory.Ar.Flat.Inh
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LatModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Deg
variable {K : Type} [Fintype K] {ι : K → Type}

end Deg

section Pull
variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem dominates_spec {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ') :
    genPt ξ ⤳ f p'.1 := by
  have e : f (genPt ξ') = genPt ξ := by
    have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
    have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    exact h1.trans (congrArg ξ h2)
  exact e ▸ p'.2.map f.continuous

theorem dominates_regAt {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ')
    (hp : genPt ξ ⤳ f p'.1) {a : Ω} (ha : a ∈ regAt ξ ⟨f p'.1, hp⟩) : i a ∈ regAt ξ' p' := by
  obtain ⟨q, hq⟩ := p'
  obtain ⟨s, rfl⟩ := ha
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact ⟨f.stalkMap q s, congrArg (fun g => g.hom s) e⟩

end Pull

section Int

end Int

end GlobalTheory.CompanionTheory.Ar.LatModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def charVal {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) : A :=
  (Spec.preimage (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X))).hom
    (AddMonoidAlgebra.single χ 1)

def KillsOver {G : Over S} [GrpObj G] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B : Type} [CommRing B]
    (b : Sp B ⟶ S) : Prop :=
  ∀ (A : Type) [CommRing A] (g : B →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
    (∀ y ∈ Y, charVal t y = 1) → t ≫ u = 1

def IsCocharLie {R : Type} [CommRing R] {x : Sp R ⟶ S} (M : LieModel (splitTorus S X) x (X →+ R)) : Prop :=
  ∀ (δ : X →+ R) (χ : X), charVal (M.pt δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ)

def LieModel.Lifts {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (c : R →+* R') {S' : Scheme.{0}} {G' : Over S'}
    (φ : G'.left ⟶ G.left) {x' : Sp R' ⟶ S'} (e : E) (v : epsAt x' ⟶ G') : Prop :=
  v.left ≫ φ = spMap (dualMap c) ≫ (M.pt e).left

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def flagStep (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : ℕ) : Submodule Ω E :=
  Submodule.span Ω (b₀ '' {k | (k : ℕ) < i})

namespace Lat

def IsFlagVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) {r : ℕ} (b₀ : Fin r → E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q

def gr (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i}

def IsGenAt (Λ : Lat ξ Ω) (p : Cpt ξ) (t : Ω) : Prop := t ≠ 0 ∧ Λ p = Submodule.span (regAt ξ p) {t}

def tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i}

end Lat

def IsGenericFlag {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (j : E →+ E') {S : Type} {r : S → ℕ} (V : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ) : Prop :=
  ∃ (c : ∀ σ, Fin (r σ) → E) (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω'),
    (∀ σ, LinearIndependent Ω (c σ) ∧ Submodule.span Ω (Set.range (c σ)) = V σ) ∧
    (∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) ∧ (∀ σ, LinearIndependent Ω' fun k => j (c σ k)) ∧
    (∀ σ, LinearIndependent Ω' (b₀ σ)) ∧ (∀ σ k, u σ k k = 1) ∧ (∀ σ l k, l < k → u σ l k = 0) ∧
    (∀ σ i, flagStep Ω' (b₀ σ) i = flagStep Ω' (fun k => ∑ l, u σ l k • j (c σ l)) i) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    0 < d ∧ Module.finrank (IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω' = d

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def IsCoeffAt (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (x : Cpt ξ) (f : Ω) : Prop :=
  ∃ α β : Ω, α ≠ 0 ∧ β ≠ 0 ∧ A.wedge p x = Submodule.span (regAt ξ x) {α • a} ∧
    B.wedge q x = Submodule.span (regAt ξ x) {β • b} ∧ f * α = β

def IsLineGenOn (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (T : Set (Cpt ξ)) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ∀ x ∈ T, IsCoeffAt A B p q a b x 1

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

