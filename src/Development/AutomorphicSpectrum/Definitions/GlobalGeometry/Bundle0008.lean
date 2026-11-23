module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def HodgeForm (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * hermForm Hm a b

def HodgeIP (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ G)
    (c : ℂ) : Prop :=
  L.IsLB ∧ IsTanAt G z v ∧ IsTanAt G z w ∧
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' w' : epsR ℂ ⟶ A) (a b : Fin g → ℂ),
    IsGrpPullback A G z φ ∧ u.IsAH Hm χ ∧ v'.left ≫ φ = v.left ∧ w'.left ≫ φ = w.left ∧
      u.IsDiff a v' ∧ u.IsDiff b w' ∧ c = Real.pi * (b ⬝ᵥ Hm.mulVec (star a))

def LieModel.GramAt (M : LieModel G ξ E) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) {r : ℕ}
    (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ v : Fin r → (epsAt z ⟶ G), (∀ i, M.ValAt z (b i) (v i)) ∧ ∀ p q, HodgeIP G L z (v p) (v q) (Γ p q)

def leadMinor {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) : ℝ :=
  if h : s ≤ r then (Γ.submatrix (Fin.castLE h) (Fin.castLE h)).det.re else 0

def LieModel.IsGrNorm (M : LieModel G ξ E) (L : LB G.left) (V : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (t : Ω) (ν : ℝ) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
    (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
      M.GramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)

def SecNorm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (A : HermLine J) (e₀ : Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ)
    (t : Ω) (ν : ℝ) : Prop :=
  e₀ ≠ 0 ∧ CoordsAt ξ y z w ∧
  ∀ c : (k : K) → J k, (∀ k, w ⟨k, c k⟩ ≠ 0) → ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
    ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k

section Form

variable {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {v w : epsAt z ⟶ G} {c : ℂ}

theorem hodgeInnerProduct_iff_hodgeForm : HodgeIP G L z v w c ↔ HodgeForm G L z w v c := by
  constructor
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩

theorem conj_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (a b : Fin g → ℂ) :
    (starRingEnd ℂ) (hermForm Hm a b) = hermForm Hm b a := by
  have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => h.apply j i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, hH]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem HodgeIP.isTanAt_left (h : HodgeIP G L z v w c) : IsTanAt G z v := h.2.1

theorem HodgeIP.isTanAt_right (h : HodgeIP G L z v w c) : IsTanAt G z w := h.2.2.1

end Form

section Minor

variable {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ}

theorem leadMinor_size_zero (Γ : Matrix (Fin r) (Fin r) ℂ) : leadMinor Γ 0 = 1 := by simp [leadMinor]

theorem leadMinor_size_one (Γ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : leadMinor Γ 1 = (Γ 0 0).re := by
  simp [leadMinor]

theorem leadMinor_size_self (Γ : Matrix (Fin r) (Fin r) ℂ) : leadMinor Γ r = Γ.det.re := by
  simp [leadMinor]

theorem leadMinor_transpose (Γ : Matrix (Fin r) (Fin r) ℂ) (s : ℕ) : leadMinor Γ.transpose s = leadMinor Γ s := by
  unfold leadMinor
  split_ifs with h
  · rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  · rfl

theorem leadMinor_pos_of_posDef (hΓ : Γ.PosDef) {s : ℕ} (h : s ≤ r) : 0 < leadMinor Γ s := by
  unfold leadMinor
  rw [dite_eq_left h]
  exact (Complex.pos_iff.1 (hΓ.submatrix (Fin.castLE_injective h)).det_pos).1

end Minor

section Gr

variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}

theorem LieModel.IsGrNorm.pos (h : M.IsGrNorm L V b₀ i z t ν) : 0 < ν := by
  obtain ⟨_, _, Γ, -, -, -, -, hΓ, rfl⟩ := h
  exact Real.sqrt_pos.2 (div_pos (leadMinor_pos_of_posDef hΓ i.2) (leadMinor_pos_of_posDef hΓ i.2.le))

end Gr

section Sec

variable {z : Spec (CommRingCat.of ℂ) ⟶ X}

namespace CxVal

theorem mul {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem isUnit (x : X.presheaf.stalk (centre z)) (h : (Scheme.stalkClosedPointTo z).hom x ≠ 0) : IsUnit x :=
  (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ h)

theorem inv {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x := isUnit x hr
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

theorem zpow {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  have hn : ∀ n : ℕ, ValAt ξ z (a ^ n) (r ^ n) := fun n => by
    induction n with
    | zero => simpa using one h.1
    | succ n ih => rw [pow_succ, pow_succ]; exact mul ih h
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using hn n
  · simpa using inv (hn n) (pow_ne_zero _ hr)

theorem aeval {σ : Type} {a : σ → Ω} {r : σ → ℂ} (hz : genPt ξ ⤳ centre z) (h : ∀ p, ValAt ξ z (a p) (r p))
    (s : MvPolynomial σ ℤ) : ValAt ξ z (MvPolynomial.aeval a s) (MvPolynomial.aeval r s) := by
  induction s using MvPolynomial.induction_on with
  | C n => exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩
  | add p q hp hq =>
    obtain ⟨_, x, hx, hx'⟩ := hp
    obtain ⟨_, y, hy, hy'⟩ := hq
    exact ⟨hz, x + y, by rw [map_add (f := _), map_add (f := _), hx, hy],
      (map_add (Scheme.stalkClosedPointTo z).hom x y).trans (by rw [map_add (f := _), ← hx', ← hy']; rfl)⟩
  | mul_X p i hp => simpa using mul hp (h i)

theorem unique {a : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z a s) : r = s := by
  obtain ⟨h, x, hx, rfl⟩ := h
  obtain ⟨_, y, hy, rfl⟩ := h'
  by_contra hne
  have hu : IsUnit (x - y) := isUnit _ fun h0 =>
    hne (sub_eq_zero.1 ((map_sub (Scheme.stalkClosedPointTo z).hom x y).symm.trans h0))
  have := hu.map (genMap ξ ⟨centre z, h⟩)
  rw [map_sub, hx, hy, sub_self] at this
  exact not_isUnit_zero this

end CxVal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}

theorem secNorm_iff_chart (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w t ν ↔ ∃ u : ℂ, ValAt ξ z (t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀)) u ∧
      ν * A.h w = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k := by
  refine ⟨fun h => h.2.2 c hc, ?_⟩
  rintro ⟨u, hu, hν⟩
  refine ⟨he, hw, fun c' hc' => ?_⟩
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (hc' k))).2 (c k)
  have hr0 : ∀ k, r k ≠ 0 := fun k h => hc k (by rw [hr', h, zero_mul])
  have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ A.a k) (∏ k ∈ s, r k ^ A.a k) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hu.1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (hr k) (hr0 k) _) ih
  have hy : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  refine ⟨u * ∏ k, r k ^ A.a k, ?_, ?_⟩
  · convert CxVal.mul hu (hp Finset.univ) using 1
    simp only [div_zpow, Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_inv]
    field_simp
  · rw [hν, norm_mul, norm_prod, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hr' k, norm_mul, mul_zpow, norm_zpow]

theorem SecNorm.exists_chart (h : SecNorm ξ y A e₀ z w t ν) : ∃ c : (k : K) → J k, ∀ k, w ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h.2.1.1
  exact ⟨c, fun k => (hc k).ne_zero⟩

theorem SecNorm.unique (h : SecNorm ξ y A e₀ z w t ν) (h' : SecNorm ξ y A e₀ z w t ν') : ν = ν' := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, hu, e⟩ := h.2.2 c hc
  obtain ⟨u', hu', e'⟩ := h'.2.2 c hc
  rw [CxVal.unique hu hu', ← e'] at e
  exact mul_right_cancel₀ (A.pos w fun k => ⟨c k, hc k⟩).ne' e

theorem SecNorm.specializes (h : SecNorm ξ y A e₀ z w t ν) : genPt ξ ⤳ centre z := by
  obtain ⟨c, hc⟩ := h.exists_chart
  obtain ⟨u, hu, -⟩ := h.2.2 c hc
  exact hu.1

theorem SecNorm.mul (h : SecNorm ξ y A e₀ z w t ν) {f : Ω} {s : ℂ} (hf : ValAt ξ z f s) :
    SecNorm ξ y A e₀ z w (f * t) (‖s‖ * ν) := by
  refine ⟨h.1, h.2.1, fun c hc => ?_⟩
  obtain ⟨u, hu, e⟩ := h.2.2 c hc
  refine ⟨s * u, ?_, ?_⟩
  · rw [mul_div_assoc]
    exact CxVal.mul hf hu
  · rw [_root_.mul_assoc, e, norm_mul, _root_.mul_assoc]

theorem aeval_blockScale {R : Type} [CommRing R] {s : MRing J} {b : K → ℕ} (hs : IsMultiHomog s b) (κ : K → R)
    (x : (Σ k, J k) → R) :
    MvPolynomial.aeval (fun p => κ p.1 * x p) s = (∏ k, κ k ^ b k) * MvPolynomial.aeval x s := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Fintype.prod_sigma (fun p : Σ k, J k => κ p.1 ^ m p)]
  simp only [Finset.prod_pow_eq_pow_sum, hs m hm]
  ring

end Sec

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_eq {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal t χ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a) t (Multiplicative.ofAdd χ)).val := by
  unfold charVal
  set g : Sp A ⟶ Spec (torusRing ZU X) := t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) with hg
  have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      = Spec.preimage g := by
    conv_lhs => rw [← Spec.map_preimage g]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h]
  rfl

theorem charVal_mul {A : Type} [CommRing A] {a : Sp A ⟶ S} (t t' : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (t * t') χ = charVal t χ * charVal t' χ := by
  simp only [charVal_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem charVal_one {A : Type} [CommRing A] {a : Sp A ⟶ S} (χ : X) :
    charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1 := by
  simp only [charVal_eq, map_one, MonoidHom.one_apply, Units.val_one]

theorem charVal_add {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ χ' : X) :
    charVal t (χ + χ') = charVal t χ * charVal t χ' := by
  simp only [charVal_eq, ofAdd_add, map_mul, Units.val_mul]

theorem charVal_zero {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) :
    charVal t 0 = 1 := by
  simp only [charVal_eq, ofAdd_zero, map_one, Units.val_one]

theorem charVal_ext {A : Type} [CommRing A] {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X}
    (h : ∀ χ, charVal t χ = charVal t' χ) : t = t' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).injective
  ext χ
  have := h χ
  rw [charVal_eq, charVal_eq] at this
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective this

theorem exists_charVal {A : Type} [CommRing A] (a : Sp A ⟶ S) (u : Multiplicative X →* Aˣ) :
    ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = (u (Multiplicative.ofAdd χ)).val := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom).comp u), fun χ => ?_⟩
  rw [charVal_eq, MulEquiv.apply_symm_apply]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem charVal_comp {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : t'.left = spMap g ≫ t.left) (χ : X) : charVal t' χ = g (charVal t χ) := by
  unfold charVal
  have e : (t'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp B ⟶ Spec (torusRing ZU X)) =
      Spec.map (CommRingCat.ofHom g) ≫
        (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X)) := by
    rw [h]; exact Category.assoc _ _ _
  rw [e, Spec.preimage_comp, Spec.preimage_map]
  rfl

theorem left_eq_of_charVal {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (hg : spMap g ≫ a = b) (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : ∀ χ, charVal t' χ = g (charVal t χ)) : t'.left = spMap g ≫ t.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk (spMap g) hg
  have : t' = k ≫ t := charVal_ext fun χ => by rw [h, charVal_comp g t (k ≫ t) rfl]
  rw [this]; rfl

def epsUnit {R : Type} [CommRing R] (δ : X →+ R) : Multiplicative X →* (DualNumber R)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun χ => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [add_comm] }

def tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  (exists_charVal _ (epsUnit δ)).choose

theorem charVal_tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (tanPt x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  (exists_charVal _ (epsUnit δ)).choose_spec χ

theorem spMap_comp_eps {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ S) (g : DualNumber R →+* A)
    (f : R →+* A) (h : g.comp (algebraMap R (DualNumber R)) = f) :
    spMap g ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = spMap f ≫ x := by
  rw [← Category.assoc, ← Spec.map_comp, ← h]; rfl

theorem fst_eps {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x := by
  rw [spMap_comp_eps x _ (RingHom.id R) (by ext; simp)]
  simp [spMap]

def lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) : LieModel (splitTorus S X) x (X →+ R) where
  pt := tanPt x
  tan δ := (left_eq_of_charVal _ (fst_eps x) (tanPt x δ) 1 fun χ => by
    rw [charVal_one, charVal_tanPt]; simp).symm
  inj δ δ' h := by
    ext χ
    have := congrArg (fun t => (charVal t χ).snd) h
    simpa [charVal_tanPt] using this
  onto v hv := by
    have h1 : ∀ χ, (charVal v χ).fst = 1 := fun χ => by
      have := charVal_comp (TrivSqZeroExt.fstHom R R R).toRingHom v (1 : Over.mk x ⟶ splitTorus S X)
        (Eq.symm hv) χ
      rw [charVal_one] at this
      exact this.symm
    refine ⟨AddMonoidHom.mk' (fun χ => (charVal v χ).snd) fun a b => ?_, charVal_ext fun χ => ?_⟩
    · simp [charVal_add, TrivSqZeroExt.snd_mul, h1, add_comm]
    · rw [charVal_tanPt]; ext <;> simp [h1]
  add δ δ' := charVal_ext fun χ => by
    rw [charVal_mul, charVal_tanPt, charVal_tanPt, charVal_tanPt]
    ext <;> simp [add_comm]
  smul c δ := left_eq_of_charVal (epsMul c)
    (spMap_comp_eps x _ _ (by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])) _ _ fun χ => by
      rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [epsMul, mul_comm]

theorem isCocharLie_lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    IsCocharLie (lieModel (X := X) x) := charVal_tanPt x

end GlobalTheory.CompanionTheory.Ar.TorusModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure IsEmbedded {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) : Prop where
  isOpen : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x
  holo : ∀ x p, A.HoloOn (U x) fun y => lam x y p
  mem : ∀ x, ∀ y ∈ U x, lam x y ∈ mcPts P
  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lam x y) (lam x' y)
  surj : ∀ z ∈ mcPts P, ∃ x, SameOrbit (lam x x) z
  inj : ∀ x x', SameOrbit (lam x x) (lam x' x') → x = x'
  immersion : ∀ x, ∀ p : (k : K) → ι k, (∀ k, lam x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lam x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

def IsSncModel {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) : Prop :=
  ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (m : ℕ) (f a : Fin m → Ω),
    (∀ l, f l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    (∀ l, a l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
      S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g → s ∈ q) ↔
            ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

def AlgOver {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) : Prop :=
  ∃ (K₀ : Type) (_ : Fintype K₀) (ι₀ : K₀ → Type) (_ : ∀ k, Fintype (ι₀ k)) (κ : K₀ → K)
    (v : (Σ k, ι₀ k) → Σ k, ι k) (U : S.X → Set S.X) (lam : S.X → S.X → (Σ k, ι₀ k) → ℂ) (β : MRing ι₀) (b : K₀ → ℕ),
    IsBlockMap κ v ∧ IsEmbedded S.A (imageZ v P) U lam ∧
    (∀ x, SameOrbit (lam (Re.π x) (Re.π x)) fun p => Re.R.lift x x (v p)) ∧
    IsMultiHomog β b ∧ β ∉ imageZ v P ∧ ∀ x ∈ bdry S.s, evC (lam x x) β = 0

section Same

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

def SameSing {D : ℕ} {σ₁ σ₂ : Type} {S₁ : AnSys D σ₁} {S₂ : AnSys D σ₂} {P₁ : Ideal (MRing ι₁)}
    {P₂ : Ideal (MRing ι₂)} (Re₁ : Realis S₁ P₁) (Re₂ : Realis S₂ P₂) (P : Ideal (MRing ι)) (κ₁ : K₁ → K)
    (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) :
    Prop :=
  ∃ f g : MRing ι, IsLineIso P (pullDeg κ₁ (Re₁.ref a₁).a) (pullDeg κ₂ (Re₂.ref a₂).a) f g ∧
    ∀ z ∈ mcPts P, evC z β ≠ 0 → ∀ (x₁ : Re₁.R.X) (x₂ : Re₂.R.X),
      SameOrbit (Re₁.R.lift x₁ x₁) (fun p => z (v₁ p)) → SameOrbit (Re₂.R.lift x₂ x₂) (fun p => z (v₂ p)) →
      Re₁.π x₁ ∉ bdry S₁.s → Re₂.π x₂ ∉ bdry S₂.s →
      ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
        Real.log (‖evC z v‖ / ‖evC z u‖ * (Re₂.ref a₂).h (fun p => z (v₂ p)) / (Re₁.ref a₁).h fun p => z (v₁ p)) =
          S₁.ph a₁ (Re₁.π x₁) - S₂.ph a₂ (Re₂.π x₂)

end Same

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

