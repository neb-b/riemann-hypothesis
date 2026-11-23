module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOfIsIntegral
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.QuadGenerator

theorem int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff ).1 h')

theorem isIntegral_int (n : ℤ) : IsIntegral ℤ (n : ℂ) := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)

theorem sq_root (d : ℕ) : (Complex.I * (Real.sqrt d : ℝ)) ^ 2 = -(d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

theorem half_coords {d : ℕ} (hd : d.Prime) {a b : ℚ}
    (hx : IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ)))) :
    ∃ t k n : ℤ, (t : ℚ) = 2 * a ∧ (k : ℚ) = 2 * b ∧ t ^ 2 + d * k ^ 2 = 4 * n := by
  have hw2 := sq_root d
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
    have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
    simpa [hwc, sub_eq_add_neg] using this
  obtain ⟨t, ht⟩ := int_of_isIntegral (r := 2 * a) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
    push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
    push_cast
    linear_combination (b : ℂ) ^ 2 * hw2)
  have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [hn, ht]; ring
  obtain ⟨m, hm⟩ := int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
    rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
    exact isIntegral_int _))
  have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
    have : ((m ^ 2 : ℤ) : ℚ) = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      rw [← hm2, ← hm]; push_cast; ring
    exact_mod_cast this
  obtain ⟨k, hk⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, hm3⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hkb : (k : ℚ) = 2 * b := by
    apply mul_left_cancel₀ hd0
    rw [← hm, hk]; push_cast; ring
  refine ⟨t, k, n, ht, hkb, ?_⟩
  have : ((t ^ 2 + d * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
    push_cast
    rw [ht, hkb, hn]; ring
  exact_mod_cast this

theorem even_of_one {d : ℕ} (h4 : d % 4 = 1) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t ∧ 2 ∣ k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 1 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - q ^ 2) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 2 := by linear_combination -h
    omega

theorem even_of_three {d : ℕ} (h4 : d % 4 = 3) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t + k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 3 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨p + q, by ring⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - 3 * q ^ 2 - 3 * q) = 3 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - 3 * q ^ 2) = 1 := by linear_combination -h
    omega
  · exact ⟨p + q + 1, by ring⟩

theorem integers_one {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 1) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * (Complex.I * (Real.sqrt d : ℝ)) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := even_of_one h4 h
    have ha : a = p := by push_cast at ht; linarith
    have hb : b = q := by push_cast at hk; linarith
    exact ⟨q, p, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw : IsIntegral ℤ (Complex.I * (Real.sqrt d : ℝ)) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [sq_root]
      simpa using isIntegral_int (-(d : ℤ))
    refine ⟨?_, v, u, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem integers_three {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨j, hj⟩ := even_of_three h4 h
    have hj' : (t : ℚ) + k = 2 * j := by exact_mod_cast hj
    have ha : a = j - k / 2 := by linarith
    have hb : b = k / 2 := by linarith
    exact ⟨k, j, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw2 := sq_root d
    obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
    have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
    have hw : IsIntegral ℤ ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
    refine ⟨?_, v - u / 2, u / 2, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem exists_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ) (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ (w θ : E) (τ : ℍ), w ^ 2 = -(d : E) ∧ (∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)) ∧ θ = (if d % 4 = 3 then (-1 + w) / 2 else w) ∧ (∀ i, φ i θ = (τ : ℂ)) ∧ IsTauOf Λ 1 τ ∧ ((d % 4 = 3 ∧ τ.im = Real.sqrt d / 2) ∨ (d % 4 = 1 ∧ τ.im = Real.sqrt d)) := by
  intro E _ _ _ I _ d φ Λ hF hΛ
  obtain ⟨hd, h4, -, -, -, -, -, w, hw, hφ⟩ := hF
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
  have hodd : d % 2 = 1 := hd.eq_two_or_odd.resolve_left (by omega)
  by_cases h3 : d % 4 = 3
  · have him : ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2 : ℂ).im = Real.sqrt d / 2 := by simp
    refine ⟨w, (-1 + w) / 2, ⟨(-1 + Complex.I * (Real.sqrt d : ℝ)) / 2, by rw [him]; positivity⟩, hw, hφ,
      by rw [if_pos h3], fun i => ?_, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_three hd h3 x)⟩, Or.inl ⟨h3, him⟩⟩
    rw [map_div₀, map_add (f := _), map_neg, map_one, map_ofNat, hφ]
  · have h1 : d % 4 = 1 := by omega
    have him : (Complex.I * (Real.sqrt d : ℝ) : ℂ).im = Real.sqrt d := by simp
    exact ⟨w, w, ⟨Complex.I * (Real.sqrt d : ℝ), by rw [him]; exact hs⟩, hw, hφ,
      by rw [if_neg h3], hφ, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_one hd h1 x)⟩, Or.inr ⟨h1, him⟩⟩

end GlobalTheory.QuadGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibility
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem top_le_fromSpecStalk {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens) (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem val_fromSpecStalk {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B ⊤)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y (memTop y) hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  have hV : y ∈ (⊤ : Y.Opens) ⊓ B.U i := memInf (memTop y) hi
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ ((⊤ : Y.Opens) ⊓ B.U i) := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open (IsOpen.inter isOpen_univ (B.U i).isOpen) hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_congr' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr'' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _


set_option maxHeartbeats 1000000 in
theorem evI_ofSpace_eq_prod_mul_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (x₀ : Sp T.Fr ⟶ Y₀ X Z), (X.ptY y'.1 = x₀ ≫ inc₀ X Z) → ∀ (j' : (L₀ X Z la).ι) (hO : ⊤ ≤ x₀ ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)) (hj : ⊤ ≤ x₀ ⁻¹ᵁ (L₀ X Z la).U j') (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit)) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr (j' PUnit.unit) (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) = (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix).val * H0.val x₀ j' hO hj w.1 := by
  intro E _ _ _ H Dw l Xo c Y X Z r U la w T io y' x₀ hx j' hO hj hz Q t hQ ht
  letI := io.toAlgebra
  let fS : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0) := ⟨_, cusp_le_secZ Z U la (ofSpace X Z U la w).2⟩
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf fS hOf hQ ht
  show evR Xo c fS.1 y'.1 = _
  rw [a]
  congr 1
  have hx' : X.pt y'.1 ≫ X.inc = x₀ ≫ inc₀ X Z := (X.pt_inc _).trans hx
  have hU₀ : ⊤ ≤ x₀ ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  have hk' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (j' PUnit.unit) := hx' ▸ hz
  have hO' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hx' ▸ hOf
  rw [val_congr' hx' _ hOf hO' hz hk']
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) x₀ j' hU₀ hj hO' hk' (secOf X _ fS)
  rw [← b1]
  have hs : H0.pull (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X _ fS) = H0.restr le_top w.1 := cuspSec_ofSpace X Z U la w
  rw [hs, val_restr'' le_top x₀ j' hO hU₀ hj]


set_option maxHeartbeats 1000000 in
theorem germ_eq_unit_mul_evI_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (y : Y₀ X Z) (T : CDVR)
    (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z)
    (j' : (L₀ X Z la).ι) (hj' : y ∈ (L₀ X Z la).U j') :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) =
      algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) := by
  letI := io.toAlgebra
  have hk : inc₀ X Z y ∈ X.F.U (j' PUnit.unit) := mem_pull.1 hj'
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hO := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ⊤ (memTop y)
  have hj := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ((L₀ X Z la).U j') hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j' PUnit.unit) := by
    have := top_le_fromSpecStalk y g (inc₀ X Z ⁻¹ᵁ X.F.U (j' PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j' PUnit.unit) hz
  have e2 := evI_ofSpace_eq_prod_mul_val X Z U la w T io y' _ hx₀ j' hO hj hz Q t hQ ht
  have e1 := val_fromSpecStalk y j' hj' ((algebraMap T.V T.Fr).comp g) w.1 hO hj
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j' PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ GlobalTheory.AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, e1, Units.coe_map, RingHom.comp_apply, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one,
    one_mul]

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem isAdditive_swap_of_isDual (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hd : IsDual A B P) :
    IsAdditive (swap P) := by
  have hP := hd.isLB
  have ext : ∀ {Y : Over S} {x y : Y ⟶ B},
      (∀ (Z : Over S) (u : Z ⟶ Y) (a : Z ⟶ A), evc hP a (u ≫ x) = evc hP a (u ≫ y)) → x = y := by
    intro Y x y h
    have hM : (ev P (fst A Y) (snd A Y ≫ x)).IsLB := pull_isLB hP _
    refine (hd.univ Y _ hM ((isAdditive_iff hM).2 fun Z a a' t ↦ ?_)).unique
      ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
    · simp only [evc_ev hP, lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hP).1 hd.additive _ _ _ _
    · exact h (A ⊗ Y) (snd A Y) (fst A Y)
  have h₁ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ fst B B)).IsLB := pull_isLB hP _
  have h₂ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ snd B B)).IsLB := pull_isLB hP _
  have hM := isLB_tens h₁ h₂
  have eM : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hM a t = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    show CechPic.pull _ (cls _ hM) = _
    rw [cls_tens h₁ h₂ hM, map_add (f := _)]
    exact congrArg₂ (· + ·) ((evc_ev hP _ _ h₁ a t).trans (by rw [lift_fst, lift_snd_assoc]))
      ((evc_ev hP _ _ h₂ a t).trans (by rw [lift_fst, lift_snd_assoc]))
  obtain ⟨m, hm, -⟩ := hd.univ (B ⊗ B) _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, (isAdditive_iff hP).1 hd.additive, (isAdditive_iff hP).1 hd.additive]
    abel)
  have hm' : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ m)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hP a (t ≫ m) = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    have e : evc hM a t = evc hm' a t := by rw [evc, evc, (cls_eq_iff hM hm').2 hm]
    rw [← eM, e, evc_ev hP, lift_fst, lift_snd_assoc]
  have hl : ∀ {Y : Over S} (b : Y ⟶ B), lift b 1 ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, add_zero]
  have hr : ∀ {Y : Over S} (b : Y ⟶ B), lift 1 b ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, zero_add]
  have e1 : ∀ (X : Over S) [MonObj X], (1 : 𝟙_ (Over S) ⟶ X) = η[X] := fun X _ ↦ by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hη : η[B ⊗ B] ≫ m = η[B] := by
    have e : (1 : 𝟙_ (Over S) ⟶ B ⊗ B) = lift (1 : 𝟙_ (Over S) ⟶ B) 1 := by
      ext <;> simp
    rw [← e1 (B ⊗ B), ← e1 B, e, hl]
  haveI : IsMonHom m := GlobalTheory.rigidity_holds S (B ⊗ B) B (AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB) hB m hη
  have hs : (swap P).IsLB := pull_isLB hP _
  refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
  rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  have e : b * b' = lift b b' ≫ m := by
    have e' : lift b b' = lift b 1 * lift 1 b' := by
      ext <;> simp [MonObj.mul_comp]
    rw [e', MonObj.mul_comp, hl, hr]
  rw [e, key, lift_fst, lift_snd]

theorem isDual_isAdditive_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme B → IsDual A B P → IsAdditive (swap P) :=
  fun _ _ _ _ _ _ hB hd ↦ isAdditive_swap_of_isDual hB hd

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLattices
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAffine

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem sub_mem_of_ex_eq {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem ex_eq_of_sub_mem {z w : Fin g → ℂ} (h : z - w ∈ u.Λ) : u.ex z = u.ex w := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, (u.ker _).2 h, _root_.one_mul] at e
  exact e

theorem exists_ex_apply_eq [LocallyOfFiniteType A.hom] (x : A.left) (hx : IsClosed ({x} : Set A.left)) :
    ∃ z, (u.ex z).left (IsLocalRing.closedPoint ℂ) = x := by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk (U := 𝟙_ (Over (Sp ℂ))) (V := A) (pointOfClosedPoint A.hom x hx)
    ((pointOfClosedPoint_comp A.hom x hx).trans rfl))
  exact ⟨z, by rw [hz]; exact pointOfClosedPoint_apply A.hom x hx _⟩

end

theorem isAffineHom_of_lift : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (B : Over (Sp ℂ)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB A.left) (L' : LB B.left) (u : HolUnif A L g) (u' : HolUnif B L' g) (a : Fin g → ℂ) (N : ℕ),
    0 < N → u.Λ ≤ u'.Λ → (∀ x ∈ u'.Λ, N • x ∈ u.Λ) →
    ∀ ψ : A.left ⟶ B.left, ψ ≫ B.hom = A.hom → (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) → IsAffineHom ψ := by
  intro g A _ hA B _ hB L L' u u' a N hN hle hN' ψ hψ hex
  have := hA.proper
  have := hB.proper
  have : IsProper (ψ ≫ B.hom) := by rw [hψ]; infer_instance
  have : IsProper ψ := IsProper.of_comp ψ B.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  haveI := u'.discrete
  haveI := holUnif_isZLattice u'
  haveI : Module.Finite ℤ u'.Λ := ZLattice.module_finite ℝ u'.Λ
  let K : Submodule ℤ u'.Λ := u.Λ.comap u'.Λ.subtype
  have hQ : Finite (u'.Λ ⧸ K) := by
    refine Module.finite_of_fg_torsion _ fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H l =>
      refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
      change ((N : ℤ) • Submodule.Quotient.mk l : u'.Λ ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change ((((N : ℤ) • l : u'.Λ)) : Fin g → ℂ) ∈ u.Λ
      rw [Submodule.coe_smul, natCast_zsmul]
      exact hN' _ l.2
  have hLQF : LocallyQuasiFinite ψ := by
    refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints ψ fun y hy => ?_
    have hcl : IsClosed ({ψ y} : Set B.left) := by simpa using ψ.isClosedMap _ hy
    refine GlobalTheory.finite_of_isClosed_of_finite_inter_closedPoints (hcl.preimage ψ.continuous) ?_
    obtain ⟨z₀, rfl⟩ := exists_ex_apply_eq u y hy
    let r := Function.surjInv (Submodule.Quotient.mk_surjective K)
    have hr : ∀ q, Submodule.Quotient.mk (r q) = q := Function.surjInv_eq (Submodule.Quotient.mk_surjective K)
    refine (Set.finite_range fun q : u'.Λ ⧸ K =>
      (u.ex (z₀ + ((r q : u'.Λ) : Fin g → ℂ))).left (IsLocalRing.closedPoint ℂ)).subset ?_
    rintro x ⟨hx, hxc⟩
    obtain ⟨z, rfl⟩ := exists_ex_apply_eq u x hxc
    have hx' : ((u.ex z).left ≫ ψ) (IsLocalRing.closedPoint ℂ) =
        ((u.ex z₀).left ≫ ψ) (IsLocalRing.closedPoint ℂ) := by
      first | exact hx | simpa using hx | (simp only [Scheme.Hom.comp_apply]; exact hx)
    rw [hex, hex] at hx'
    have e1 : u'.ex (z + a) = u'.ex (z₀ + a) :=
      Over.OverMorphism.ext (ext_of_apply_closedPoint_eq B.hom (Over.w _) (Over.w _) hx')
    have hl : z - z₀ ∈ u'.Λ := by
      simpa [add_sub_add_right_eq_sub] using sub_mem_of_ex_eq u' e1
    refine ⟨Submodule.Quotient.mk ⟨z - z₀, hl⟩, ?_⟩
    have h2 : (r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) - ⟨z - z₀, hl⟩ : u'.Λ) ∈ K :=
      (Submodule.Quotient.eq K).1 (hr _)
    have h3 : ((r (Submodule.Quotient.mk ⟨z - z₀, hl⟩) : u'.Λ) : Fin g → ℂ) - (z - z₀) ∈ u.Λ := h2
    dsimp only
    rw [ex_eq_of_sub_mem u (z := z₀ + _) (w := z) (by convert h3 using 1; abel)]
  have : IsFinite ψ := .of_isProper_of_locallyQuasiFinite _
  infer_instance

end GlobalTheory.LiftAffine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullbStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) := by
  first | (exact @GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (exact GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (intros; apply GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_normalModel_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  first | (exact @GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (exact GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (intros; apply GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic  <;> assumption)
end

