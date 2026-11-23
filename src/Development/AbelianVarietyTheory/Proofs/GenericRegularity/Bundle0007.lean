module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsNoetherianRingTensor
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsFractionRingSubringOfClosureEqTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddOfMemHolSub
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory

namespace IntegralCusp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem norm_eval_le_of_isHomogeneous' {N d : ℕ} {p : MvPolynomial (Fin N) ℂ}
    (hp : p.IsHomogeneous d) (w : Fin N → ℂ) :
    ‖MvPolynomial.eval w p‖ ≤ (∑ s ∈ p.support, ‖p.coeff s‖) * ‖w‖ ^ d := by
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ j, s j = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  calc ∏ j, ‖w j ^ s j‖ ≤ ∏ j, ‖w‖ ^ s j := by
        refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) _
    _ = ‖w‖ ^ d := by rw [Finset.prod_pow_eq_pow_sum, hdeg]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.IntegralCusp.exists_root_bound (N k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) ℂ)
    (hc : ∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin N → ℂ) (g : ℂ),
      g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i = 0 →
        ‖g‖ ≤ C * ‖w‖ ^ k := by
  classical
  set A : ℕ → ℝ := fun i => ∑ s ∈ (cf i).support, ‖(cf i).coeff s‖ with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set B : ℝ := 1 + ∑ i ∈ Finset.range m, A i with hBdef
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA0 i)
  have hB0 : 0 < B := by linarith
  refine ⟨B, hB0.le, fun w g hg => ?_⟩
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]; positivity
  have hroot : g ^ m = -∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
    have h1 : g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i) = 0 := by
      have hs : ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i =
          g * ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
      rw [mul_add, ← hs]
      exact hg
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hg0)
  set x := ‖g‖ with hx
  set t := ‖w‖ ^ k with ht
  have hx0 : 0 < x := norm_pos_iff.mpr hg0
  have ht0 : 0 ≤ t := by positivity
  by_contra hlt
  push_neg at hlt
  have htx : t ≤ x / B := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ i ∈ Finset.range m,
      ‖MvPolynomial.eval w (cf i) * g ^ i‖ ≤ A i * (x ^ m / B) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow]
    have hci := norm_eval_le_of_isHomogeneous' (hc i him) w
    have hpow : ‖w‖ ^ ((m - i) * k) = t ^ (m - i) := by rw [ht, ← pow_mul, mul_comm]
    have hkey : t ^ (m - i) * x ^ i ≤ x ^ m / B := by
      have h1 : t ^ (m - i) ≤ (x / B) ^ (m - i) := pow_le_pow_left₀ ht0 htx _
      have h2 : B ≤ B ^ (m - i) := le_self_pow₀ hB1 (by omega)
      calc t ^ (m - i) * x ^ i ≤ (x / B) ^ (m - i) * x ^ i := by gcongr
        _ = x ^ m / B ^ (m - i) := by
          rw [div_pow, div_mul_eq_mul_div, ← pow_add, Nat.sub_add_cancel him.le]
        _ ≤ x ^ m / B := div_le_div_of_nonneg_left (by positivity) hB0 h2
    calc ‖MvPolynomial.eval w (cf i)‖ * x ^ i ≤ A i * t ^ (m - i) * x ^ i := by
          gcongr
          rw [← hpow]
          exact hci
      _ = A i * (t ^ (m - i) * x ^ i) := by ring
      _ ≤ A i * (x ^ m / B) := mul_le_mul_of_nonneg_left hkey (hA0 i)
  have hbound : x ^ m ≤ (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by
    calc x ^ m = ‖g ^ m‖ := by rw [norm_pow]
      _ = ‖∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i‖ := by rw [hroot, norm_neg]
      _ ≤ ∑ i ∈ Finset.range m, ‖MvPolynomial.eval w (cf i) * g ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, A i * (x ^ m / B) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by rw [Finset.sum_mul]
  have hS : ∑ i ∈ Finset.range m, A i = B - 1 := by rw [hBdef]; ring
  have hxm : 0 < x ^ m / B := by positivity
  have hBx : B * (x ^ m / B) = x ^ m := by field_simp
  rw [hS, sub_mul, _root_.one_mul, hBx] at hbound
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.IntegralCusp.nfac_nsmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (k : ℕ) (h : ∀ τ i, la' τ i = k * la τ i) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la' x = X.nfac la x ^ k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in
theorem _root_.GlobalTheory.IntegralCusp.laU_nsmul {σ : c.F →+* ℂ} {r : ℕ} (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r)
    (a : (E →+* ℂ) × ℕ → ℕ) (n k : ℕ) (hn : Even n) (j : U.Comp) (τ : (U.X j).Ψ) (i : Fin r) :
    _root_.Formalism.L2.PjFree.laU U (k • a) (k * n) j τ i = k * _root_.Formalism.L2.PjFree.laU U a n j τ i := by
  unfold _root_.Formalism.L2.PjFree.laU
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Nat.mul_div_assoc k hn.two_dvd]
  split_ifs <;> push_cast <;> ring

def evHom {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ))
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    Rul Xo c →+* ℂ where
  toFun f := Formalism.L2.PjFree.toC (evR Xo c f y)
  map_one' := evalAt_one _ _ y hy
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in
theorem _root_.GlobalTheory.IntegralCusp.evHom_aeval {σ : c.F →+* ℂ} (y : _root_.Formalism.L2.Pj.FrPt Xo c (_root_.Formalism.L2.Pj.CAt σ))
    (hy : _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y) {N : ℕ}
    (w : Fin N → _root_.Formalism.L2.Pj.Rul Xo c) (p : MvPolynomial (Fin N) c.F) :
    _root_.GlobalTheory.IntegralCusp.evHom y hy (MvPolynomial.aeval w p) =
      MvPolynomial.eval (fun i => _root_.GlobalTheory.IntegralCusp.evHom y hy (w i))
        (MvPolynomial.map σ p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.eval_C,
      Algebra.algebraMap_eq_smul_one]
    show _root_.Formalism.L2.PjFree.toC (_root_.Formalism.L2.Pj.evalAt _ _ (a • (1 : _root_.Formalism.L2.Pj.Rul Xo c)) y) = σ a
    rw [_root_.Formalism.L2.Pj.evalAt_smul, _root_.Formalism.L2.Pj.evalAt_one _ _ y hy, _root_.mul_one]
    rfl
  | add p q hp hq =>
    rw [map_add (MvPolynomial.aeval w), (evHom y hy).map_add,
      map_add (MvPolynomial.map σ), map_add (MvPolynomial.eval _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval_X]

end IntegralCusp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsExtendOfPowDenom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_extend_of_pow_denom {R A L : Type} [CommRing R] [CommRing A] [IsDomain A] [Field L]
    (β : R →+* FractionRing A) (d : A)
    (h : ∀ r, ∃ (x : A) (t : ℕ), β r * algebraMap A _ (d ^ t) = algebraMap A _ x)
    (φ : A →+* L) (hd : φ d ≠ 0) :
    ∃ ψ : R →+* L, ∀ (r : R) (x s : A),
      β r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  choose X T hXT using h
  have hp : ∀ t : ℕ, φ (d ^ t) ≠ 0 := fun t => by rw [map_pow]; exact pow_ne_zero _ hd
  have key : ∀ (r : R) (x s : A), β r * algebraMap A _ s = algebraMap A _ x →
      φ (X r) / φ (d ^ T r) * φ s = φ x := by
    intro r x s hx
    have h1 : X r * s = x * d ^ T r := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_mul, map_mul, ← hXT r, ← hx]; ring
    have h2 := congrArg φ h1
    rw [map_mul, map_mul] at h2
    rw [div_mul_eq_mul_div, h2, mul_div_assoc, div_self (hp _), _root_.mul_one]
  refine ⟨{ toFun := fun r => φ (X r) / φ (d ^ T r), map_one' := ?_, map_mul' := ?_,
            map_zero' := ?_, map_add' := ?_ }, key⟩
  · have := key 1 1 1 (by simp)
    simpa using this
  · intro r s
    have := key (r * s) (X r * X s) (d ^ T r * d ^ T s) (by
      rw [map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_mul, map_mul] at this
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this
  · have := key 0 0 1 (by simp)
    simpa using this
  · intro r s
    have := key (r + s) (X r * d ^ T s + d ^ T r * X s) (d ^ T r * d ^ T s) (by
      rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, ← hXT r, ← hXT s]; ring)
    rw [map_add (f := _), map_mul, map_mul, map_mul] at this
    rw [div_add_div _ _ (hp _) (hp _), eq_div_iff (mul_ne_zero (hp _) (hp _))]
    exact this

theorem openChart_regular_away :
    ∀ (K Ω O A : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [IsDomain A] [Algebra O A] (io : K →+* FractionRing O) (gens : Finset Ω) (e : Ω) (α : Ω →+* FractionRing A) (eb : A) (ϖ : O), Irreducible ϖ → e ≠ 0 → algebraMap A (FractionRing A) eb = α e → (∀ (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α (algebraMap K Ω k) * algebraMap A _ (algebraMap O A b) = algebraMap A _ (algebraMap O A a)) → (∀ g ∈ gens, α g ∈ Set.range (algebraMap A (FractionRing A))) → (∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ), α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x) ∧ ∀ (L : Type) [Field L] (φ : A →+* L), φ (algebraMap O A ϖ * eb) ≠ 0 → ∃ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L, ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A), α r * algebraMap A _ s = algebraMap A _ x → ψ r * φ s = φ x := by
  intro K Ω O A _ _ _ _ _ _ _ _ _ io gens e α eb ϖ hϖ he heb hk hg
  have h1 : ∀ r ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), ∃ (x : A) (t : ℕ),
      α r * algebraMap A _ ((algebraMap O A ϖ * eb) ^ t) = algebraMap A _ x := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨algebraMap O A ϖ, 1, ?_⟩
        rw [pow_one, map_mul, heb, _root_.mul_comm _ (α e), ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ he,
          map_one, _root_.one_mul]
      · obtain ⟨y, hy⟩ := hg x hx
        exact ⟨y, 0, by simp [hy]⟩
    | algebraMap k =>
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (io k)
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
      have hb1 : algebraMap O (FractionRing O) b ≠ 0 := by simpa using hb0
      have := hk k (a * u) (ϖ ^ n) (by
        rw [← hu, ← hab, map_mul, map_mul, ← _root_.mul_assoc, div_mul_cancel₀ _ hb1])
      refine ⟨algebraMap O A (a * u) * eb ^ n, n, ?_⟩
      rw [mul_pow, ← map_pow, map_mul, ← _root_.mul_assoc, this, ← map_mul]
    | add x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * (algebraMap O A ϖ * eb) ^ t + b * (algebraMap O A ϖ * eb) ^ s, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_add (f := _), map_add (f := _), map_mul, map_mul, map_mul, ← ha, ← hb]; ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, s, ha⟩ := ihx
      obtain ⟨b, t, hb⟩ := ihy
      refine ⟨a * b, s + t, ?_⟩
      generalize algebraMap O A ϖ * eb = d at *
      rw [pow_add, map_mul, map_mul, map_mul, ← ha, ← hb]; ring
  refine ⟨h1, fun L _ φ hφ => ?_⟩
  exact exists_extend_of_pow_denom
    (α.comp (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))).val.toRingHom) _
    (fun r => h1 r r.2) φ hφ

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsMulEqOfSubfieldClosureEqTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory

theorem exists_mul_eq_of_subfield_closure_eq_top {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {t : Set Ω} (ht : Subfield.closure (Set.range (algebraMap K Ω) ∪ t) = ⊤)
    (R : Subalgebra K Ω) (hR : t ⊆ R) (x : Ω) : ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  haveI : IsFractionRing R.toSubring Ω := isFractionRing_subring_of_closure_eq_top ht R.toSubring
    (Set.union_subset (by rintro _ ⟨a, rfl⟩; exact R.algebraMap_mem a) hR)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R.toSubring) x
  have hb0 : (b : Ω) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  exact ⟨a, a.2, b, b.2, hb0, div_mul_cancel₀ _ hb0⟩

theorem exists_normal_charts_over_dvr :
    ∀ (K Ω O : Type) [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (io : K →+* FractionRing O) (gens es : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → (∀ e ∈ es, e ≠ 0 ∧ e ∈ Subring.closure ((algebraMap K Ω '' {a | io a ∈ Set.range (algebraMap O (FractionRing O))}) ∪ (gens : Set Ω))) → (∀ e ∈ es, Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))) → ∃ (J : Type) (_ : Finite J) (A : J → Type) (_ : ∀ j, CommRing (A j)) (_ : ∀ j, IsDomain (A j)) (_ : ∀ j, Algebra O (A j)) (α : ∀ j, Ω →+* FractionRing (A j)), (∀ j, Algebra.FiniteType O (A j) ∧ Module.Flat O (A j) ∧ IsIntegrallyClosed (A j)) ∧ (∀ j (k : K) (a b : O), io k * algebraMap O _ b = algebraMap O _ a → α j (algebraMap K Ω k) * algebraMap (A j) _ (algebraMap O (A j) b) = algebraMap (A j) _ (algebraMap O (A j) a)) ∧ (∀ j, ∀ g ∈ gens, α j g ∈ Set.range (algebraMap (A j) (FractionRing (A j)))) ∧ ∀ e ∈ es, ∀ (L : Type) [Field L] (W : ValuationSubring L) (χ : FractionRing O →+* L) (ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* L), (∀ k : K, ψ (algebraMap K _ k) = χ (io k)) → (∀ a : O, χ (algebraMap O _ a) ∈ W) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → ψ g ∈ W) → ∃ (j : J) (φ : A j →+* L), (∀ x, φ x ∈ W) ∧ (∀ a : O, φ (algebraMap O (A j) a) = χ (algebraMap O _ a)) ∧ ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j), α j r * algebraMap (A j) _ s = algebraMap (A j) _ x → ψ r * φ s = φ x := by
  classical
  intro K Ω O _ _ _ _ _ _ _ io gens es hgen _ hsm
  letI : Algebra K (FractionRing O) := io.toAlgebra
  obtain ⟨J, hJ, Ω', hΩ', α, gm, hαgm, htop, hR⟩ :=
    GlobalTheory.BaseChangeComponents.components K (FractionRing O) Ω (Algebra.adjoin K (gens : Set Ω))
      (Subalgebra.fg_adjoin_finset gens)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ Algebra.subset_adjoin)
  have hαgm' : ∀ j (k : K), α j (algebraMap K Ω k) = gm j (io k) := hαgm
  letI : ∀ j, Algebra O (Ω' j) := fun j => ((gm j).comp (algebraMap O (FractionRing O))).toAlgebra
  have hO : ∀ j (a : O), algebraMap O (Ω' j) a = gm j (algebraMap O (FractionRing O) a) :=
    fun _ _ => rfl
  have hinj : ∀ j, Function.Injective (algebraMap O (Ω' j)) := fun j =>
    (gm j).injective.comp (IsFractionRing.injective O (FractionRing O))
  have hcl : ∀ j, Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) = ⊤ := by
    intro j
    set E := Subfield.closure (Set.range (algebraMap O (Ω' j)) ∪
      ((gens.image (α j) : Finset (Ω' j)) : Set (Ω' j))) with hE
    have hgm : ∀ a, gm j a ∈ E := by
      intro a
      obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀, ← hO, ← hO]
      exact div_mem (Subfield.subset_closure (Or.inl ⟨x, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨y, rfl⟩))
    have hα : (⊤ : Subfield Ω) ≤ E.comap (α j) := by
      rw [← hgen, Subfield.closure_le]
      rintro x (⟨k, rfl⟩ | hx)
      · change α j _ ∈ E
        rw [hαgm']; exact hgm _
      · change α j _ ∈ E
        exact Subfield.subset_closure (Or.inr (by
          rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩))
    rw [eq_top_iff, ← htop j, Subfield.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact hα (Subfield.mem_top y)
    · exact hgm y
  choose A hsA hft hfl hic hfr hmin hW using fun j =>
    GlobalTheory.exists_normalisation_adjoin_finset_dvr O (Ω' j) (hinj j) (gens.image (α j)) (hcl j)
  let ε : ∀ j, Ω' j ≃ₐ[A j] FractionRing (A j) := fun j =>
    (FractionRing.algEquiv (A j) (Ω' j)).symm
  have hε : ∀ j (x : A j), algebraMap (A j) (FractionRing (A j)) x = ε j (x : Ω' j) :=
    fun j x => ((ε j).commutes x).symm
  refine ⟨J, hJ, fun j => A j, inferInstance, inferInstance, inferInstance,
    fun j => ((ε j).toRingEquiv.toRingHom).comp (α j),
    fun j => ⟨hft j, hfl j, hic j⟩, ?_, ?_, ?_⟩
  · intro j k a b h
    rw [hε, hε]
    change ε j (α j _) * ε j (algebraMap O (Ω' j) b) = ε j (algebraMap O (Ω' j) a)
    rw [← map_mul, hαgm', hO, hO, ← map_mul, h]
  · intro j g hg
    refine ⟨⟨α j g, hsA j (by rw [Finset.coe_image]; exact ⟨g, hg, rfl⟩)⟩, ?_⟩
    rw [hε]; rfl
  · intro e he L _ W χ ψ hψ hχ hg
    have hsub : (gens : Set Ω) ⊆ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) :=
      (Set.subset_insert _ _).trans Algebra.subset_adjoin
    obtain ⟨hD, hφ⟩ := hR (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (hsm e he)
      (exists_mul_eq_of_subfield_closure_eq_top hgen _ hsub)
    obtain ⟨j, φ, h1, h2⟩ := hφ L χ ψ hψ
    have hgmD : ∀ a, gm j a ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
    have hαD : ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), α j r ∈ Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      fun r => Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩)
    have hAD := hmin j _ (hD j) (fun a => hgmD _) (by
      rw [Finset.coe_image]
      rintro _ ⟨g, hg, rfl⟩
      exact hαD ⟨g, hsub hg⟩)
    let inc : A j →+* Subring.closure (α j '' (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) : Set Ω) ∪ Set.range (gm j)) :=
      ((A j).val : A j →+* Ω' j).codRestrict _ fun x => hAD x.2
    have hφO : ∀ a : O, (φ.comp inc) (algebraMap O (A j) a) = χ (algebraMap O _ a) :=
      fun a => h2 _ (hgmD _)
    refine ⟨j, φ.comp inc, hW j L W (φ.comp inc) (fun a => by rw [hφO]; exact hχ a) ?_, hφO, ?_⟩
    · intro x hx
      obtain ⟨g, hg', hgx⟩ := Finset.mem_image.mp hx
      have : inc x = ⟨α j (⟨g, hsub hg'⟩ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), hαD _⟩ :=
        Subtype.ext hgx.symm
      rw [RingHom.comp_apply, this, h1]
      exact hg _ hg'
    · intro r x s h
      rw [hε, hε] at h
      have h' : α j r * (s : Ω' j) = x := (ε j).injective (by rw [map_mul]; exact h)
      rw [← h1 r (hαD r), RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg φ (Subtype.ext h')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_valuationSubring_comap_eq_nonunits {K L : Type} [Field K] [Field L] (f : K →+* L)
    (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U ∧ ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
  classical
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  refine ⟨W, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxU
      have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
      have hinv : x⁻¹ ∈ U := (U.mem_or_inv_mem x).resolve_left hxU
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U) := by
        intro hu
        obtain ⟨⟨y, hy⟩, hyx⟩ := isUnit_iff_exists_inv.mp hu
        have hyx' : x⁻¹ * y = 1 := congrArg Subtype.val hyx
        have : y = x := by
          calc y = x * (x⁻¹ * y) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hx0, _root_.one_mul]
            _ = x := by rw [hyx', _root_.mul_one]
        exact hxU (this ▸ hy)
      apply hnu
      apply (hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))
      refine isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · intro hx
      exact hW ⟨x, hx⟩
  · intro x hx
    obtain ⟨hxU, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
    have hfx : f x ∈ W := hW ⟨x, hxU⟩
    have key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmax
      exact hloc.map_nonunit (⟨x, hxU⟩ : U) hu
    exact (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩

theorem exists_prime_natCast_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  classical
  have hbot : la.asIdeal ≠ ⊥ := la.ne_bot
  have hprime : la.asIdeal.IsPrime := la.isPrime
  have main : ∀ n : ℕ, (n : 𝓞 K) ∈ la.asIdeal → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hn0
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hn))
      obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
      rw [Nat.cast_mul] at hn
      rcases hprime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
        refine ih m ?_ h hm0
        calc m = 1 * m := (_root_.one_mul m).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hm0)
  exact main _ (Ideal.absNorm_mem la.asIdeal) (by rwa [Ne, Ideal.absNorm_eq_zero_iff])

theorem modelAt_of_good_level : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by
  intro hI E _ _ _ H Dw hpq Xo l c la hgood
  obtain ⟨-, hI⟩ := hI
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xo
  unfold ModelAt
  obtain ⟨p, hp, hpla⟩ := exists_prime_natCast_mem la
  obtain ⟨W, hcomap, hnon⟩ :=
    exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring
  have hlt : la.valuation c.F (p : c.F) < 1 := by
    have h := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla
    exact_mod_cast h
  have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    have hpos : 0 < la.valuation c.F (p : c.F) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)
  have hW : (p : ℂ) ∈ W.nonunits := by
    have h := hnon _ hpU
    rwa [map_natCast] at h
  let i : Idx H p := ⟨l, c, hgood p hp hpla⟩
  rw [← hcomap]
  exact ⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩

end GlobalTheory.Reg
end

