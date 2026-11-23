module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisEqEmbeddingsOCModPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EmbTwo

theorem range_eq_of_normal {F E L : Type} [Field F] [Field E] [Algebra F E] [Normal F E] [Field L]
    [Algebra F L] (φ ψ : E →ₐ[F] L) : φ.fieldRange = ψ.fieldRange := by
  let e : E ≃ₐ[F] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal F ψ.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem exists_approx (y : OC l) : ∃ (z : OC l) (w : OC l), (∃ z' : Om l, (z : ℂ_[l]) = (z' : ℂ_[l])) ∧
    y = z + (l : OC l) * w := by
  have hl : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  obtain ⟨z', hz'⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt (y : ℂ_[l]) hl
  set w : ℂ_[l] := (y : ℂ_[l]) - (z' : ℂ_[l]) with hw
  have hw1 : ‖w‖ < ‖((l : ℕ) : ℂ_[l])‖ := by rw [hw, ← dist_eq_norm]; exact hz'
  have hwO : w ∈ 𝓞_ℂ_[l] := (GlobalTheory.RingBasics.mem_OC _).2 (hw1.le.trans GlobalTheory.RingBasics.norm_p_lt.le)
  have hzO : (z' : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    have : (z' : ℂ_[l]) = (y : ℂ_[l]) - w := by rw [hw]; ring
    rw [this]; exact Subring.sub_mem _ y.2 hwO
  have hq : w / ((l : ℕ) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC, norm_div, div_le_one hl]; exact hw1.le
  refine ⟨⟨_, hzO⟩, ⟨_, hq⟩, ⟨z', rfl⟩, Subtype.ext ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ GlobalTheory.RingBasics.p_ne_zero, hw]; ring

end GlobalTheory.EmbTwo


open GlobalTheory.EmbTwo in
theorem GlobalTheory.EmbTwo.exists_gal_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  intro l _ K D _ _ θ₁ θ₂ h1 h2 hK
  let F := FractionRing D
  have i1 : Function.Injective ((algebraMap D F).comp θ₁) := (IsFractionRing.injective D F).comp h1
  have i2 : Function.Injective ((algebraMap D F).comp θ₂) := (IsFractionRing.injective D F).comp h2
  let τ₁ : ℂ_[l] →+* F := IsFractionRing.lift i1
  let τ₂ : ℂ_[l] →+* F := IsFractionRing.lift i2
  let σ₁ : Om l →+* F := τ₁.comp (algebraMap (Om l) ℂ_[l])
  let σ₂ : Om l →+* F := τ₂.comp (algebraMap (Om l) ℂ_[l])
  have hτ₁ : ∀ y : OC l, τ₁ (y : ℂ_[l]) = algebraMap D F (θ₁ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i1 y
  have hτ₂ : ∀ y : OC l, τ₂ (y : ℂ_[l]) = algebraMap D F (θ₂ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i2 y

  have hO : ∀ r : ↥(OL K), σ₁ ((r : ↥K.1) : Om l) = σ₂ ((r : ↥K.1) : Om l) := fun r => by
    change τ₁ ((intToOC K r : OC l) : ℂ_[l]) = τ₂ ((intToOC K r : OC l) : ℂ_[l])
    rw [hτ₁, hτ₂, hK]

  have hKK : ∀ x : ↥K.1, σ₁ (x : Om l) = σ₂ (x : Om l) := fun x => by
    have ha : IsAlgebraic ℤ_[l] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
    let r : ↥(OL K) := ⟨y • x, hy⟩
    let s : ↥(OL K) := algebraMap ℤ_[l] ↥(OL K) y
    have hrs : ((r : ↥K.1) : Om l) = ((s : ↥K.1) : Om l) * (x : Om l) := by
      change ((y • x : ↥K.1) : Om l) = _
      rw [Algebra.smul_def]; rfl
    have hs0 : ((s : ↥K.1) : Om l) ≠ 0 := by
      intro h0
      apply hy0
      have : (s : ↥K.1) = 0 := Subtype.ext h0
      have h3 : algebraMap ℤ_[l] ↥K.1 y = 0 := this
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, _root_.map_eq_zero] at h3
      exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h3.trans (map_zero _).symm)
    have e1 := hO r
    rw [hrs, map_mul, map_mul, hO s] at e1
    exact mul_left_cancel₀ ((map_ne_zero σ₂).2 hs0) e1
  letI : Algebra ↥K.1 F := (σ₁.comp (algebraMap ↥K.1 (Om l))).toAlgebra
  let φ₁ : Om l →ₐ[↥K.1] F := { σ₁ with commutes' := fun _ => rfl }
  let φ₂ : Om l →ₐ[↥K.1] F := { σ₂ with commutes' := fun x => (hKK x).symm }
  have hR := range_eq_of_normal φ₁ φ₂
  let e₁ : Om l ≃ₐ[↥K.1] φ₁.fieldRange := AlgEquiv.ofInjectiveField φ₁
  have hmem : ∀ z, φ₂ z ∈ φ₁.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : Om l →ₐ[↥K.1] Om l := e₁.symm.toAlgHom.comp (φ₂.codRestrict φ₁.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, σ₁ (g₀ z) = σ₂ z := fun z => by
    have := congrArg Subtype.val (e₁.apply_symm_apply ⟨φ₂ z, hmem z⟩)
    exact this
  let g₁ : Om l ≃ₐ[↥K.1] Om l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  let g : GQ l := g₁.restrictScalars ℚ_[l]
  have hgK : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g₀.commutes ⟨x, hx⟩
  have hg : ∀ z : Om l, σ₁ (g z) = σ₂ z := hg₀
  have c1 : ∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO g y) := by
    rintro y ⟨z, hz⟩
    apply IsFractionRing.injective D F
    rw [← hτ₁, ← hτ₂]
    have e2 : ((Per.σO g y : OC l) : ℂ_[l]) = ((g z : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l g y).trans ?_
      rw [hz, GlobalTheory.RingBasics.σC_coe]
    rw [e2, hz]
    exact (hg z).symm
  refine ⟨⟨g, hgK⟩, c1, fun y => ?_⟩
  obtain ⟨z, w, hz, rfl⟩ := exists_approx y
  refine ⟨θ₂ w - θ₁ (Per.σO g w), ?_⟩
  have := c1 z hz
  simp only [map_add (f := _), map_mul, map_natCast]
  rw [this]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

theorem isUnit_l : IsUnit (l : (PreDisc l (0 : W) 1)⟦X⟧) := by
  rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧)]
  refine IsUnit.map _ ?_
  rw [← map_natCast (algebraMap W (PreDisc l (0 : W) 1))]
  exact IsLocalization.Away.algebraMap_isUnit _

def phi : PreDisc l (X : W⟦X⟧) ρ →+* (PreDisc l (0 : W) 1)⟦X⟧ :=
  IsLocalization.Away.lift (l : W⟦X⟧) (g := PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1))) (by
    rw [map_natCast]; exact isUnit_l l)

theorem phi_alg (s : W⟦X⟧) :
    phi l ρ (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) s) = PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) s :=
  IsLocalization.Away.lift_eq _ _ s

theorem phi_inv :
    phi l ρ (IsLocalization.Away.invSelf (l : W⟦X⟧)) = C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) := by
  have h := congrArg (phi l ρ) (IsLocalization.Away.mul_invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧))
  rw [map_mul, phi_alg, map_natCast, map_one] at h
  have h2 : (l : (PreDisc l (0 : W) 1)⟦X⟧) * C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) = 1 := by
    rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧), ← map_mul,
      ← map_natCast (algebraMap W (PreDisc l (0 : W) 1)), IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_l l).mul_left_cancel (h.trans h2.symm)

def aPre (n : ℕ) : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (0 : W) 1 :=
  (coeff n : (PreDisc l (0 : W) 1)⟦X⟧ →ₗ[PreDisc l (0 : W) 1] PreDisc l (0 : W) 1).toAddMonoidHom.comp
    (phi l ρ).toAddMonoidHom

theorem aPre_apply (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n y = coeff n (phi l ρ y) := rfl

theorem aPre_mono (n a b c : ℕ) :
    aPre l ρ n (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ a * X ^ b) *
      IsLocalization.Away.invSelf (l : W⟦X⟧) ^ c) =
    if n = b then algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c else 0 := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv]
  have e : PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) ((l : W⟦X⟧) ^ a * X ^ b) *
      C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) ^ c =
      C (algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) * X ^ b := by
    simp only [map_mul, map_pow, map_natCast, map_X]; ring
  rw [e, coeff_C_mul_X_pow]

theorem norm_W_mono (hl : 0 < l) (a c : ℕ) :
    ‖algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c‖ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a := by
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  exact gauge_le l (0 : W) 1 (by positivity) (Submodule.subset_span ⟨a, 0, c, by field_simp; simp, by simp⟩)

theorem norm_aPre_le (hl : 0 < l) (hρ : ρ ≤ 1) (y : PreDisc l (X : W⟦X⟧) ρ) (n : ℕ) :
    ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
  suffices h : ∀ r : ℝ, 0 < r → y ∈ ball l (X : W⟦X⟧) ρ r → ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r from
    le_of_forall_gt_imp_ge_of_dense fun r hr =>
      h r ((norm_nonneg y).trans_lt hr) (mem_ball_of_gauge_lt l _ ρ hr) n
  have hρ' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hadd : ∀ (r : ℝ) (n : ℕ) (z w : PreDisc l (0 : W) 1), ‖z‖ * (ρ : ℝ) ^ n ≤ r → ‖w‖ * (ρ : ℝ) ^ n ≤ r →
      ‖z + w‖ * (ρ : ℝ) ^ n ≤ r := fun r n z w hz hw =>
    (mul_le_mul_of_nonneg_right (gauge_add_le_max l (0 : W) 1 z w) (by positivity)).trans
      (by rw [max_mul_of_nonneg _ _ (by positivity)]; exact max_le hz hw)
  intro r hr hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    intro n
    rw [aPre_mono]
    split_ifs with hn
    · subst hn
      calc _ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a * (ρ : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (norm_W_mono l hl a c) (by positivity)
        _ ≤ r := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; exact h1
    · rw [norm_zero, zero_mul]; exact hr.le
  | zero => intro n; rw [map_zero, norm_zero, zero_mul]; exact hr.le
  | add x y _ _ hx hy => intro n; rw [map_add (f := _)]; exact hadd r n _ _ (hx n) (hy n)
  | smul s x _ hx =>
    intro n
    rw [aPre_apply, Algebra.smul_def, map_mul, phi_alg, coeff_mul]
    refine Finset.sum_induction _ (fun z => ‖z‖ * (ρ : ℝ) ^ n ≤ r) (fun z w hz hw => hadd r n z w hz hw)
      (by rw [norm_zero, zero_mul]; exact hr.le) (fun p hp => ?_)
    have hp2 : p.2 ≤ n := by have := _root_.Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
    rw [coeff_map]
    calc ‖algebraMap W (PreDisc l (0 : W) 1) (coeff p.1 s) * coeff p.2 (phi l ρ x)‖ * (ρ : ℝ) ^ n
        ≤ (1 * ‖coeff p.2 (phi l ρ x)‖) * (ρ : ℝ) ^ p.2 :=
          mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _) (norm_nonneg _)))
            (pow_le_pow_of_le_one (by positivity) hρ' hp2) (by positivity) (by positivity)
      _ ≤ r := by rw [one_mul]; exact hx p.2

theorem norm_X_pow_le (hρ0 : 0 < ρ) (m : ℕ) :
    ‖algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m)‖ ≤ (ρ : ℝ) ^ m := by
  have := norm_toDisc_pow_le (l := l) (u := (X : W⟦X⟧)) (ρ := ρ) m hρ0
  rwa [toDisc, RingHom.comp_apply, norm_ofPre] at this

theorem norm_le_of_aPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r) : ‖y‖ ≤ r := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  have hco : ∀ n, aPre l ρ n y =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
    intro n
    rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ht0 (pow_pos hl c)) (show (ρ : ℝ) < 1 by exact_mod_cast hρ)
  set hd : W⟦X⟧ := ∑ m ∈ Finset.range N, C (coeff m s) * X ^ m with hhd
  obtain ⟨s', hs'⟩ : (X : W⟦X⟧) ^ N ∣ s - hd := X_pow_dvd_iff.2 fun m hm => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hhd, map_sub, coeff_C_mul_X_pow, map_sum, Finset.mem_range, hm]
  have hsplit : y = ∑ m ∈ Finset.range N, algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c +
      algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, ← Finset.sum_mul, ← map_sum, ← add_mul, ← map_add (f := _), ← hs', ← hhd, add_sub_cancel]
  rw [hsplit]
  refine (gauge_add_le_max l _ ρ _ _).trans (max_le ?_ ?_)
  · refine Finset.sum_induction _ (fun z => ‖z‖ ≤ t)
      (fun a b ha hb => (gauge_add_le_max l _ ρ a b).trans (max_le ha hb)) (by rw [norm_zero]; exact ht0.le)
      fun m _ => ?_
    have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (algebraMap W _ (coeff m s) *
          IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) *
          algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m) := by
      rw [map_mul (preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C), map_pow (preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C), preMap_alg, preMap_inv,
        map_mul (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ))]; ring
    rw [e]
    have hpm := norm_preMap_le (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (by simp)
      (algebraMap W _ (coeff m s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c)
    refine (norm_mul_le _ _).trans ((mul_le_mul hpm (norm_X_pow_le l ρ hρ0 m) (norm_nonneg _)
      (norm_nonneg _)).trans ?_)
    rw [← hco]; exact (h m).trans ht.le
  · have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        s' • (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ 0 * X ^ N) *
          IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
      rw [Algebra.smul_def, pow_zero, one_mul, mul_comm ((X : W⟦X⟧) ^ N) s', map_mul, mul_assoc]
    rw [e]
    refine gauge_le l _ ρ ht0 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, N, c, ?_, rfl⟩))
    rw [lt_div_iff₀ (by positivity)] at hN
    rw [pow_zero, mul_one, mul_comm]; exact hN.le

theorem continuous_aPre (hl : 0 < l) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) (n : ℕ) : Continuous (aPre l ρ n (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ ((ρ : ℝ) ^ n)⁻¹ fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact norm_aPre_le l ρ hl hρ y n

theorem norm_aPre_le_const (hl : 0 < l) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ∃ C : ℝ, ∀ n, ‖aPre l ρ n y‖ ≤ C := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(l : ℝ) ^ c / (l : ℝ) ^ 0, fun n => ?_⟩
  rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine (norm_mul_le _ _).trans ((mul_le_mul (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _)
    le_rfl (norm_nonneg _) zero_le_one).trans ?_)
  rw [one_mul]
  have := norm_W_mono (W := W) l hl 0 c
  rwa [pow_zero, map_one, one_mul] at this

theorem exists_coeff_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1),
      (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧
      (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧
      (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧
      ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  intro l _ K bk ρ hρ0 hρ1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hc := fun n => continuous_aPre l (W := Wq l bk.a) ρ hl hρ0 hρ1.le n
  let A : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1) := fun n => (aPre l ρ n).completion (hc n)
  have hA : ∀ n y, A n (ofPre l (X : bk.S) ρ y) = ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n y) := fun n y =>
    AddMonoidHom.completion_coe _ _ y
  have hAc : ∀ n, Continuous (A n) := fun n => AddMonoidHom.continuous_completion _ _
  have h2 : ∀ n y, ‖A n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
    intro n y
    refine (denseRange_ofPre l (X : bk.S) ρ).induction_on y
      (isClosed_le (((hAc n).norm).mul continuous_const) continuous_norm) fun y => ?_
    rw [hA, norm_ofPre, norm_ofPre]
    exact norm_aPre_le l ρ hl hρ1.le y n
  refine ⟨A, fun n x => ?_, h2, fun y r hr h => ?_, fun y => ?_⟩
  · change A n (ofPre l (X : bk.S) ρ (algebraMap _ _ x)) = ofPre l (0 : Wq l bk.a) 1 (algebraMap _ _ (coeff n x))
    rw [hA, aPre_apply, phi_alg, coeff_map]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    have hz' : ‖z‖ ≤ r + ε / 2 := by
      refine norm_le_of_aPre l ρ hρ0 hρ1 z _ (by positivity) fun n => ?_
      rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm, show ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) =
        A n y - A n (y - ofPre l (X : bk.S) ρ z) by rw [map_sub, sub_sub_cancel, hA]]
      refine (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)).trans ?_
      rw [add_mul]
      exact add_le_add (h n) ((h2 n _).trans hz.le)
    calc ‖y‖ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + ‖ofPre l (X : bk.S) ρ z‖ := norm_le_norm_sub_add _ _
      _ ≤ ε / 2 + (r + ε / 2) := add_le_add hz.le (by rw [norm_ofPre]; exact hz')
      _ = r + ε := by ring
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    obtain ⟨C, hC⟩ := norm_aPre_le_const l ρ hl z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) (show (0 : ℝ) < C + 1 by linarith))
      (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hρn : (ρ : ℝ) ^ n ≤ (ρ : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by exact_mod_cast hρ1.le) hn
    rw [lt_div_iff₀ (by linarith)] at hN
    have e : A n y = A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) := by
      rw [← hA, ← map_add (f := _), sub_add_cancel]
    rw [e]
    calc ‖A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ * (ρ : ℝ) ^ n
        ≤ (‖A n (y - ofPre l (X : bk.S) ρ z)‖ + ‖aPre l ρ n z‖) * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm]
          exact norm_add_le _ _
      _ = ‖A n (y - ofPre l (X : bk.S) ρ z)‖ * (ρ : ℝ) ^ n + ‖aPre l ρ n z‖ * (ρ : ℝ) ^ n := add_mul _ _ _
      _ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + C * (ρ : ℝ) ^ N :=
          add_le_add (h2 n _) (mul_le_mul (hC n) hρn (by positivity) hC0)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hz ?_
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ ρ by positivity) N]
      _ = ε := add_halves ε

end GlobalTheory.BSP.DiscSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorH2Twist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.FreeTwistH2

theorem powSub_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    ((powSub (M := O) ϖ n : Submodule O O) : Set O) = ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
  ext x
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, SetLike.mem_coe,
    mem_powSub, Ideal.mem_span_singleton']
  simp only [smul_eq_mul, mul_comm]

theorem powSub_open_basis {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hO : PadicCoeff p O) {ϖ : O} (hϖ : Irreducible ϖ) :
    (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) ∧
      ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U := by
  haveI := hO.ring
  obtain ⟨h1, h2⟩ := (isAdic_iff).1 hO.adic
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · rw [powSub_eq hϖ]; exact h1 n
  · obtain ⟨n, hn⟩ := h2 U hU
    exact ⟨n, by rw [powSub_eq hϖ]; exact hn⟩

theorem exists_free_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K →
    PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε
  haveI := hO.compact
  haveI := hO.t2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hopen, hbasis⟩ := powSub_open_basis hO hϖ
  haveI := GlobalTheory.T.isAdicComplete_of_padicCoeff' hO
  have hd : ∀ n : ℕ, ringChar (O ⧸ IsLocalRing.maximalIdeal O ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hO.p_mem n
  let φ : ℤ_[p] →+* O := IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal O)
    (fun n => (ZMod.castHom (hd n) (O ⧸ IsLocalRing.maximalIdeal O ^ n)).comp (PadicInt.toZModPow n))
    (fun {m n} hle => by
      rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_zmod _ _)
  have hφ : Continuous φ := _root_.GlobalTheory.padicInt_ringHom_continuous_of_padicCoeff hO φ
  let χZ : Formalism.GaloisCohomology.GK p K →* ℤ_[p]ˣ := (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))
  have hχc : Continuous fun g => (χZ g : ℤ_[p]) :=
    Units.continuous_val.comp (cyclotomicCharacter.continuous p K (PadicAlgCl p))
  obtain ⟨c, hc⟩ := GlobalTheory.TateTop.exists_gen_all hχc fun r => by
    have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    exact GlobalTheory.TateTop.exists_gen hχc
      (hT p K hK (r + 1) (ZMod (p ^ (r + 1))) (ReciprocityTheory.Gal.charRep (GlobalTheory.Cyc.TwistLift.redChar χZ (r + 1)))
        (Nat.succ_pos _) (GlobalTheory.Cyc.TwistLift.contAction_charRep _
          ((GlobalTheory.PadicH2Separated.continuous_reduction _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT p K hK (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  let e : G ≃* Formalism.GaloisCohomology.GK p K := i.toMulEquiv
  have he : Continuous e := i.continuous
  have he' : Continuous e.symm := i.symm.continuous
  let χ : G →* ℤ_[p]ˣ := χZ.comp e.toMonoidHom
  let cG : G × G → ℤ_[p] := fun q => c (e q.1, e q.2)
  have hcG : ∀ r, GlobalTheory.TateTop.Gen χ r cG := fun r => (hc r).transport e he he'
  have hεφ : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p]) := fun g => _root_.GlobalTheory.CycImage.cyc_eq_image hO φ i hε g
  have hχGc : Continuous fun g => (χ g : ℤ_[p]) := hχc.comp he
  have hεc : Continuous fun g => ((ε g : Oˣ) : O) := by
    simp_rw [hεφ]
    exact hφ.comp hχGc
  have hcont : ContAction (twist ε O) := by
    show Continuous fun q : G × O => twist ε O q.1 q.2
    simp only [twist_apply, smul_eq_mul]
    exact (hεc.comp continuous_fst).mul continuous_snd
  have hfin := fun n => GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i (twist ε O) hcont ϖ hϖ hopen n
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hcG r)
  have hcc : Continuous cG :=
    GlobalTheory.PadicH2Separated.continuous_of_reductions cG fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[p]) * cG (h, k) - cG (g * h, k) + cG (g, h * k) - cG (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add (f := _), map_mul, map_zero] using (hG n).1.2 g h k
  let z0 : G × G → O := fun q => φ (cG q)
  have hz0 : z0 ∈ Z2 (twist ε O) := by
    refine (mem_cocycles2 _ _).2 ⟨hφ.comp hcc, fun g h k => ?_⟩
    simp only [twist_apply, smul_eq_mul, z0, hεφ]
    rw [← map_mul, ← map_sub, ← map_add (f := _), ← map_sub, hcoc, map_zero]
  let Z : H2 (twist ε O) := Submodule.Quotient.mk ⟨z0, hz0⟩
  refine ⟨Z, fun a b hab => ?_, fun y => ?_⟩
  · have h0 : (a - b) • Z = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hab
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 h0
    refine sub_eq_zero.1 (GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen (a - b) f hf
      fun g h => ?_)
    have e1 := congrFun hfd (g, h)
    rw [e1]
    rfl
  · induction y using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨a, ha⟩ := GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen w.1 w.2
      refine ⟨a, ?_⟩
      show a • Z = Submodule.Quotient.mk w
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      show (w.1 - a • z0) ∈ B2 (twist ε O)
      refine GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow ε ϖ hopen hbasis hfin _
        (sub_mem w.2 (Submodule.smul_mem _ a hz0)) fun n => ?_
      obtain ⟨b, hb, hbd⟩ := ha n
      exact ⟨b, hb, fun g h => by rw [hbd]; rfl⟩

end GlobalTheory.FreeTwistH2
end
end

