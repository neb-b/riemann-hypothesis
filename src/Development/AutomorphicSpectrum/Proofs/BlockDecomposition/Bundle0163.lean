module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0107
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0006
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0009
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingForUpwardClosedCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GlobRel

theorem subsingleton_H_of_retract {R : Type} [CommRing R] {K L : Cx R}
    (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (n : ℕ) (hL : Subsingleton (L.H n)) : Subsingleton (K.H n) := by
  have key : ∀ a : K.H n, ψ.mapH n (φ.mapH n a) = a := by
    intro a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    change Submodule.Quotient.mk (ψ.mapZ n (φ.mapZ n z)) = Submodule.Quotient.mk z
    congr 1
    exact Subtype.ext (h n z.1)
  refine ⟨fun a b => ?_⟩
  rw [← key a, ← key b, Subsingleton.elim (φ.mapH n a) (φ.mapH n b)]

theorem subsingleton_HU_iter {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    (F : C ⥤ ModuleCat.{0} R) (A B : ObjectProperty C) (P : ObjectProperty A.FullSubcategory)
    (hBA : ∀ T, B T → A T) (hP : ∀ T : A.FullSubcategory, P T ↔ B T.obj) (j : ℕ)
    (hB : Subsingleton (HU F B j)) : Subsingleton (HU (A.ι ⋙ F) P j) := by
  let G : B.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (A.lift B.ι fun T => hBA _ T.property) fun T => (hP _).2 T.property
  let G' : P.FullSubcategory ⥤ B.FullSubcategory :=
    B.lift (P.ι ⋙ A.ι) fun T => (hP _).1 T.property
  let m : CH.Mor (P.ι ⋙ A.ι ⋙ F) (B.ι ⋙ F) (RingHom.id R) := ⟨G, fun _ => LinearMap.id, fun _ _ => rfl⟩
  let m' : CH.Mor (B.ι ⋙ F) (P.ι ⋙ A.ι ⋙ F) (RingHom.id R) := ⟨G', fun _ => LinearMap.id, fun _ _ => rfl⟩
  exact subsingleton_H_of_retract m.hom m'.hom (fun n x => funext fun s => rfl) j hB

theorem glob_van_rel : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS W S) j)) →
      ∀ j < s, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j)) →
      ∀ j, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS W S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) := by
  intro R _ C _ F ι _ W hW s
  let U' : ι → ObjectProperty (ObjectProperty.FullSubcategory fun T : C => ∃ α, W α T) :=
    fun α T => W α T.obj
  have hU : ∀ α, Cosieve (U' α) := fun α T T' f h => hW α f.hom h T'.property
  have hc : ∀ T, ∃ α, U' α T := fun T => T.property
  have tr : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j) →
      Subsingleton (HU ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) (capS U' S) j) := by
    intro S hS j h
    obtain ⟨a, ha⟩ := hS
    exact subsingleton_HU_iter F _ (capS W S) (capS U' S) (fun T hT => ⟨a, hT a ha⟩)
      (fun T => Iff.rfl) j h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.cech_vanishing_from_cover ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) U' hU hc s
  exact ⟨fun h j hj => h1 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj,
    fun h j => h2 (fun S hS j => tr S hS j (h S hS j)) j,
    fun h j hj => h3 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj⟩

end GlobalTheory.CompanionTheory.GlobRel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogenise
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.FSCrofton.HessFrame

private lemma contDiffOn_norm_sq_of_differentiableOn {d : ℕ} {U : Set (V d)} (hU : IsOpen U) {f : V d → ℂ}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℝ ∞ (fun v => ‖f v‖ ^ 2) U :=
  (contDiff_norm_sq ℝ).comp_contDiffOn
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d f U hU hf).restrict_scalars ℝ)

theorem cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by
  intro z hz
  obtain ⟨R, hRdef⟩ : ∃ R : V d → ℝ,
      R = fun v => 1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2 := ⟨_, rfl⟩
  have hpos : ∀ v ∈ U, 0 < ‖b j₀ v‖ ^ 2 := fun v hv => pow_pos (norm_pos_iff.2 (h0 v hv)) 2
  have hRpos : ∀ v, 0 < R v := fun v => by rw [hRdef]; positivity
  have hp : ContDiffOn ℝ ∞ (fun v => Real.log (‖b j₀ v‖ ^ 2)) U :=
    (contDiffOn_norm_sq_of_differentiableOn hU (hb j₀)).log fun v hv => (hpos v hv).ne'
  have hq : ContDiffOn ℝ ∞ (fun v => Real.log (R v)) U := by
    refine ContDiffOn.log ?_ fun v _ => (hRpos v).ne'
    rw [hRdef]
    exact contDiffOn_const.add
      (ContDiffOn.sum fun j _ => contDiffOn_norm_sq_of_differentiableOn hU (by
        simpa only [div_eq_mul_inv] using (hb j.1).fun_mul ((hb j₀).fun_inv h0)))
  have hsplit : ∀ v ∈ U, ∑ j, ‖b j v‖ ^ 2 = ‖b j₀ v‖ ^ 2 * R v := by
    intro v hv
    have hn : ‖b j₀ v‖ ^ 2 ≠ 0 := (hpos v hv).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (F := inferInstance) (Finset.univ.erase j₀) (p := fun j => j ≠ j₀) (by simp),
      hRdef]
    simp only [mul_add, mul_one, Finset.mul_sum, norm_div, div_pow, mul_div_cancel₀ _ hn]
  have hev : (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun v => ((Real.log (‖b j₀ v‖ ^ 2) + 1 * Real.log (R v) : ℝ) : ℂ) := by
    refine Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => ?_
    simp only
    rw [hsplit v hv, Real.log_mul (hpos v hv).ne' (hRpos v).ne', one_mul]
  have hzero : cHess d (fun w => ((Real.log (‖b j₀ w‖ ^ 2) : ℝ) : ℂ)) z = 0 := by
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hU hz (hb j₀) h0 j k
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hev,
    ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hU hp hq 1 hz, hzero, zero_add, Complex.ofReal_one,
    one_smul, hRdef]

end GlobalTheory.CompanionTheory.FSCrofton.HessFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescription
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

private theorem exists_factorial_mul_eq_pow' (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, m, hm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) l hp.one_lt.ne'
  have hcop : IsCoprime (((l : ℤ)) : A.W) (((m : ℤ)) : A.W) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).intCast
  obtain ⟨u, v, huv⟩ := hcop
  push_cast at huv
  have := A.completeW
  have hj : (l : A.W) ∈ (⊥ : Ideal A.W).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {(l : A.W)}) (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit ((m : A.W) * v) := by
    have h := Ideal.mem_jacobson_bot.1 hj (-u)
    convert h using 1
    linear_combination huv
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  refine ⟨e, v * t, ?_⟩
  rw [hk]
  push_cast
  linear_combination (l : A.W) ^ e * ht

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := by
  obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow' A k
  have hu : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) (k.factorial : A.W)) := by
    have h1 : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) ((l : A.W) ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit _).pow N
    rw [← hc, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [map_natCast] at hu
  unfold CrystallineSemistableComparison.PAlg.dxi0
  apply Subtype.ext
  push_cast
  unfold CrystallineSemistableComparison.dpw
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

theorem xi_mul_divided_power (r : ℕ) :
    algebraMap A.W A.Acr0 A.xi * A.dxi0 r = ((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1) := by
  have h1 := factorial_mul_divided_power_xi A 1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
  rw [← h1, divided_power_xi_mul, add_comm 1 r, Nat.choose_one_right]

theorem exists_factorial_mul_eq_pow (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l)
    (Nat.factorial_ne_zero k) (le_refl _)
  refine ⟨k.factorial.factorization l, A.sW c, ?_⟩
  have := congrArg A.sW hc
  simpa using this

theorem filtration_element_power_multiple_xi (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow A k
    refine ⟨N, A.xi ^ (k - r) * c, ?_⟩
    have h := factorial_mul_divided_power_xi A k
    calc (l : A.Acr0) ^ N * A.dxi0 k = algebraMap A.W A.Acr0 ((l : A.W) ^ N) * A.dxi0 k := by simp
    _ = algebraMap A.W A.Acr0 c * ((k.factorial : A.Acr0) * A.dxi0 k) := by
        rw [← hc, map_mul, map_natCast]; ring
    _ = algebraMap A.W A.Acr0 (A.xi ^ r * (A.xi ^ (k - r) * c)) := by
        rw [h, ← map_pow, ← map_mul]
        congr 1
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
        ring
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N1, w1, h1⟩ := hx
    obtain ⟨N2, w2, h2⟩ := hy
    refine ⟨N1 + N2, (l : A.W) ^ N2 * w1 + (l : A.W) ^ N1 * w2, ?_⟩
    calc (l : A.Acr0) ^ (N1 + N2) * (x + y)
        = (l : A.Acr0) ^ N2 * ((l : A.Acr0) ^ N1 * x) + (l : A.Acr0) ^ N1 * ((l : A.Acr0) ^ N2 * y) := by ring
    _ = _ := by
        rw [h1, h2]
        simp only [map_mul, map_add (f := _), map_pow, map_natCast]
        ring
  | smul a x _ hx =>
    obtain ⟨N, w, h⟩ := hx
    refine ⟨N, a * w, ?_⟩
    rw [Algebra.smul_def]
    calc (l : A.Acr0) ^ N * (algebraMap A.W A.Acr0 a * x)
        = algebraMap A.W A.Acr0 a * ((l : A.Acr0) ^ N * x) := by ring
    _ = _ := by
        rw [h, ← map_mul]
        congr 1
        ring

theorem filtration_element_mod_next_level (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rcases hk.eq_or_lt with h | h
    · subst h
      exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_mul, sub_zero]
      exact (mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨k, Nat.succ_le_of_lt h, rfl⟩)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, h1⟩ := hx
    obtain ⟨w2, h2⟩ := hy
    refine ⟨w1 + w2, ?_⟩
    have e : x + y - algebraMap A.W A.Acr0 (w1 + w2) * A.dxi0 r =
        (x - algebraMap A.W A.Acr0 w1 * A.dxi0 r) + (y - algebraMap A.W A.Acr0 w2 * A.dxi0 r) := by
      rw [map_add (f := _)]; ring
    rw [e]
    exact Ideal.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨w, h⟩ := hx
    refine ⟨a * w, ?_⟩
    have e : a • x - algebraMap A.W A.Acr0 (a * w) * A.dxi0 r =
        algebraMap A.W A.Acr0 a * (x - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ h

theorem divided_power_multiple_next_level_iff (r : ℕ) (w : A.W) :
    algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi} := by
  have hinj : Function.Injective (algebraMap A.W A.Acr0) := by
    intro x y h
    apply A.algebraMap_WL_injective
    exact congrArg Subtype.val h
  constructor
  · intro h
    obtain ⟨N, v, hv⟩ := filtration_element_power_multiple_xi A (r + 1) h
    have hr := factorial_mul_divided_power_xi A r
    have e1 : algebraMap A.W A.Acr0 ((l : A.W) ^ N * w * A.xi ^ r) =
        algebraMap A.W A.Acr0 (A.xi * ((r.factorial : A.W) * v) * A.xi ^ r) := by
      have e2 := congrArg (fun t => (r.factorial : A.Acr0) * t) hv
      simp only [map_mul, map_pow, map_natCast] at e2 ⊢
      linear_combination e2 - (l : A.Acr0) ^ N * algebraMap A.W A.Acr0 w * hr
    have e3 : (l : A.W) ^ N * w = A.xi * ((r.factorial : A.W) * v) :=
      (mul_cancel_right_mem_nonZeroDivisors (pow_mem (_root_.GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.1 r)).1 (hinj e1)
    have e4 : (r.factorial : A.W) * v ∈ Ideal.span {(l : A.W) ^ N} := by
      apply (_root_.GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.2 N
      rw [← e3]
      exact Ideal.mem_span_singleton.2 ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e4
    rw [hy] at e3
    have e5 : w = A.xi * y := by
      apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem A.l_mem_nzd N)).1
      rw [e3]
      ring
    exact Ideal.mem_span_singleton.2 ⟨y, e5⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h
    have h2 := xi_mul_divided_power A r
    have e : algebraMap A.W A.Acr0 (A.xi * y) * A.dxi0 r =
        algebraMap A.W A.Acr0 y * (((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1)) := by
      rw [← h2, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      ((mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨r + 1, le_rfl, rfl⟩)))

theorem crystalline_filtration_graded_pieces : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ),
    (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧
    (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧
    ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W),
      (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  intro l hl A r
  exact ⟨fun z hz => filtration_element_mod_next_level A r hz, fun w => divided_power_multiple_next_level_iff A r w,
    fun z hz => filtration_element_power_multiple_xi A r hz⟩

end GlobalTheory.CompanionTheory.PerfFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeRootValuationQuotient
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem untilt_mod_varpi_sq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest →
    ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧
      R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  intro l _ A hA
  obtain ⟨t, ht⟩ := A.frob_bijective.2 A.pi
  have ht' : t ^ l = A.pi := ht
  have hpow : A.sharp t ^ l = (l : A.U) := by
    rw [← map_pow, ht', A.sharp_pi]
  refine ⟨A.sharp t, hpow, ?_⟩
  have hle : Ideal.span {(l : A.U) ^ 1} ≤ Ideal.span {A.sharp t ^ 2} := by
    rw [pow_one, ← hpow]
    exact Ideal.span_singleton_le_span_singleton.2
      (pow_dvd_pow _ (Fact.out : l.Prime).two_le)
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  let g : A.A →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    (Ideal.Quotient.factor hle).comp A.aToU1
  have hg : Function.Surjective g :=
    (Ideal.Quotient.factor_surjective hle).comp hsurj
  have hπ : ∀ a ∈ Ideal.span {A.pi}, g a = 0 := fun a ha => by
    rw [← hker] at ha
    change Ideal.Quotient.factor hle (A.aToU1 a) = 0
    rw [RingHom.mem_ker.1 ha, map_zero]
  let g' : A.A ⧸ Ideal.span {A.pi} →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    Ideal.Quotient.lift _ g hπ
  have hg' : Function.Surjective g' := Ideal.Quotient.lift_surjective_of_surjective _ hπ hg
  exact ⟨(GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g' hg').2
      (GlobalTheory.CompanionTheory.ValQuot.valuation_comparable_quotient A.pi hA.2),
    (GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g hg).1 hA.1⟩

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyFamily
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

universe w w'

theorem tens_transfer {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₂ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {M' M₂' : Type w'} [AddCommGroup M'] [AddCommGroup M₂']
    {f : ∀ i, N i → M i → M'} {f₂ : ∀ i, N i → M₂ i → M₂'} (a : ∀ i, M i ≃ₗ[R] M₂ i) (a' : M' ≃+ M₂')
    (hc : ∀ i n x, a' (f i n x) = f₂ i n (a i x)) (ht : Tens R f) : Tens R f₂ := by
  obtain ⟨g, hg⟩ := ht
  let b : (∀ i, N i ⊗[R] M₂ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (a i).symm).toAddEquiv
  refine ⟨(b.trans g).trans a', fun i n x => ?_⟩
  have hb : b (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (a i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [b]
    · simp [b, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply, hb, hg, hc, LinearEquiv.apply_symm_apply]

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem pull_pull_id {D : Type 1} [Category.{0} D] {F : C ⥤ ModuleCat.{0} R} {E : D ⥤ ModuleCat.{0} R}
    (m : CH.Mor F E (RingHom.id R)) (m' : CH.Mor E F (RingHom.id R)) (j : ℕ)
    (h : ∀ f, m'.pullC j (m.pullC j f) = f) (x : CH.H F j) : m'.pull j (m.pull j x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

abbrev inn (U P : ObjectProperty C) : ObjectProperty U.FullSubcategory := fun T => P T.obj

abbrev toDirect (U P : ObjectProperty C) : (inn U P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((inn U P).ι ⋙ U.ι) fun T => T.property

abbrev ofDirect {U P : ObjectProperty C} (h : P ≤ U) : P.FullSubcategory ⥤ (inn U P).FullSubcategory :=
  (inn U P).lift (U.lift P.ι fun T => h _ T.property) fun T => T.property

def dirMor (F : C ⥤ ModuleCat.{0} R) (U P : ObjectProperty C) :
    CH.Mor (P.ι ⋙ F) ((inn U P).ι ⋙ U.ι ⋙ F) (RingHom.id R) where
  G := toDirect U P
  τ _ := LinearMap.id
  nat _ _ := rfl

def itMor (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) :
    CH.Mor ((inn U P).ι ⋙ U.ι ⋙ F) (P.ι ⋙ F) (RingHom.id R) where
  G := ofDirect h
  τ _ := LinearMap.id
  nat _ _ := rfl

def isoH (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) (j : ℕ) :
    HU F P j ≃ₗ[R] HU (U.ι ⋙ F) (inn U P) j :=
  LinearEquiv.ofLinear ((dirMor F U P).pull j) ((itMor F h).pull j)
    (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl)) (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl))

theorem isoH_morU {R' : Type} [CommRing R'] {σ : R →+* R'} {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} (m : CH.Mor F F' σ) {U P : ObjectProperty C}
    {U' P' : ObjectProperty C'} (hU : ∀ T, U' T → U (m.G.obj T)) (hP : ∀ T, P' T → P (m.G.obj T))
    (h : P ≤ U) (h' : P' ≤ U') (j : ℕ) (x : HU F P j) :
    isoH F' h' j ((morU m hP).pull j x) =
      (morU (morU m hU) (U := inn U P) (U' := inn U' P') fun T hT => hP _ hT).pull j (isoH F h j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem base_change_rel : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (W : A → ObjectProperty C) (W' : A → ObjectProperty C')
    (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T')
    (hW' : ∀ α ⦃T T' : C'⦄, (T ⟶ T') → W' α T → (∃ β, W' β T') → W' α T') (h : ∀ α T, W' α T → W α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS W S) j) (M' := HU F' (capS W' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS W S) (U' := capS W' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => HU (F i) (fun T => ∃ α, W α T) j) (M' := HU F' (fun T => ∃ α, W' α T) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := fun T => ∃ α, W α T) (U' := fun T => ∃ α, W' α T)
        fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ W W' hW hW' h hyp j
  let U : ObjectProperty C := fun T => ∃ α, W α T
  let U' : ObjectProperty C' := fun T => ∃ α, W' α T
  have hUU : ∀ T, U' T → U (G.obj T) := fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩
  let G₁ : U'.FullSubcategory ⥤ U.FullSubcategory := U.lift (U'.ι ⋙ G) fun T => hUU _ T.property
  refine GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (C := U.FullSubcategory) (C' := U'.FullSubcategory) G₁ N
    (fun i => U.ι ⋙ F i) (U'.ι ⋙ F') (fun i n T => τ i n T.obj) (fun i n _ _ φ x => hτ i n φ.hom x)
    (fun i n n' T x => hadd i n n' T.obj x) (fun i r n T x => hsm i r n T.obj x)
    (fun α T => W α T.obj) (fun α T => W' α T.obj)
    (fun α _ T' φ hT => hW α φ.hom hT T'.property) (fun α _ T' φ hT => hW' α φ.hom hT T'.property)
    (fun T => T.property) (fun T => T.property) (fun α T hT => h α T.obj hT) ?_ j
  intro S hS j
  obtain ⟨α₀, hα₀⟩ := hS
  have hP : capS W S ≤ U := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  have hP' : capS W' S ≤ U' := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  refine tens_transfer (fun i => isoH (F i) hP j) (isoH F' hP' j).toAddEquiv (fun i n x => ?_) (hyp S ⟨α₀, hα₀⟩ j)
  exact isoH_morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hUU (fun T hT α hα => h α T (hT α hα)) hP hP' j x

end GlobalTheory.CompanionTheory.CosieveRel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFiniteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first | exact @GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | exact GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | (intros; apply GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS <;> assumption)
end

