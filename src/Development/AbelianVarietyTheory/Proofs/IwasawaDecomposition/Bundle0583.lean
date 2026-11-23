module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincipalHartogs

theorem mem_span_singleton_of_forall_height_le_one {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [IsNoetherianRing B] (f s : B)
    (h : ∀ q : Ideal B, q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * s ∈ Ideal.span {f}) :
    s ∈ Ideal.span {f} := by
  by_cases hf : f = 0
  · subst hf
    obtain ⟨u, hu, hus⟩ := h ⊥ Ideal.isPrime_bot (by simp)
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hus ⊢
    rcases mul_eq_zero.mp hus with h0 | h0
    · exact absurd (h0 ▸ Submodule.zero_mem ⊥) hu
    · exact h0
  let K := FractionRing B
  have hfK : algebraMap B K f ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hf
  let d : Ideal B := (Ideal.span {f}).colon {s}
  have hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f} := fun a => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul]
  by_cases hd1 : d = ⊤
  · simpa using (hd 1).1 (hd1 ▸ Submodule.mem_top)
  exfalso
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.exists_le_maximal d hd1
  have hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c →
      a ∈ d := fun a c e => by
    rw [hd, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul] at e
    rw [mul_comm f c]
    exact IsFractionRing.injective B K e
  obtain ⟨p, hp, -, h1, hpf⟩ := NormalPole.exists_height_one (K := K)
    (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))
  obtain ⟨u, hu, hus⟩ := h p hp h1.le
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hus
  refine hu (hpf u c ?_)
  rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]

end GlobalTheory.PrincipalHartogs

namespace GlobalTheory.PrincipalHartogs

end GlobalTheory.PrincipalHartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerGrowth

theorem differentiableOn_matrix_det_of_entries_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableOn ℂ (fun b => ∏ i ∈ t, A b (σ i) i) B := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableOn_matrix_inv_apply_of_entries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin d) :
    DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) B := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det_of_entries_normedSpace hA).inv hd).mul (differentiableOn_matrix_det_of_entries_normedSpace fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA _ _

theorem lam_polyGrowth_of_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r lam M W hd hs hW hb
  by_cases hne : (logDom n a).Nonempty
  swap
  · exact ⟨0, 0, fun s hs' => absurd ⟨s, hs'⟩ hne⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hli0, hsp0, Hm0, hH0, hP0, hM0⟩ := hs s0 hs0
  obtain ⟨hMa, hMd, hr⟩ := _root_.GlobalTheory.hermForm_periods_alternating_nondeg g r (lam s0) M Hm0 hli0 hsp0 hH0 hP0 hM0
  obtain ⟨d, e, f, heW, hee, hfe, hsp⟩ := _root_.GlobalTheory.exists_lagrangian_dual_in_coisotropic r M W hMa hMd hW
  obtain ⟨hli, hrd⟩ := _root_.GlobalTheory.familyIsotropicDual_linearIndependent_and_card r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ℂ) → Fin d → Fin d → ℂ, E = fun s i => ∑ m, (e i m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℂ) → Fin d → Fin d → ℂ, F = fun s j => ∑ m, (f j m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Em = fun s => Matrix.of fun k i => E s i k :=
    ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Fm = fun s => Matrix.of fun k j => F s j k :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin n → ℂ) → Fin d → Fin d → ℂ, τ = fun s i j => ((Em s)⁻¹ * Fm s) i j := ⟨_, rfl⟩
  have hlinE : LinearIndependent ℝ e := hli.comp Sum.inl Sum.inl_injective

  have hpt : ∀ s ∈ logDom n a, (Em s).det ≠ 0 ∧ (∀ j, F s j = ∑ i, τ s i j • E s i) ∧
      (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) ∧
      ∀ i j, τ s i j - τ s j i = ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ) := by
    intro s hs'
    obtain ⟨hli1, -, Hm, hH, hP, hMs⟩ := hs s hs'
    have h6 := GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct d r (lam s) M Hm hMs
    have hEE : ∀ i j, (hermForm Hm (E s i) (E s j)).im = 0 := fun i j => by
      rw [hE]; exact (h6 _ _).trans (hee i j)
    have hFE : ∀ i j, (hermForm Hm (F s i) (E s j)).im = if i = j then 1 else 0 := fun i j => by
      rw [hE, hF]; exact (h6 _ _).trans (hfe i j)
    have hFF : ∀ i j, (hermForm Hm (F s i) (F s j)).im = f i ⬝ᵥ M *ᵥ f j := fun i j => by
      rw [hF]; exact h6 _ _
    have hEli : LinearIndependent ℝ (E s) := by
      rw [hE]; exact GlobalTheory.T.linearIndependent_real_combinations_of_independent d r d (lam s) e hli1 hlinE
    have hdet : (Em s).det ≠ 0 := by rw [hEm]; exact _root_.GlobalTheory.det_ne_zero_of_real_indep_isotropic d Hm (E s) hP hEli hEE
    have hFt : ∀ j, F s j = ∑ i, τ s i j • E s i := by
      intro j
      have hm := Matrix.mul_nonsing_inv_cancel_left (Em s) (Fm s) (Ne.isUnit hdet)
      funext k
      have := congrFun (congrFun hm k) j
      have hEmk : ∀ k i, Em s k i = E s i k := fun k i => by simp [hEm]
      have hFmk : ∀ k i, Fm s k i = F s i k := fun k i => by simp [hFm]
      rw [Matrix.mul_apply] at this
      simp only [hEmk, hFmk] at this
      rw [hτ]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    obtain ⟨h4a, h4b⟩ := _root_.GlobalTheory.riemann_relations_period_matrix d d Hm (E s) (F s) (τ s) hH hP hFt hEE hFE
    exact ⟨hdet, hFt, h4a, fun i j => (h4b i j).trans (by rw [hFF])⟩

  have hlam : ∀ m k, DifferentiableOn ℂ (fun s => lam s m k) (logDom n a) := fun m k =>
    differentiableOn_pi.1 (differentiableOn_pi.1 hd m) k
  have hEmd : ∀ k i, DifferentiableOn ℂ (fun s => Em s k i) (logDom n a) := fun k i => by
    simp only [hEm, hE, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hFmd : ∀ k i, DifferentiableOn ℂ (fun s => Fm s k i) (logDom n a) := fun k i => by
    simp only [hFm, hF, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hτd : DifferentiableOn ℂ τ (logDom n a) := by
    refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
    simp only [hτ, Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (differentiableOn_matrix_inv_apply_of_entries hEmd (fun s hs' => (hpt s hs').1) i l).mul (hFmd l j)
  obtain ⟨C, k, hC⟩ := _root_.GlobalTheory.period_matrix_polynomial_growth n a d τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun s hs' => (hpt s hs').2.2.1)
    (fun s hs' => (hpt s hs').2.2.2)
  set R : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ ‖logExp a s‖ ≤ 1 / 2 ∧
    ∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi} with hR
  have hEb : ∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hb (e i) (heW i)
    exact ⟨C, fun s hs' => by rw [hE]; exact hC s hs'.1 hs'.2.1⟩
  have h9 := _root_.GlobalTheory.matrix_mul_bounded_poly_growth n d d R τ E ⟨C, k, fun s hs' => hC s hs'.1 hs'.2.1 hs'.2.2⟩ hEb
  obtain ⟨C', k', h8⟩ := _root_.GlobalTheory.growth_bound_of_spanning_combinations n d r (Fin d ⊕ Fin d) R lam (Sum.elim e f) hsp (fun i => by
    rcases i with i | j
    · obtain ⟨C, hC⟩ := hEb i
      exact ⟨C, 0, fun s hs' => by simpa [hE] using hC s hs'⟩
    · obtain ⟨C, k, hC⟩ := h9 j
      refine ⟨C, k, fun s hs' => ?_⟩
      have := (hpt s hs'.1).2.1 j
      simp only [hF] at this
      simp only [Sum.elim_inr]
      rw [this]
      exact hC s hs')
  exact ⟨C', k', fun s hs' h1 h2 => h8 s ⟨hs', h1, h2⟩⟩

end GlobalTheory.ShFam.Hor.LogCh.PerGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.unif_sq_polarised_iso | exact GlobalTheory.unif_sq_polarised_iso | (intros; apply GlobalTheory.unif_sq_polarised_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

section Pt

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pull_one_eq_zero (L : RigLB G) {T : Over S} :
    pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
  rw [cls_pull L.isLB] at a
  rw [Hom.one_def, Over.comp_left, pull_comp]
  change pull _ (pull (eSec G) _) = 0
  rw [a, map_zero]

theorem pull_inv (L : RigLB G) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (hs : s.IsGen) {T : Over S} (x : T ⟶ G) :
    pull x⁻¹.left (cls L.L L.isLB) = pull x.left (cls L.L L.isLB) := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨s, hs⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_smul, neg_smul] at e
  have e' : pull (ι[G]).left (cls L.L L.isLB) = cls L.L L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact e
  rw [Hom.inv_def, Over.comp_left, pull_comp, e']

theorem lam_self [IsCommMonObj G] (L : RigLB G) (hΘ : ∃ t : LB.Gen (Theta G L.L), t.IsGen)
    (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    {T : Over S} (x : T ⟶ G) :
    lam (cls L.L L.isLB) x x = 2 • pull x.left (cls L.L L.isLB) := by
  have h := lam_mul_left L.isLB hΘ x⁻¹ x x
  rw [inv_mul_cancel, lam_one_left] at h
  have h2 : lam (cls L.L L.isLB) x⁻¹ x = - pull x⁻¹.left (cls L.L L.isLB) - pull x.left (cls L.L L.isLB) := by
    simp only [lam, inv_mul_cancel, pull_one_eq_zero]; abel
  calc lam (cls L.L L.isLB) x x
      = (lam (cls L.L L.isLB) x⁻¹ x + lam (cls L.L L.isLB) x x) - lam (cls L.L L.isLB) x⁻¹ x := by abel
    _ = 2 • pull x.left (cls L.L L.isLB) := by rw [← h, h2, pull_inv L s hs]; abel

theorem lam_pull_fst {S' : Scheme.{0}} (f : S' ⟶ S) (c : Pic G.left) {T : Over S'}
    (x y : T ⟶ (Over.pullback f).obj G) :
    lam (CechPic.pull (pullback.fst G.hom f) c) x y =
      lam c (pushPt (isGrpPullback_pullback G f).1.w x) (pushPt (isGrpPullback_pullback G f).1.w y) := by
  have h := isGrpPullback_pullback G f
  have e1 : (x * y).left ≫ pullback.fst G.hom f = (pushPt h.1.w x * pushPt h.1.w y).left :=
    congrArg (fun z => z.left) (map_mul (pushHom h T) x y)
  have e0 : (1 : T ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  simp only [lam, ← pull_comp, e1, e0]
  rfl

end Pt

end GlobalTheory.SquareOfGeneric

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

theorem diag_lam_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (U : Unif (maximalIdeal R) D A G) (L : LB ((Over.pullback (jK R)).obj G).left) (hL : L.IsLB)
    (eL : LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (h : (abelian₂ ((Over.pullback (jK R)).obj G) L).IsLB) :
    CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left
        (cls _ h) = 2 • CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) := by
  have e₁ : cls _ h = lam (cls L hL) (fst _ _) (snd _ _) := cls_cube_two hL _ _ h
  have e₂ : cls L hL = CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) :=
    (cls_eq_iff hL (pull_isLB U.LG.isLB _)).2 eL
  rw [e₁, pull_lam, lift_fst, lift_snd, e₂, lam_pull_fst,
    lam_self U.LG ⟨U.cubG.t, U.cubG.isGen⟩ U.symG U.symG_gen]
  rfl

end GlobalTheory.SquareOfGeneric

open GlobalTheory.CechPic MonoidalCategory CartesianMonoidalCategory MonObj in
theorem GlobalTheory.squares_iso_of_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' L L' hL hL' eL eL' eΛ
  have hΛ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).2 eΛ
  have key := congrArg (CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G))
    (𝟙 ((Over.pullback (jK R)).obj G))).left) hΛ
  have k₁ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D A U L hL eL (LB.isLB_linComb hL _ _)
  have k₂ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D' A' U' L' hL' eL' (LB.isLB_linComb hL' _ _)
  replace key := k₁.symm.trans (key.trans k₂)
  refine _root_.GlobalTheory.lbIso_of_generic_normal_local R hR.1 hR.2.1 G.left G.hom (eSec G) hG.smooth hG.quasiCompact
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ _ (LB.isLB_linComb U'.LG.isLB _ _) (LB.isLB_linComb U.LG.isLB _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _) (pull_isLB (LB.isLB_linComb U.LG.isLB _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb U'.LG.isLB _ _), cls_pull (LB.isLB_linComb U.LG.isLB _ _),
    cls_linComb U'.LG.isLB, cls_linComb U.LG.isLB]
  simp only [Fin.sum_univ_one, pull_id, map_zsmul]
  rw [two_zsmul, two_zsmul, ← two_nsmul, ← two_nsmul]
  exact key.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolExt

section Det

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {N : Scheme.{0}} {p' : N ⟶ Z'.X}
  {p : N ⟶ Z.X} {G : Over N} [GrpObj G] [IsCommMonObj G] {ψ' : G.left ⟶ Z'.t.G.left} {ψ : G.left ⟶ Z.t.G.left}
  (h' : IsGrpPullback G Z'.t.G p' ψ') (h : IsGrpPullback G Z.t.G p ψ) {S S' : Type} [CommRing S] [CommRing S']

def pullBasis (M : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) : Module.Basis (Fin M.n) S (TanM x G) :=
  (lieBasis M (x ≫ p) hx).map (tanEquiv h x).symm

theorem tanPull_pullBasis (M : MChart Z) (φ : S →+* S') {x : Sp S ⟶ N} {x' : Sp S' ⟶ N} (e : spMap φ ≫ x = x')
    (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (hx' : ⊤ ≤ (x' ≫ p) ⁻¹ᵁ M.U) (j : Fin M.n) :
    tanPull φ e (pullBasis h M x hx j) = pullBasis h M x' hx' j := by
  have e' : spMap φ ≫ x ≫ p = x' ≫ p := by rw [← Category.assoc, e]
  apply (tanEquiv h x').injective
  rw [← tanPull_tanEquiv h φ e e']
  simp only [pullBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact tanPull_lieBasis M φ e' hx hx' j

theorem pullBasis_toMatrix (M M₁ : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U)
    (hx₁ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M₁.U) : (pullBasis h M x hx).toMatrix (pullBasis h M₁ x hx₁) =
      (lieBasis M (x ≫ p) hx).toMatrix (lieBasis M₁ (x ≫ p) hx₁) := by
  ext i j
  simp [pullBasis, Module.Basis.toMatrix_apply]

def twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    Γ(N, p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)ˣ :=
  (isUnit_rdet_toMatrix (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl)))
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl)))).unit

theorem ev_twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) (x : Sp S ⟶ N)
    (h₀ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (h₁ : ⊤ ≤ (x ≫ p') ⁻¹ᵁ M'.U) (hh : ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    ev x _ hh (twoDet h' h M M' ha).val = rdet ((pullBasis h M x h₀).toMatrix (pullBasis h' M' x h₁)) := by
  have e : spMap (ev x _ hh) ≫ tau ha = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  have h1 := (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl))).sum_toMatrix_smul_self
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := G) _ e) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, tanPull_pullBasis h' M' _ e _ h₁] at h2
  simp only [map_smulₛₗ, tanPull_pullBasis h M _ e _ h₀] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl


include h' h in
theorem lbIso_detLie_pull (ha : ∀ (U : Z.X.Opens) (U' : Z'.X.Opens), IsAffineOpen U → IsAffineOpen U' →
    IsAffineOpen (p ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ U')) : LBIso ((detLie Z').pull p') ((detLie Z).pull p) := by
  have le : ∀ J : ((detLie Z).pull p).ι, ((detLie Z).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  have le' : ∀ J : ((detLie Z').pull p').ι, ((detLie Z').pull p').U J ≤ p' ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z') (fun _ : PUnit => p') J PUnit.unit
  refine ⟨⟨fun a => res (inf_le_inf (le a.1) (le' a.2))
    (twoDet h' h (a.1 PUnit.unit) (a.2 PUnit.unit) (ha _ _ (MChart.hU _) (MChart.hU _)))⟩, fun a b => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U a.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U b.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U a.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U b.2 := le_preimage_mono inf_le_right hq
  have hp0 := le_preimage_map p (le a.1) hp1
  have hq0 := le_preimage_map p (le b.1) hq1
  have hp3 := le_preimage_map p' (le' a.2) hp2
  have hq3 := le_preimage_map p' (le' b.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf (le a.1) (le' a.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf (le b.1) (le' b.2)) hq
  have g := ev_pull_g (detLie Z) p z a.1 b.1 (le_preimage_inf hp1 hq1) (le_preimage_inf hp0 hq0)
  have g' := ev_pull_g (detLie Z') p' z a.2 b.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans
    (ev_twoDet h' h _ _ _ z hp0 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g'.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp0 hq0 _)))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_twoDet h' h _ _ _ z hq0 hq3 hq4)))).symm)
  exact (congrArg (_ * rdet ·) (pullBasis_toMatrix h' _ _ z hp3 hq3).symm).trans ((rdet_toMatrix_mul _ _ _).trans
    ((congrArg (rdet · * _) (pullBasis_toMatrix h _ _ z hp0 hq0).symm).trans (rdet_toMatrix_mul _ _ _)).symm)

end Det

theorem isAffineOpen_snd_inf_fst {X Y T : Scheme.{0}} [IsAffine T] (f : X ⟶ T) (g : Y ⟶ T) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U) := by
  let m : pullback (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  have e : m.opensRange = pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec, Set.inter_comm]
    rfl
  exact e ▸ isAffineOpen_opensRange m

end GlobalTheory.PolExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesFourthPowerAssociatedStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_coordinates_fourthPower_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.psi_coord_fourth_associated | exact GlobalTheory.psi_coord_fourth_associated | (intros; apply GlobalTheory.psi_coord_fourth_associated <;> assumption)
end

