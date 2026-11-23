module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimitStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry_real (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => (NormedSpace.exp (t • X)) i j := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h2

theorem coord_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) (k : KG ε) : coord ε c (k * expK ε X 0) = coord ε c k := by
  simp [coord, toMK_mul, toMK_expK hX, NormedSpace.exp_zero]

theorem mono_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) (k : KG ε) : mono ε s (k * expK ε X 0) = mono ε s k := by
  simp only [mono, coord_mul_expK_zero hX]

theorem hasDerivAt_coord {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) : ∃ ψ ∈ polyV ε 1, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε X t)) (ψ k) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ k : KG ε, HasDerivAt (fun t : ℝ => (toMK (k * expK ε X t)) a b)
      (∑ l, toMK k a l * X l b) 0 := by
    intro k
    have e : (fun t : ℝ => (toMK (k * expK ε X t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • X)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hX, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real X l b).const_mul _
  cases f
  · refine ⟨∑ l, star (X l b) • coord ε (a, l, false), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have h := (hent k).star
      have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε X t)) =
          fun t => star ((toMK (k * expK ε X t)) a b) := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, star (X l b) • coord ε (a, l, false)) k = star (∑ l, toMK k a l * X l b) := by
        rw [Finset.sum_apply, star_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, Bool.false_eq_true, if_false, star_mul']
        exact mul_comm _ _
      rw [hv]; exact h
  · refine ⟨∑ l, X l b • coord ε (a, l, true), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε X t)) =
          fun t => (toMK (k * expK ε X t)) a b := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, X l b • coord ε (a, l, true)) k = ∑ l, toMK k a l * X l b := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, if_true]
        exact mul_comm _ _
      rw [hv]; exact hent k

theorem hasDerivAt_mono {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) : ∀ d, s.length ≤ d → ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε X t)) (ψ k) 0 := by
  induction s with
  | nil =>
    intro d _
    refine ⟨0, Submodule.zero_mem _, fun k => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    intro d hd
    simp only [List.length_cons] at hd
    obtain ⟨ψc, hψc, hc⟩ := hasDerivAt_coord hX c
    obtain ⟨ψs, hψs, hs⟩ := ih (d - 1) (by omega)
    refine ⟨ψc * mono ε s + coord ε c * ψs, ?_, fun k => ?_⟩
    · have hle : 1 + (d - 1) ≤ d := by omega
      exact add_mem (polyV_mono ε hle (mul_mem hψc (mono_mem (by omega))))
        (polyV_mono ε hle (mul_mem (coord_mem ε c) hψs))
    · have h := (hc k).mul (hs k)
      have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε X t)) =
          fun t => coord ε c (k * expK ε X t) * mono ε s (k * expK ε X t) := by
        funext t; simp [mono]
      rw [e]
      rw [coord_mul_expK_zero hX, mono_mul_expK_zero hX] at h
      exact h

theorem hasDerivAt_of_mem {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (ψ k) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hasDerivAt_mono hX s d hs
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ₁, h₁, d₁⟩ := hx
    obtain ⟨ψ₂, h₂, d₂⟩ := hy
    exact ⟨ψ₁ + ψ₂, add_mem h₁ h₂, fun k => (d₁ k).add (d₂ k)⟩
  | smul a x _ hx =>
    obtain ⟨ψ, h, dψ⟩ := hx
    exact ⟨a • ψ, Submodule.smul_mem _ a h, fun k => by simpa using (dψ k).const_mul a⟩

theorem rder_mem_and_hasDerivAt (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    (X : Mx n) (hX : inK ε X) : rder ε [X] φ ∈ polyV ε d ∧
      ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (rder ε [X] φ k) 0 := by
  obtain ⟨ψ, hψ, hd⟩ := hasDerivAt_of_mem hX hφ
  have e : rder ε [X] φ = ψ := by
    funext k
    rw [rder_cons, rder_nil]
    exact (hd k).deriv
  rw [e]
  exact ⟨hψ, hd⟩

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqMatrixCoeffOfLocallyUniformLimitKFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.eq_coef_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ h : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn h (UJset ε) → GlobalTheory.TypeSum.UMG ε h →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε → ‖h y - ∑ a, L a (σ y (w a))‖ < δ) →
    ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
      ∀ y ∈ UJset ε, h y = ∑ a, L a (σ y (w a)) := by
  intro hHC hCW n ε H _ _ _ σ hstd d w hw h hcont humg happ
  obtain ⟨N, Φ, hΦ0, hΦD, hΦG⟩ := humg
  have hCh : CSm ε h := ⟨Φ, hΦ0, hΦD, _root_.GlobalTheory.TypeSum.DerFamCont.continuousOn_of_isDerFam n ε N Φ hΦD hΦG⟩
  set h0 : Mx n → ℂ := (UJset ε).indicator h with hh0def
  have hh0 : ∀ g ∈ UJset ε, h g = h0 g := fun g hg => (Set.indicator_of_mem hg h).symm
  have hm0 : h0 ∈ Smo ε := ⟨fun g hg => Set.indicator_of_notMem hg h, hCh.congr hh0⟩
  have hwS : ∀ a, Sm ε σ (w a) := fun a => hstd.2.2.1 _ (hw a)
  have hrel : ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε) = 0 := by
    intro m c u hcu
    have hA := GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit n ε h hCh m c u (fun C hC δ hδ => by
      obtain ⟨L, hL, hLa⟩ := happ C hC δ hδ
      obtain ⟨hB1, hB2⟩ := _root_.GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF n ε H σ hstd d L hL w hwS
      refine ⟨_, hB1, hLa, fun y hy => ?_⟩
      simp only [fun i => hB2 (u i) y hy]
      rw [← Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin d))) (f := fun a => L a (σ y (∑ i, c i • wordV σ (u i) (w a))))
        (fun a _ => by rw [hcu a, map_zero, map_zero])]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm)
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_wordE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Submodule.coe_zero, Pi.zero_apply]
    by_cases hg : g ∈ UJset ε
    · rw [← hA g hg]
      exact Finset.sum_congr rfl fun i _ => by rw [wordF_congr hh0 (u i) g hg]
    · refine Finset.sum_eq_zero fun i _ => ?_
      have := (wordE ltrM (u i) (⟨h0, hm0⟩ : Smo ε)).2.1 g hg
      rw [coe_wordE] at this
      rw [this, mul_zero]
  obtain ⟨T, hT1, hT2, hT3⟩ := _root_.GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations hHC n ε H σ hstd d w hw (Smo ε) ltrM ⟨h0, hm0⟩ hrel
  have hD : ∀ a, ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε,
      ((Smo ε).subtype ∘ₗ T a) v y = L (σ y v) := by
    intro a
    refine _root_.GlobalTheory.TypeSum.GrowthForm.exists_form hCW n ε H σ hstd N ((Smo ε).subtype ∘ₗ T a) (fun v hv => ?_) (fun v hv k hk g hg => ?_)
      (fun v hv X hX g hg => ?_)
    · obtain ⟨m, c, u, e⟩ := hT3 a v hv
      have hb := fun i => _root_.GlobalTheory.TypeSum.CoefClos.wordF_growth n ε N h Φ hΦ0 hΦD hΦG (u i)
      choose C hC using hb
      refine ⟨∑ i, ‖c i‖ * C i, fun g hg => ?_⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, e, Submodule.coe_sum, Submodule.coe_smul, coe_wordE,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, mul_assoc, ← wordF_congr hh0 (u i) g hg]
      exact mul_le_mul_of_nonneg_left (hC i g hg) (norm_nonneg _)
    · have := hT1 a v hv (Sum.inr ⟨k, hk⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show σ k v = ltrV σ (Sum.inr ⟨k, hk⟩ : Ltr ε) v from rfl, this]
      rfl
    · have := hT1 a v hv (Sum.inl ⟨X, hX⟩)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [show dRep σ X v = ltrV σ (Sum.inl ⟨X, hX⟩ : Ltr ε) v from rfl, this]
      exact (T a v).2.2.hasDerivAt hX hg
  choose L hL1 hL2 using hD
  refine ⟨L, hL1, fun y hy => ?_⟩
  rw [hh0 y hy, show h0 = ((⟨h0, hm0⟩ : Smo ε) : Mx n → ℂ) from rfl, ← hT2, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => hL2 a (w a) (hw a) y hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {f | ∃ d, ⇑f ∈ polyV ε d}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using mul_mem ha hb⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by simpa using add_mem (polyV_mono ε (le_max_left a b) ha) (polyV_mono ε (le_max_right a b) hb)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨0, ?_⟩
    convert const_mem ε 0 c using 1
    funext k; simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert star_mem ha using 1
    funext k; rfl

theorem toMK_injective (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  have h1 : ((a : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((b : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := Units.ext h
  exact Subtype.ext (Subtype.ext h1)

theorem polyAlg_separatesPoints (ε : Fin n → Bool) : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective ε h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  refine ⟨_, ⟨⟨coord ε (i, j, true), continuous_coord ε _⟩, ⟨1, show coord ε (i, j, true) ∈ polyV ε 1 from coord_mem ε _⟩, rfl⟩, ?_⟩
  simpa [coord] using hij

theorem polyAlg_dense (ε : Fin n → Bool) : (polyAlg ε).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_separatesPoints ε)

theorem integrable_cont (ε : Fin n → Bool) (F : C(KG ε, ℂ)) : Integrable F (muK ε) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_integral_cont (ε : Fin n → Bool) :
    Continuous fun F : C(KG ε, ℂ) => ∫ k, F k ∂(muK ε) := by
  refine (LipschitzWith.of_dist_le_mul fun F G => ?_).continuous (K := 1)
  rw [dist_eq_norm, ← integral_sub (integrable_cont ε F) (integrable_cont ε G)]
  have h := norm_integral_le_of_norm_le_const (μ := muK ε) (C := ‖F - G‖)
    (Filter.Eventually.of_forall fun k => by
      simpa using ContinuousMap.norm_coe_le_norm (F - G) k)
  simpa [probReal_univ, dist_eq_norm] using h

theorem eq_zero_of_orth_poly : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  intro n ε h hc horth
  let H : C(KG ε, ℂ) := ⟨h, hc⟩
  let Φ : C(KG ε, ℂ) → ℂ := fun F => ∫ k, star (F k) * h k ∂(muK ε)
  have hΦ : Continuous Φ := by
    have : Continuous fun F : C(KG ε, ℂ) => star F * H := (continuous_star).mul continuous_const
    exact (continuous_integral_cont ε).comp this
  have hclosed : IsClosed {F : C(KG ε, ℂ) | Φ F = 0} := isClosed_eq hΦ continuous_const
  have hsub : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {F | Φ F = 0} := by
    rintro F ⟨d, hd⟩
    exact horth d _ hd
  have hcl : closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) = Set.univ := by
    have := polyAlg_dense ε
    rw [← StarSubalgebra.topologicalClosure_coe, this]
    rfl
  have hH : Φ H = 0 := by
    have : H ∈ closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by rw [hcl]; trivial
    exact hclosed.closure_subset_iff.mpr hsub this

  have hint : ∫ k, (Complex.normSq (h k) : ℂ) ∂(muK ε) = 0 := by
    have e : (fun k => (Complex.normSq (h k) : ℂ)) = fun k => star (h k) * h k := by
      funext k; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [e]; exact hH
  have hint' : ∫ k, Complex.normSq (h k) ∂(muK ε) = 0 := by
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hnn : 0 ≤ᵐ[muK ε] fun k => Complex.normSq (h k) := Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
  have hcn : Continuous fun k => Complex.normSq (h k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint'
  have hz : (fun k => Complex.normSq (h k)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hcn continuous_const).mp hae
  funext k
  have := congrFun hz k
  simpa using this

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KSpan

def kSub {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | inK ε Y}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · unfold inG at *
      rw [conjTranspose_add, add_mul, mul_add]
      calc _ = (aᴴ * Jm ε + Jm ε * a) + (bᴴ * Jm ε + Jm ε * b) := by abel
        _ = 0 := by rw [ha1, hb1, add_zero]
    · rw [add_mul, mul_add, ha2, hb2]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp [inG]
    · simp
  smul_mem' := by
    intro t Z hZ
    have h := inK_smul_real ε hZ t
    rwa [Complex.coe_smul] at h

theorem finite_real_span : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  intro n ε
  let b := Module.finBasis ℝ (kSub ε)
  refine ⟨Module.finrank ℝ (kSub ε), fun j => ((b j : kSub ε) : Matrix (Fin n) (Fin n) ℂ), fun j => (b j).2, ?_⟩
  intro Y hY
  refine ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.coe_smul]

end GlobalTheory.KSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubOrthogonal
section
namespace GlobalTheory.OrthogonalProjectionPoly

open MeasureTheory

theorem exists_sub_orthogonal {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ q ∈ V, Continuous q) (p : X → ℂ) (hp : Continuous p) :
    ∃ p' ∈ V, ∀ q ∈ V, ∫ x, star (q x) * (p x - p' x) ∂μ = 0 := by
  classical
  let j : V →ₗ[ℂ] C(X, ℂ) :=
    { toFun := fun q => ⟨q, hV q q.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : V →ₗ[ℂ] Lp ℂ 2 μ := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap ∘ₗ j
  let W : Submodule ℂ (Lp ℂ 2 μ) := LinearMap.range T
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range T
  let P : C(X, ℂ) := ⟨p, hp⟩
  obtain ⟨p', hp'⟩ := LinearMap.mem_range.1 (W.starProjection_apply_mem (ContinuousMap.toLp 2 μ ℂ P))
  refine ⟨p', p'.2, fun q hq => ?_⟩
  have h0 := W.starProjection_inner_eq_zero (ContinuousMap.toLp 2 μ ℂ P) (T ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
  rw [← hp'] at h0
  have h1 : ContinuousMap.toLp 2 μ ℂ P - T p' = ContinuousMap.toLp 2 μ ℂ (P - j p') := by
    rw [map_sub]
    rfl
  rw [h1] at h0
  have h2 : inner ℂ (ContinuousMap.toLp 2 μ ℂ (P - j p')) (T ⟨q, hq⟩) =
      ∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ :=
    ContinuousMap.inner_toLp μ (P - j p') (j ⟨q, hq⟩)
  rw [h2] at h0
  calc ∫ x, star (q x) * (p x - (p' : X → ℂ) x) ∂μ
      = ∫ x, (starRingEnd ℂ) (q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x)) ∂μ := by
        congr 1
        funext x
        rw [map_mul, Complex.conj_conj, starRingEnd_apply, _root_.mul_comm]
    _ = (starRingEnd ℂ) (∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ) := integral_conj
    _ = 0 := by rw [h0, map_zero]

theorem exists_proj_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : ↥(Formalism.REAL.KG ε) → ℂ), Continuous p →
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ (k : ↥(Formalism.REAL.KG ε)), Star.star (q k) * (p k - p' k) ∂ Formalism.REAL.muK ε = (0 : ℂ) := by
  intro n ε d p hp
  exact exists_sub_orthogonal (Formalism.REAL.muK ε) (GlobalTheory.KFourier.polyV ε d)
    (fun q hq => GlobalTheory.KFourier.continuous_of_mem hq) p hp

end GlobalTheory.OrthogonalProjectionPoly
end

