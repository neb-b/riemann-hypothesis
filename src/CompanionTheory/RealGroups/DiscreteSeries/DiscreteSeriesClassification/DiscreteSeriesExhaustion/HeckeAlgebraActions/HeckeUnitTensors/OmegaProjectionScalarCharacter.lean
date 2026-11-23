module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.RightCasimirMemSubmodule

@[expose] public section

noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}


variable (X χ s) in
def toS (g : (step X (χ s)).V) : ↥(stepSub X (χ s)) := g

variable (X χ s) in
def ofS (g : ↥(stepSub X (χ s))) : (step X (χ s)).V := g

theorem toS_add (g g' : (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (g + g') = toS (X := X) (χ := χ) (s := s) g + toS (X := X) (χ := χ) (s := s) g' := rfl

theorem toS_neg (g : (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (-g) = -toS (X := X) (χ := χ) (s := s) g := rfl

theorem toS_sum (g : Fin (m + 1) → (step X (χ s)).V) : toS (X := X) (χ := χ) (s := s) (∑ c, g c) = ∑ c, toS (X := X) (χ := χ) (s := s) (g c) :=
  map_sum (AddMonoidHom.mk' (toS (X := X) (χ := χ) (s := s)) toS_add) g univ

theorem toS_E (a b : Fin (m + 1)) (g : (step X (χ s)).V) :
    ((toS (X := X) (χ := χ) (s := s) ((step X (χ s)).E a b g) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) =
      tensE X a b (toS (X := X) (χ := χ) (s := s) g : Fin (m + 1) → X.V) := rfl

def coeY (G : Fin (m + 1) → (step X (χ s)).V) : Fin (m + 1) → Fin (m + 1) → X.V :=
  fun c => ((toS (X := X) (χ := χ) (s := s) (G c) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V)

theorem coeY_injective : Function.Injective (coeY (X := X) (χ := χ) (s := s)) := fun G G' h =>
  funext fun c => (Subtype.ext (congrFun h c) : toS (X := X) (χ := χ) (s := s) (G c) = toS (X := X) (χ := χ) (s := s) (G' c))

theorem coeY_smul (r : ℂ) (G) : coeY (X := X) (χ := χ) (s := s) (r • G) = r • coeY G := by
  funext c d; rfl

theorem coeY_sub (G G') : coeY (X := X) (χ := χ) (s := s) (G - G') = coeY G - coeY G' := by
  funext c d; rfl

theorem coe_omD (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (omD (step X (χ s)) G) = y2 (X := X) (coeY G) := by
  funext a
  have h : omD (step X (χ s)) G a = -∑ c, (step X (χ s)).E a c (G c) := by
    simp [omD, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [show y2 (X := X) (coeY G) a = -∑ c, tensE X a c (coeY G c) by simp [y2, LinearMap.pi_apply]]
  change ((toS (X := X) (χ := χ) (s := s) (omD (step X (χ s)) G a) : ↥(stepSub X (χ s))) : Fin (m + 1) → X.V) = _
  rw [h, toS_neg, toS_sum, Submodule.coe_neg, Submodule.coe_sum]
  simp only [toS_E]
  rfl

theorem coe_pow (β : ℂ) (k : ℕ) (G : Fin (m + 1) → (step X (χ s)).V) :
    coeY (((omD (step X (χ s)) - β • 1) ^ k) G) = ((y2 (X := X) - β • 1) ^ k) (coeY G) := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, coeY_sub, coeY_smul, coe_omD]


variable (χ s) in
def phi0 (hS : ScalChar X χ) : X.V →ₗ[ℂ] (Fin (m + 1) → (step X (χ s)).V) where
  toFun v := fun c => ofS X χ s ⟨Pr X χ s (Pi.single c v), Pr_mem hS _⟩
  map_add' v w := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (v + w)), _⟩ =
      ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩ + ofS X χ s ⟨Pr X χ s (Pi.single c w), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (v + w)) = Pr X χ s (Pi.single c v) + Pr X χ s (Pi.single c w)
    rw [Pi.single_add, map_add (f := _)]
  map_smul' r v := by
    funext c
    show ofS X χ s ⟨Pr X χ s (Pi.single c (r • v)), _⟩ = r • ofS X χ s ⟨Pr X χ s (Pi.single c v), _⟩
    apply Subtype.ext
    show Pr X χ s (Pi.single c (r • v)) = r • Pr X χ s (Pi.single c v)
    rw [Pi.single_smul, map_smul]

theorem coe_projection_scalar_character (hS : ScalChar X χ) (v : X.V) : coeY (phi0 (X := X) (χ := χ) (s := s) hS v) = fun c => Pr X χ s (Pi.single c v) := by
  funext c; rfl

theorem omega_projection_scalar_character (hS : ScalChar X χ) (v : X.V) :
    omD (step X (χ s)) (phi0 (X := X) (χ := χ) (s := s) hS v) = (-(χ s + 1) - cn (m + 1)) • phi0 (X := X) (χ := χ) (s := s) hS v := by
  apply coeY_injective
  rw [coe_omD, coeY_smul, coe_projection_scalar_character]
  funext a
  have hy (H : Fin (m + 1) → Fin (m + 1) → X.V) (a : Fin (m + 1)) :
      y2 (X := X) H a = -∑ c, tensE X a c (H c) := by
    simp [y2, LinearMap.pi_apply]
  rw [hy]
  simp_rw [← Pr_tensE (X := X) (χ := χ) (s := s)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, sum_tensE_single, map_add (f := _), map_smul, Pr_om, om_Pr hS, ← add_smul, ← neg_smul, Pi.smul_apply]
  congr 1
  unfold cn; push_cast; ring

theorem tensVd_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) (f : Fin n → M) (d : Fin n) :
    ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd E a b f d = E a b (f d) - if d = b then f a else 0 := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp

theorem tensE_single (a b d : Fin (m + 1)) (v : X.V) :
    tensE X a b (Pi.single d v) = Pi.single d (X.E a b v) + if b = d then Pi.single a v else 0 := by
  funext i
  rw [tensE_apply, Pi.add_apply]
  simp only [Pi.single_apply]
  by_cases hi : i = d <;> by_cases hb : b = d <;> by_cases ha : i = a <;> simp_all

end CompanionTheory.RgExh.Hk.UnitPf
