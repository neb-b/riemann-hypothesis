module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedMatrixGroupImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfExpLocal
section
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LinRedLie

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  one_mem' := hG.one_mem
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  inv_mem' := fun {u} hu => by
    have h := hG.inv_mem _ hu
    rw [← Matrix.coe_units_inv] at h
    exact h

theorem isClosed_unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) :
    IsClosed (unitsOf hG : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  refine isClosed_of_closure_subset fun u hu => ?_
  refine hG.closed _ u.isUnit ?_
  exact closure_mono (fun v hv => hv) (map_mem_closure Units.continuous_val hu (fun v hv => hv))


open scoped Matrix.Norms.L2Operator in
theorem exists_subspace (hG : GlobalTheory.LinRed.IsLinRed G) :
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ 𝔤, NormedSpace.exp X ∈ G) ∧
      ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
        ∀ X ∈ U, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  obtain ⟨𝔤, h⟩ := GlobalTheory.CompanionTheory.ClosedSubgroupUnits.exists_isExpLieAlgebra (unitsOf hG) (isClosed_unitsOf hG)
  obtain ⟨U, hUo, h0, -, hU⟩ := h.exists_nhds
  exact ⟨𝔤, fun X hX => h.expUnit_mem X hX, U, hUo, h0, fun X hXU hX => hU X hXU hX⟩

theorem exists_lieAlgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
      ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  intro n G hG
  obtain ⟨𝔤, hexp, U, hUo, h0, hU⟩ := exists_subspace hG
  refine ⟨𝔤, fun X => ⟨fun hX t => hexp _ (𝔤.smul_mem t hX), fun hX => ?_⟩,
    U, hUo.mem_nhds h0, hU⟩
  have hc : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hev : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ U :=
    hc.continuousAt.eventually_mem (by simpa using hUo.mem_nhds h0)
  obtain ⟨t, htU, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, t • X ∈ U ∧ t ∈ ({0}ᶜ : Set ℝ)).exists
  exact (𝔤.smul_mem_iff ht).1 (hU _ htU (hX t))

end GlobalTheory.CompanionTheory.LinRedLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieGeneratorsGlRelations
section
noncomputable section

open Matrix
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GLK.Pair

section Ring

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem brk_ee (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r - Complex.I • s))
      - ((1 / 2 : ℂ) • (r - Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q))
      = (1 / 2 : ℂ) • (P - Complex.I • Q) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  linear_combination (norm := skip) (-(Complex.I / 4)) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ff (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p + Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      - ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p + Complex.I • q))
      = (1 / 2 : ℂ) • (P + Complex.I • Q) := by
  subst h1 h2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ef (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      = ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q)) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

end Ring

section Main

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z - Complex.I • D (Complex.I • Z))

def fP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z + Complex.I • D (Complex.I • Z))

theorem first_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : e1 D a b = eP D (Matrix.single a b 1) := by
  simp [e1, eP, Matrix.smul_single]

theorem second_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : f1 D a b = fP D (Matrix.single a b 1) := by
  simp [f1, fP, Matrix.smul_single]

variable {D : Mat n → Module.End ℂ V}

theorem D_neg (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) : D (-X) = -D X := by
  simpa using hs (-1) X

theorem D_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : D (0 : Mat n) = 0 := by
  simpa using hs 0 0

theorem D_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : D (X - Y) = D X - D Y := by
  rw [sub_eq_add_neg, ha, D_neg hs, sub_eq_add_neg]

theorem eP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : eP D (0 : Mat n) = 0 := by
  simp [eP, D_zero hs]

theorem fP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : fP D (0 : Mat n) = 0 := by
  simp [fP, D_zero hs]

theorem eP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : eP D (X - Y) = eP D X - eP D Y := by
  simp only [eP, smul_sub, D_sub ha hs]
  abel

theorem fP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : fP D (X - Y) = fP D X - fP D Y := by
  simp only [fP, smul_sub, smul_add, D_sub ha hs]
  abel

theorem brk_four (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    D Z * D W - D W * D Z = D (Z * W - W * Z) ∧
    D (Complex.I • Z) * D W - D W * D (Complex.I • Z) = D (Complex.I • (Z * W - W * Z)) ∧
    D Z * D (Complex.I • W) - D (Complex.I • W) * D Z = D (Complex.I • (Z * W - W * Z)) ∧
    D (Complex.I • Z) * D (Complex.I • W) - D (Complex.I • W) * D (Complex.I • Z) = -D (Z * W - W * Z) := by
  refine ⟨(hb Z W).symm, ?_, ?_, ?_⟩
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb, ← D_neg hs]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel

theorem eP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * eP D W - eP D W * eP D Z = eP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ee _ _ _ _ _ _ h1 h2 h3 h4

theorem fP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    fP D Z * fP D W - fP D W * fP D Z = fP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ff _ _ _ _ _ _ h1 h2 h3 h4

theorem eP_fP_comm (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * fP D W = fP D W * eP D Z := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ef _ _ _ _ _ _ h1 h2 h3 h4

theorem single_brk (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 - Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have h : ∀ a b c d : Fin n, (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))
  rw [h, h]

theorem eP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    e1 D a b * e1 D c d - e1 D c d * e1 D a b =
      (if b = c then e1 D a d else 0) - (if d = a then e1 D c b else 0) := by
  simp only [first_generator_eq_single]
  rw [eP_brk hs hb, single_brk, eP_sub ha hs]
  split_ifs <;> simp [eP_zero hs]

theorem fP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    f1 D a b * f1 D c d - f1 D c d * f1 D a b =
      (if b = c then f1 D a d else 0) - (if d = a then f1 D c b else 0) := by
  simp only [second_generator_eq_single]
  rw [fP_brk hs hb, single_brk, fP_sub ha hs]
  split_ifs <;> simp [fP_zero hs]

end Main

theorem gl_pair : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V),
    (∀ X Y, D (X + Y) = D X + D Y) → (∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) →
    (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) →
    Formalism.REAL.GlRel (e1 D) ∧ Formalism.REAL.GlRel (e2 D) ∧ ∀ a b c d, e1 D a b * e2 D c d = e2 D c d * e1 D a b := by
  intro n V _ _ D ha hs hb
  refine ⟨fun a b c d => eP_units ha hs hb a b c d, fun a b c d => ?_, fun a b c d => ?_⟩
  · have h := fP_units ha hs hb b a d c
    simp only [e2, neg_mul_neg]
    rw [h]
    simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
    split_ifs <;> simp <;> abel
  · simp only [e2, mul_neg, neg_mul, first_generator_eq_single, second_generator_eq_single]
    rw [eP_fP_comm hs hb]

end GlobalTheory.CompanionTheory.GLK.Pair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientHeckeDecay
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CoeffBound

theorem exists_radius {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (b : ℝ) (hb0 : 0 < b)
    (hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < b ∧ ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < ρ := by
  classical
  have hfin : Set.Finite {μ : ℂ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  let s : Finset ℝ := insert 0 (hfin.toFinset.image fun μ => ‖μ‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hM : s.max' hs < b := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hb0
    · obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hy
      exact hb μ (hfin.mem_toFinset.1 hμ)
  have h0 : 0 ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨(s.max' hs + b) / 2, by linarith, by linarith, fun μ hμ => ?_⟩
  have h1 : ‖μ‖ ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hμ)))
  linarith

theorem exists_coordinates (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    ∃ (d : ℕ) (e : W ≃ₗ[ℂ] (Fin d → ℂ))
      (φ : Module.End ℂ W →ₐ[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))),
      (∀ (S : Module.End ℂ W) (x : W), φ S (e x) = e (S x)) ∧
      ∀ (S : Module.End ℂ W) (μ : ℂ),
        Module.End.HasEigenvalue ((φ S : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ)) μ →
          S.HasEigenvalue μ := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  let φ : Module.End ℂ W →ₐ[ℂ] ((Fin (Module.finrank ℂ W) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Fin (Module.finrank ℂ W) → ℂ)).toAlgHom.comp
      (e.conjAlgEquiv ℂ).toAlgHom
  have hφ : ∀ (S : Module.End ℂ W) (x : Fin (Module.finrank ℂ W) → ℂ), φ S x = e (S (e.symm x)) := by
    intro S x
    simp [φ, LinearEquiv.conjAlgEquiv_apply]
    rfl
  refine ⟨_, e, φ, fun S x => by rw [hφ]; simp, fun S μ h => ?_⟩
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hx1 : φ S x = μ • x := Module.End.mem_eigenspace_iff.1 hx.1
  rw [hφ] at hx1
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm x)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h0 => hx.2 (by simpa using h0)⟩
  apply e.injective
  rw [hx1]
  simp

theorem diagPow_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) : Zls.diagPow k N 0 = 1 := by
  refine Units.ext ?_
  ext i j
  simp [Zls.diagPow, Matrix.one_apply, Matrix.diagonal_apply]

theorem lamOf_zero (N : ℕ) : Zls.lamOf (0 : Fin (N - 1) → ℕ) = 0 := by
  funext i
  simp [Zls.lamOf]

theorem hecke_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hsm : IsSmooth π) {m : ℕ} (hm : 1 ≤ m)
    (j : Fin (N - 1)) (T : Module.End ℂ (fixed π (Zls.Km k N m)))
    (hT : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1))) T) (n : ℕ) :
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf (Pi.single j n : Fin (N - 1) → ℕ))) (T ^ n) := by
  induction n with
  | zero =>
    rw [Pi.single_zero, lamOf_zero, diagPow_zero, pow_zero]
    intro v l _
    simp
  | succ n ih =>
    have hs : (Pi.single j (n + 1) : Fin (N - 1) → ℕ) = Pi.single j n + Pi.single j 1 := by
      rw [← Pi.single_add]
    rw [hs, ((GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1 _ _), pow_succ]
    refine GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _ ih ?_
    rw [(GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).2 j]
    exact hT

theorem radius_sq_lt {q ρ : ℝ} (hq : 0 < q) (a : ℕ) (h0 : 0 ≤ ρ)
    (h : ρ < q ^ (-((a : ℝ) / 2))) : q ^ a * ρ ^ 2 < 1 := by
  have h1 : ρ ^ 2 < (q ^ (-((a : ℝ) / 2))) ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  have h2 : (q ^ (-((a : ℝ) / 2))) ^ 2 = (q ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q a, ← Real.rpow_neg hq.le]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  have h3 : 0 < q ^ a := pow_pos hq a
  calc q ^ a * ρ ^ 2 < q ^ a * (q ^ a)⁻¹ := mul_lt_mul_of_pos_left h1 h3
    _ = 1 := mul_inv_cancel₀ h3.ne'

theorem coeff_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → Zls.HeckeSpectral π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hrad := fun j : Fin (N - 1) => exists_radius (T j) _ (Real.rpow_pos_of_pos hq
      (-(((((((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) : ℕ) : ℝ)) / 2)))
    (fun μ hμ => hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ)
  choose ρ hρ0 hρb hρe using hrad
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact radius_sq_lt hq _ (hρ0 j) (hρb j)
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

end GlobalTheory.CompanionTheory.CoeffBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      GlobalTheory.BZMir.eLast k n j :=
    fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
  have hblock : ∀ i j : Fin n,
      ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
        (1 : Matrix (Fin n) (Fin n) k) i j :=
    fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hy
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
  apply Units.ext
  ext i j
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
  rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
      GlobalTheory.BZMir.eLast]
  · simp [hrow, GlobalTheory.BZMir.eLast]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalarStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_central_block_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  first | exact @GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | exact GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | (intros; apply GlobalTheory.CompanionTheory.JCScalar.piTensor_zj <;> assumption)
end

