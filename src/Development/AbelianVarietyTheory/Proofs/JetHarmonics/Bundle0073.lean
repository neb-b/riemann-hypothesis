module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DetLeibniz

open Matrix QnYLeibnizW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_adjugate_mul_eq_sum_cramer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A.adjugate * B).trace = ∑ j, A.cramer (fun i => B i j) j := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem hasDerivAt_det_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g X : Q.Mx k r) :
    HasDerivAt (fun t : ℝ => (Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X))).det)
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X)).trace 0 := by
  have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X)))
    (Zhat k r z z' (g * X)) 0 (fun i j =>
      (hermL (Hpk k r) (fvec k r z' j) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_exp_smul_zero g X))
  simp only [curve_zero] at h
  exact h

theorem Zhat_add_smul (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A B : Q.Mx k r) (c : ℂ) :
    Zhat k r z z' (A + c • B) = Zhat k r z z' A + c • Zhat k r z z' B := by
  ext i j
  simp [Zhat, herm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]

theorem Zhat_mul_single (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r)
    (p q : Fin (2 * r + k + 1)) (j : Fin (r + 1)) :
    (fun i => Zhat k r z z' (g * Matrix.single p q 1) i j) =
      fvec k r z' j q • fun i => herm (Hpk k r) (g *ᵥ bvec p) (fvec k r z i) := by
  have hv : Matrix.single p q (1 : ℂ) *ᵥ fvec k r z' j = fvec k r z' j q • bvec p := by
    rw [Matrix.single_mulVec]
    funext l
    by_cases h : l = p
    · subst h; simp [bvec]
    · simp [bvec, h]
  funext i
  simp only [Zhat, Pi.smul_apply, ← Matrix.mulVec_mulVec, hv, herm, Matrix.mulVec_smul, dotProduct_smul]

theorem det_leibniz : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  intro E _ _ k r z z' D a b f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hgG : g ∈ Q.Glev k r 0 := hg.1
  obtain ⟨hX1, hX2⟩ := hpart_mem (k := k) (r := r) (i := 0) a b
  set Z : Q.Mx k r := Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := hasDerivAt_f f F U g X1 hU hgU hgG hF hfF hX1
  have hf2 := hasDerivAt_f f F U g X2 hU hgU hgG hF hfF hX2
  have hEf : Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g =
      fderiv ℝ F g (g * X1) + Complex.I • fderiv ℝ F g (g * X2) := by
    show RdV X1 f g + Complex.I • RdV X2 f g = _
    rw [rdV_of_hasDerivAt X1 g f _ hf1, rdV_of_hasDerivAt X2 g f _ hf2]
  have key : ∀ (φ : Q.Mx k r → ℂ) (d1 d2 : ℂ),
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X1))) d1 0 →
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X2))) d2 0 →
      Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => φ x • f x) g =
        φ g • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (d1 + Complex.I * d2) • f g := by
    intro φ d1 d2 h1 h2
    rw [hEf]
    show RdV X1 (fun x => φ x • f x) g + Complex.I • RdV X2 (fun x => φ x • f x) g = _
    rw [rdV_smul_of X1 g φ f d1 _ h1 hf1, rdV_smul_of X2 g φ f d2 _ h2 hf2]
    module
  rw [key (fun x => (Zhat k r z z' x).det) _ _ (hasDerivAt_det_Zhat k r z z' g X1)
    (hasDerivAt_det_Zhat k r z z' g X2)]
  have hsum : g * X1 + Complex.I • (g * X2) = g * Z := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hX1def, hX2def, hpart_sum]
  have hd : ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X1)).trace +
      Complex.I * ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X2)).trace =
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * Z)).trace := by
    rw [← hsum, Zhat_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hd, trace_adjugate_mul_eq_sum_cramer]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hZdef, Zhat_mul_single, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HatNF.DetLeibniz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

@[to_additive]
theorem minorSt_prod_range {M : Type} [CommMonoid M] {N r : ℕ} (hr : r ≤ N) (g : ℕ → M)
    (hg : ∀ s, ¬ (1 ≤ s ∧ s ≤ r) → g s = 1) :
    ∏ s ∈ Finset.range (N + 1), g s = ∏ s : Fin r, g (s.val + 1) := by
  rw [Finset.prod_range_succ', hg 0 (by omega), _root_.mul_one, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) r]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hr)
  intro s _ hs
  apply hg
  rw [Finset.mem_range] at hs
  omega

theorem minorSt : MinorSt := by
  classical
  intro E _ _ _ H Dw K _ typ m n₁ n₂ hm
  let rk : (E →+* ℂ) → ℕ := fun τ => min (Dw.mult τ) (if typ τ then n₁ else n₂)
  have hrk : ∀ τ, rk τ ≤ Dw.mult τ := fun τ => min_le_left _ _
  have hrk1 : ∀ τ, typ τ → rk τ ≤ n₁ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hrk2 : ∀ τ, ¬ typ τ → rk τ ≤ n₂ := fun τ h => (min_le_right _ _).trans (by simp [h])
  have hm0 : ∀ τ s, ¬ (1 ≤ s ∧ s ≤ rk τ) → m τ s = 0 := by
    intro τ s hs
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hm τ s h
    exact hs ⟨h1, le_min h2 h3⟩
  let col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂) := fun τ i =>
    if h : typ τ then Fin.castAdd n₂ (Fin.castLE (hrk1 τ h) i) else Fin.natAdd n₁ (Fin.castLE (hrk2 τ h) i)
  refine ⟨rk, hrk, col, fun τ s => m τ (s.val + 1), ?_, ?_, ?_, ?_⟩
  · intro τ i j hij
    by_cases h : typ τ
    · simp only [col, dif_pos h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
    · simp only [col, dif_neg h] at hij
      have := congrArg Fin.val hij
      exact Fin.ext (by simpa using this)
  · intro τ i
    by_cases h : typ τ
    · have := hrk1 τ h
      have := i.isLt
      simp only [col, dif_pos h, h, iff_true, Fin.val_castAdd, Fin.val_castLE]
      omega
    · simp [col, h]
  · unfold degOf
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [minorSt_sum_range (hrk τ) (fun s => s * m τ s) (fun s hs => by simp [hm0 τ s hs])]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  · unfold minorProd FamGerm.minorsP
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod]
    by_cases h : typ τ
    · rw [if_pos h, if_neg (not_not.mpr h), _root_.mul_one,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₁ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk1 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_pos h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl
    · rw [if_neg h, if_pos h, _root_.one_mul,
        minorSt_prod_range (hrk τ) _ (fun s hs => by rw [hm0 τ s hs, pow_zero])]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hs : s.val + 1 ≤ Dw.mult τ ∧ s.val + 1 ≤ n₂ :=
        ⟨(Nat.succ_le_of_lt s.isLt).trans (hrk τ), (Nat.succ_le_of_lt s.isLt).trans (hrk2 τ h)⟩
      rw [dif_pos hs, map_pow, AlgHom.map_det]
      unfold leadMinor
      congr 2
      ext a i : 2
      simp only [col, dif_neg h, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, MvPolynomial.rename_X]
      rfl

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriLoweringStepGlTensorDualStandard
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.WigSh

def splitCasimirDual {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)) where
  toFun y := WithLp.toLp 2 (fun a => ∑ c, E a c (y c))
  map_add' x y := by
    ext a
    simp [Finset.sum_add_distrib]
  map_smul' t y := by
    ext a
    simp [Finset.smul_sum]

theorem splitCasimirDual_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (y : PiLp 2 (fun _ : Fin (n + 1) => V))
    (a : Fin (n + 1)) : splitCasimirDual E y a = ∑ c, E a c (y c) := rfl

theorem pieri_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ j, L j ≠ L l - 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l - 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hH hadj hEt hL
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.casimir_eigenspace_irred_dual_standard V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  have h4 := _root_.GlobalTheory.reducedWigner_lowering V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.succ + 1) := by
    intro j
    have := hH.anti (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    constructor <;> simp only <;> omega
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hH).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hH.anti).2 hL
  have hz : (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := by
    have hm := (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection_apply_mem
      (PiLp.single 2 (Fin.last n) v)
    exact (Submodule.eq_bot_iff _).1 hbot _ hm
  rw [hz] at h5
  have h6 : ((wM L (fun j : Fin n => L j.succ + 1) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r := by
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    convert (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1
    ext x
    simp
  have hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r)) := continuous_id
    have h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} :=
      hφ.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := νq) hmeas
    rwa [hrestr] at h2
  refine ⟨hae, hcont, ?_, ?_⟩
  · intro a
    exact (hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · intro l hl w hw
    exact hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfinite
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.RhvPoly

inductive IsPol {V : Type} [AddCommGroup V] [Module ℂ V] : (ℂ → V) → Prop
  | const (a : V) : IsPol fun _ => a
  | add {f g : ℂ → V} : IsPol f → IsPol g → IsPol fun y => f y + g y
  | xsmul {f : ℂ → V} : IsPol f → IsPol fun y => y • f y

section module

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end module

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

end alg

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_finset_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → V}
    (hf : ∀ i ∈ s, _root_.GlobalTheory.RhvPoly.IsPol (f i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_pow_smul (n : ℕ) (v : V) : _root_.GlobalTheory.RhvPoly.IsPol fun y : ℂ => y ^ n • v := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    exact ih.xsmul

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eval_smul (p : Polynomial ℂ) (v : V) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => p.eval y • v := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]
  refine isPol_finset_sum _ fun i _ => ?_
  convert isPol_pow_smul i (p.coeff i • v) using 1
  funext y
  exact smul_comm _ _ _

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_linearMap_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℂ) →ₗ[ℂ] A)
    (p : ι → Polynomial ℂ) : _root_.GlobalTheory.RhvPoly.IsPol fun y => g (fun ρ => (p ρ).eval y) := by
  have h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ) := by
    intro y
    ext ρ'
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_smul]
  exact isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_linearMap_comp (g : V →ₗ[ℂ] W) {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => g (f y) := by
  induction hf with
  | const a => exact .const _
  | add _ _ ihf ihg => simpa only [map_add (f := _)] using ihf.add ihg
  | xsmul _ ih => simpa only [map_smul] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_mul {f g : ℂ → A} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (hg : _root_.GlobalTheory.RhvPoly.IsPol g) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg
  | add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg
  | xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_algebraMap_eval (p : Polynomial ℂ) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => algebraMap ℂ A (p.eval y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPol_eval_smul p (1 : A)

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_list_prod {ι : Type} (l : List ι) {F : ι → ℂ → A}
    (hF : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol (F i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => (l.map fun i => F i y).prod := by
  induction l with
  | nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)
  | cons a l ih => simpa using isPol_mul (hF a) ih

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_Tvprod' {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvprod y := by
  have hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i := by
    intro i
    have : (fun y => L.Tvl y i) =
        fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0] := by
      funext y
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvl
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    rw [this]
    exact (_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)
  have h : (fun y => L.Tvprod y) =
      fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod := by
    funext y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod
    simp [List.ofFn_eq_map, List.map_reverse]
  rw [h]
  exact isPol_list_prod _ hT

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma exists_polynomial_eq_functional_of_isPol {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (φ : V →ₗ[ℂ] ℂ) :
    ∃ p : Polynomial ℂ, ∀ y, φ (f y) = p.eval y := by
  induction hf with
  | const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, fun y => by simp [hp, hq]⟩
  | xsmul _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨Polynomial.X * p, fun y => by simp [hp]⟩

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eq_zero_of_infinite_zeros {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) {S : Set ℂ}
    (hS : S.Infinite) (h0 : ∀ y ∈ S, f y = 0) (y : ℂ) : f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨p, hp⟩ := exists_polynomial_eq_functional_of_isPol hf φ
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    (hS.mono fun x hx => by simp [← hp, h0 x hx])
  simp [hp, this]


open MeasureTheory in
theorem _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A]
    (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite →
    (∀ y ∈ S, _root_.GlobalTheory.HatNF.rhv d y ∈ K) → ∀ y : ℂ, _root_.GlobalTheory.HatNF.rhv d y ∈ K := by
  intro P A _ _ _ d K S hS hmem y
  classical
  have hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y := by
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC
    simp [Polynomial.eval_prod]
  have hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y := by
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.S12
    refine isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.M.xEx
    simp [Polynomial.eval_prod]
  have hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y := by
    have := (_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add
      (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi)))
        (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.m0
    simp [sub_eq_add_neg]
  have hTv := isPol_Tvprod' d.L
  have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j :=
    fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv
  have hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y := by
    have h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y =>
        d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 +
          d.L.GG * d.x y * d.L.Tvprod y 1 0) := by
      funext y
      unfold _root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr
      simp
    rw [h]
    refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12)
      (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))
  have hq := isPol_linearMap_comp K.mkQ hpol
  have := isPol_eq_zero_of_infinite_zeros hq hS
    (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y
  exact (Submodule.Quotient.mk_eq_zero K).1 this

end GlobalTheory.RhvPoly
end

