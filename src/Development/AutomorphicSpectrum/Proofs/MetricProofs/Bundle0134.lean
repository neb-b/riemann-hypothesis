module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelation
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem thmA_swap : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  intro hI II hII Ψ _ _ N d S K _ ι _ P Re τ a b hb Q lam
  obtain ⟨h0, h1, h2⟩ := gap_swap_decomp Ψ N τ a b hb lam
  have key := _root_.GlobalTheory.CompanionTheory.Ar.PB.thmA_limit hI GroundTheory.Heights₂.Heights.Inter.FibreLocal.proof II hII K ι d (Ψ × Fin N) S P Re (τ, a) (xiCoef τ a) Q
    (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) h0 (gap lam (τ, a))
  rw [eval_toWt_gap, eval_toWt_gap, ← key]
  exact congrArg₂ (· + ·) (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h1))
    (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h2))

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOnNhdOfDifferentiableOn
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

def sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Ψ (segre (γ t)) i.succ / Ψ (segre (γ t)) 0

def sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (V : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0}

def sheetNorm (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (z : (Σ k, J k) → ℂ) :
    ((k : K) → J k) → ℂ :=
  (Ψ (segre z) 0)⁻¹ • segre z

theorem analyticOnNhd_of_differentiableOn {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : DifferentiableOn ℂ γ V) : AnalyticOnNhd ℂ γ V :=
  fun t ht => analyticAt_pi_iff.mpr fun p => osgood n _ _ hV (differentiableOn_pi.mp hγ p) t ht

theorem analyticAt_psi_segre (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t) :
    AnalyticAt ℂ (fun t' => Ψ (segre (γ t'))) t := by
  classical
  have h1 : AnalyticAt ℂ (fun t' => segre (γ t')) t :=
    analyticAt_pi_iff.mpr fun (i : (k : K) → J k) =>
      Finset.analyticAt_fun_prod _ fun k _ => analyticAt_coord h ⟨k, i k⟩
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp h1

theorem analyticAt_sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t)
    (h0 : Ψ (segre (γ t)) 0 ≠ 0) : AnalyticAt ℂ (sheetProj Ψ γ) t := by
  have hc := fun j => analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ h) j
  exact analyticAt_pi_iff.mpr fun i => (hc i.succ).div (hc 0) h0

theorem isOpen_sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) : IsOpen (sheetReg Ψ γ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨htV, h0, hd⟩
  have hc0 := (analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ (hγ t htV)) 0).continuousAt
  have hcd := (analyticAt_det_fderiv (analyticAt_sheetProj Ψ (hγ t htV) h0)).continuousAt
  filter_upwards [hV.mem_nhds htV, hc0.eventually_ne h0, hcd.eventually_ne hd] with u h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem sheetNorm_mem_fibre {P : Ideal (MRing J)} (hK : Nonempty K) (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ)
    {t : Fin n → ℂ} (hz : γ t ∈ mcPts P) (h0 : Ψ (segre (γ t)) 0 ≠ 0) :
    sheetNorm Ψ (γ t) ∈ fibre P Ψ (sheetProj Ψ γ t) := by
  classical
  obtain ⟨k0⟩ := hK
  set c : K → ℂ := Function.update (fun _ => 1) k0 (Ψ (segre (γ t)) 0)⁻¹ with hc
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hc, h0]
    · simp [hc, hk]
  have hprod : ∏ k, c k = (Ψ (segre (γ t)) 0)⁻¹ := by
    rw [hc, Finset.prod_update_of_mem (Finset.mem_univ k0)]
    simp
  refine ⟨fun p => c p.1 * γ t p, mcPts_smul hP c hc0 hz, ?_, ?_⟩
  · rw [segre_smul, hprod]; rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [sheetNorm, h0]
    · simp [sheetNorm, sheetProj, div_eq_inv_mul]

theorem sheetNorm_eq_torusSat (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {z z' : (Σ k, J k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h0 : Ψ (segre z) 0 ≠ 0)
    (h0' : Ψ (segre z') 0 ≠ 0) (h : sheetNorm Ψ z = sheetNorm Ψ z') : z ∈ torusSat {z'} := by
  have hs : segre z = (Ψ (segre z) 0 * (Ψ (segre z') 0)⁻¹) • segre z' := by
    have := congrArg (fun v => Ψ (segre z) 0 • v) h
    simpa [sheetNorm, smul_smul, h0] using this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre hz' _ (mul_ne_zero h0 (inv_ne_zero h0')) hs
  exact ⟨z', rfl, c, hc, hcz⟩

theorem sheetProj_fibre_finite {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') (y : Fin n → ℂ) :
    ({t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0} ∩ sheetProj Ψ γ ⁻¹' {y}).Finite := by
  refine Set.Finite.of_finite_image (f := fun t => sheetNorm Ψ (γ t))
    ((fibreFinite K J P n Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨t, ⟨⟨htV, h0⟩, hy⟩, rfl⟩
    have := sheetNorm_mem_fibre hP.1 hP.2.1.2.1 Ψ γ (hmem t htV) h0
    rwa [show sheetProj Ψ γ t = y from hy] at this
  · rintro t ⟨⟨ht, h0⟩, -⟩ t' ⟨⟨ht', h0'⟩, -⟩ h
    exact hinj t ht t' ht' (sheetNorm_eq_torusSat Ψ (hmem t' ht').1 h0 h0' h)

theorem sheet_not_flat {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hOV : O ⊆ V) (hne : O.Nonempty) (h0 : ∀ t ∈ O, Ψ (segre (γ t)) 0 ≠ 0)
    (hdet : ∀ t ∈ O, LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne
    (fun t ht => analyticAt_sheetProj Ψ (hγ t (hOV ht)) (h0 t ht)) hdet
  exact hy ((sheetProj_fibre_finite hP hΨ hmem hinj y).subset fun t ht =>
    ⟨⟨hOV ht.1, h0 t ht.1⟩, ht.2⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

def tz {I : Type} [Fintype I] (Z : Matrix I I ℂ) (z : I → ℂ) : I → ℂ := z - Z *ᵥ star z

abbrev Ix (Ψ : Type) (j j' : ℕ) : Type := (Fin j' ⊕ Fin j) × Ψ

def emb {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (i : Ix Ψ j j') : 𝓞 E →+* ℂ :=
  Sum.elim (fun _ => σ i.2) (fun _ => (starRingEnd ℂ).comp (σ i.2)) i.1

def bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ :=
  blockDiagonal fun τ => fromBlocks 0 (ballMat q t τ)ᵀ (ballMat q t τ) 0

def bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (t : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (bigZ q t).submatrix e.symm e.symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIndependentLeOfDualMin
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_independent_le_of_dual_min :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (μ : ℝ), 0 < μ →
      (∀ y : V, y ≠ 0 → (∀ x ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → μ ≤ ‖y‖) →
      ∃ b : Fin (Module.finrank ℝ V) → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
        ∀ i, ‖b i‖ ≤ (Module.finrank ℝ V : ℝ) ^ (3 / 2 : ℝ) / μ := by
  intro V _ _ _ L _ _ μ hμ hdual
  set n := Module.finrank ℝ V with hn
  set c : ℝ := (n : ℝ) / μ with hc
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hμ.le
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  have main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧
      (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
      intro w hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hw0 : w = 0 := by
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
        exact hw
      simp [hw0]
    | succ k ih =>
      intro hk
      obtain ⟨b, hbL, hbli, hbn, hcov⟩ := ih (by omega)
      set W := Submodule.span ℝ (Set.range b) with hW
      set N := Submodule.span ℤ (Set.range b) with hN
      have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
      have hNW : Submodule.span ℝ (N : Set V) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
      have hWtop : W ≠ ⊤ := by
        intro h
        have h1 : Module.finrank ℝ W = k := by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]
        rw [h, finrank_top] at h1
        omega
      have hNsubW : ∀ y ∈ N, y ∈ W := fun y hy => by rw [← hNW]; exact Submodule.subset_span hy
      obtain ⟨m, hmL, hp0, hpn⟩ := Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop
      set p := Wᗮ.starProjection m with hp
      have hpW : p ∈ Wᗮ := Wᗮ.starProjection_apply_mem m
      have hwW : m - p ∈ W := by
        have := Wᗮ.sub_starProjection_mem_orthogonal m
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨z, hzN, hz⟩ := hcov (m - p) hwW
      have hzW : z ∈ W := hNsubW z hzN
      set v := m - z with hv
      have hvdec : v = (m - p - z) + p := by rw [hv]; abel
      have hvL : v ∈ L := L.sub_mem hmL (hNL hzN)
      have hp2 : ‖p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      have pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2 := by
        intro a ha q hq
        have h0 : ⟪a, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal ha hq
        rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]
      have hvW : v ∉ W := by
        intro h
        apply hp0
        have hmW : m ∈ W := by
          have e : m = v + z := by rw [hv]; abel
          rw [e]
          exact W.add_mem h hzW
        have hm' : m ∈ Wᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
        exact Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'
      have hsub : m - p - z ∈ W := W.sub_mem hwW hzW
      refine ⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hvL
        · simpa using hbL j
      · exact linearIndependent_finCons.mpr ⟨hbli, hvW⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hvdec, pyth _ hsub _ hpW]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
          nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]
        · simpa using hbn j
      · intro w' hw'
        rw [Fin.range_cons, Submodule.mem_span_insert] at hw'
        obtain ⟨t, u, hu, rfl⟩ := hw'
        set s := t - round t with hs
        have hs2 : s ^ 2 ≤ 1 / 4 := by
          have h := abs_sub_round t
          rw [← hs] at h
          nlinarith [abs_nonneg s, sq_abs s]
        have hq : s • (m - p - z) + u ∈ W := W.add_mem (W.smul_mem _ hsub) hu
        obtain ⟨z', hz'N, hz'⟩ := hcov (s • (m - p - z) + u) hq
        refine ⟨(round t : ℤ) • v + z', ?_, ?_⟩
        · rw [Fin.range_cons, Submodule.mem_span_insert]
          exact ⟨round t, z', hz'N, rfl⟩
        · have e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p := by
            rw [← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]
            module
          rw [e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs]
          have h4 := mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          push_cast
          nlinarith [h4, hz']
  obtain ⟨b, hbL, hbli, hbn, -⟩ := main n le_rfl
  refine ⟨b, hbL, hbli, fun i => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast i.pos
  have key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc,
      ← Real.rpow_add_one hnR.ne']
    norm_num
  rw [key]
  calc ‖b i‖ = Real.sqrt (‖b i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hbn i)

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriod
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem maDensity_const_eq_normSq_jacobian_mul :
    ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ)
      (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) →
      (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) →
      maDensity (fun (_ : Fin n) => ψ) t =
        ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  intro n φ ψ A G t hA hG hφ hψ
  have h := GroundTheory.Heights₂.Heights.ChartEnergySwapHessian.maDensity_comp_holo
    (fun (_ : Fin n) => ψ) (fun (_ : Fin n) => φ) A G t (fun _ => hφ) hA.contDiffAt hG.contDiffAt
    (fun _ => hψ)
  rw [h, LinearMap.det_toMatrix', Complex.normSq_eq_norm_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp
end

