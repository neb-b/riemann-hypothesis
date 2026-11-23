module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardModelDualRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety

noncomputable section

namespace StandardModelDualRank

variable {K : Type} [Field K] {i : ℕ}

abbrev gen (K : Type) [Field K] (i : ℕ) (j : Fin i) : ProjField K i :=
  algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)

def embK (K : Type) [Field K] (i : ℕ) : K →+* dualStdModelField K i :=
  (dualStdModelEmb K i).comp (algebraMap K (ProjField K i))

def u (K : Type) [Field K] (i : ℕ) (j : Fin i) : dualStdModelField K i :=
  dualStdModelEmb K i (gen K i j) * dualStdModelS K i * dualStdModelT K i

def psiA (K : Type) [Field K] (i : ℕ) :
    MvPolynomial (Fin i) K →+* MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) :=
  eval₂Hom (((C : MvPolynomial Unit (ProjField K i) →+* _).comp C).comp (algebraMap K (ProjField K i)))
    fun j => C (C (gen K i j)) * C (X ()) * X ()

def psi (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) K →+* dualStdModelField K i :=
  (algebraMap _ _).comp (psiA K i)

def psiZ (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) ℤ →+* dualStdModelField K i :=
  (psi K i).comp (MvPolynomial.map (Int.castRingHom K))

theorem psiA_injective : Function.Injective (psiA K i) := by
  let ev : MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) →+* ProjField K i :=
    eval₂Hom (MvPolynomial.eval fun _ => (1 : ProjField K i)) fun _ => 1
  have h : ev.comp (psiA K i) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [ev, psiA, RingHom.comp_apply, eval₂Hom_C, eval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · intro j
      simp [ev, psiA]
  intro p q hpq
  apply IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)
  rw [← h, RingHom.comp_apply, RingHom.comp_apply, hpq]

theorem psi_injective : Function.Injective (psi K i) := by
  rw [psi, RingHom.coe_comp]
  exact (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i)).comp psiA_injective

theorem psi_X (j : Fin i) : psi K i (X j) = u K i j := by
  simp [psi, psiA, u, dualStdModelEmb, dualStdModelS, dualStdModelT]

theorem psi_C (k : K) : psi K i (C k) = embK K i k := by
  simp [psi, psiA, embK, dualStdModelEmb]

theorem closure_le : Subring.closure (Set.range (u K i)) ≤ (psiZ K i).range :=
  (Subring.closure_le).mpr (by rintro _ ⟨j, rfl⟩; exact ⟨X j, by simp [psiZ, psi_X]⟩)

theorem exists_den {f : dualStdModelField K i} (hf : f ∈ Subfield.closure (Set.range (u K i))) :
    ∃ d ∈ (psiZ K i).range, d ≠ 0 ∧ d * f ∈ (psiZ K i).range := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hf
  by_cases h0 : z = 0
  · exact ⟨1, one_mem _, one_ne_zero, by simp [h0]⟩
  · refine ⟨z, closure_le hz, h0, ?_⟩
    rw [mul_div_cancel₀ y h0]
    exact closure_le hy

theorem exists_den_fin {n : ℕ} (f : Fin n → dualStdModelField K i)
    (hf : ∀ k, f k ∈ Subfield.closure (Set.range (u K i))) :
    ∃ D ∈ (psiZ K i).range, D ≠ 0 ∧ ∀ k, D * f k ∈ (psiZ K i).range := by
  classical
  choose d hd hd0 hdf using fun k => exists_den (hf k)
  refine ⟨∏ k, d k, prod_mem fun k _ => hd k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k), mul_comm (d k), mul_assoc]
  exact mul_mem (prod_mem fun l _ => hd l) (hdf k)

variable [NumberField K]

theorem indep_int {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (q : Fin n → MvPolynomial (Fin i) ℤ)
    (h : ∑ k, embK K i (B k) * psiZ K i (q k) = 0) : ∀ k, q k = 0 := by
  have h' : ∑ k, C (B k) * MvPolynomial.map (Int.castRingHom K) (q k) = 0 := by
    apply psi_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    simpa [psiZ, psi_C] using h
  have hB : LinearIndependent ℤ B := B.linearIndependent.restrict_scalars' ℤ
  intro k
  ext m
  have hm := congrArg (AddMonoidAlgebra.coeff · m) h'
  rw [coeff_sum, AddMonoidAlgebra.coeff_zero] at hm
  simp only [coeff_C_mul, coeff_map, eq_intCast] at hm
  have := Fintype.linearIndependent_iff.mp hB (fun k => AddMonoidAlgebra.coeff (q k) m) (by simpa [zsmul_eq_mul, mul_comm] using hm) k
  simpa using this

theorem exists_int_smul_mem (F : HermLattice K i) (v : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : K) • v ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  refine ⟨N, hN, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    have hg' := hint _ (Finset.mem_image_of_mem _ hg)
    rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [dotProduct_add, map_add (f := _), ha, hc]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    rw [dotProduct_smul, map_mul, ha]
    rfl

variable {T : Type}

def w (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : dualStdModelField K i :=
  dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i * dualStdModelT K i

omit [NumberField K] in
theorem S_ne_zero : dualStdModelS K i ≠ 0 := by
  rw [dualStdModelS]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i))).mpr (by simp [X_ne_zero])

omit [NumberField K] in
theorem T_ne_zero : dualStdModelT K i ≠ 0 := by
  rw [dualStdModelT]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i))).mpr (X_ne_zero _)

theorem coord_ne_zero (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) ≠ 0 := by
  rw [map_ne_zero_iff _ (dualStdModelEmb K i).injective, dualLatticeCoord_eq]
  exact evalForm_ne_zero fun h => b.ne_zero t ((Submodule.coe_eq_zero).mp h)

theorem w_ne_zero (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : w b t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (coord_ne_zero b t) S_ne_zero) T_ne_zero

theorem w_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    w b t = ∑ j, embK K i ((b t : Fin i → K) j) * u K i j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [w, u, dualLatticeCoord, map_sum, map_mul, Finset.sum_mul, embK, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_assoc, mul_assoc, mul_assoc]

theorem exists_int_comb [Fintype T] (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (a : K) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ n : T → ℤ, ∑ t, (n t : dualStdModelField K i) * w b t = (N : _) * embK K i a * w b c := by
  obtain ⟨N, hN, hmem⟩ := exists_int_smul_mem (HermLattice.standard K i) (a • (b c : Fin i → K))
  obtain ⟨φ, hφ⟩ : ∃ φ : dualLattice (HermLattice.standard K i),
      (φ : Fin i → K) = (N : K) • a • (b c : Fin i → K) := ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨N, hN, fun t => b.repr φ t, ?_⟩
  have hrepr := congrArg (fun ψ : dualLattice (HermLattice.standard K i) => evalForm i (ψ : Fin i → K))
    (b.sum_repr φ)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hφ, map_smul] at hrepr
  simp only [← dualLatticeCoord_eq b, zsmul_eq_mul, Algebra.smul_def, map_intCast] at hrepr
  have h2 := congrArg (fun y => dualStdModelEmb K i y * dualStdModelS K i * dualStdModelT K i) hrepr
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, Finset.sum_mul] at h2
  simp only [w, embK, RingHom.comp_apply, mul_assoc] at h2 ⊢
  rw [h2]

theorem linIndep {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)]
    (hΦ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Subfield.closure (Set.range (u K i))) :
    LinearIndependent Φ₀ fun k => embK K i (B k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hf : ∀ k, algebraMap Φ₀ _ (g k) ∈ Subfield.closure (Set.range (u K i)) := fun k => by
    rw [← hΦ]; exact RingHom.mem_fieldRange.mpr ⟨g k, rfl⟩
  obtain ⟨D, -, hD0, hD⟩ := exists_den_fin _ hf
  choose q hq using fun k => RingHom.mem_range.mp (hD k)
  simp only [Algebra.smul_def] at hg
  have hsum : ∑ k, embK K i (B k) * psiZ K i (q k) = 0 := by
    calc ∑ k, embK K i (B k) * psiZ K i (q k)
        = D * ∑ k, algebraMap Φ₀ _ (g k) * embK K i (B k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hq]; ring
      _ = 0 := by rw [hg, mul_zero]
  have h0 := indep_int B q hsum
  intro k
  have hk : D * algebraMap Φ₀ (dualStdModelField K i) (g k) = 0 := by rw [← hq, h0, map_zero]
  exact (algebraMap Φ₀ (dualStdModelField K i)).injective
    (((mul_eq_zero.mp hk).resolve_left hD0).trans (map_zero _).symm)

theorem adjoin_embK_eq_span {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)] :
    Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range (embK K i))) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
  have hq : ∀ q : ℚ, (q : dualStdModelField K i) = algebraMap Φ₀ _ ((q.num : Φ₀) / (q.den : Φ₀)) := fun q => by
    rw [map_div₀, map_intCast, map_natCast, Rat.cast_def]
  rw [Algebra.adjoin_eq_span, show Submonoid.closure (Set.range (embK K i)) = (embK K i).range.toSubmonoid from
    Submonoid.closure_eq (embK K i).range.toSubmonoid]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← B.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast, hq, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨B k, rfl⟩)

end StandardModelDualRank

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualCotangentKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualCotangentKer.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    (_b : Module.Basis T ℤ (dualLattice F)) (k : Type) [Field k] (ρ : 𝓞 K →+* k)
    (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ → Function.Surjective σ →
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) →
    ∀ ψ : dualLattice F, σ ψ = 0 →
      ψ ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeModPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeModPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (𝔭 : Ideal (𝓞 K)), 𝔭.IsMaximal →
    ∃ σ : dualLattice F →+ (Fin i → 𝓞 K ⧸ 𝔭), Function.Surjective σ ∧
      ∀ (μ : 𝓞 K) (φ ψ : dualLattice F), (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) →
        σ ψ = Ideal.Quotient.mk 𝔭 μ • σ φ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChartParts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def latCombo {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    (b' : Module.Basis T ℤ (dualLattice F')) (c : T → ℤ) : Fin i → K :=
  ∑ t, c t • (b' t : Fin i → K)

def graphFirstForm {T : Type} [Fintype T] (c : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (c t) * graphFirst t

def graphSecondForm {T : Type} [Fintype T] (d : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (d t) * graphSecond t

def QuadIdentity {K : Type} [Field K] {i : ℕ} (φ₁ φ₂ φ₃ φ₄ : Fin i → K) : Prop :=
  ∀ x : Fin i → K, (φ₁ ⬝ᵥ x) * (φ₂ ⬝ᵥ x) = (φ₃ ⬝ᵥ x) * (φ₄ ⬝ᵥ x)

def excChartIdeal {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

abbrev excChartRing {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) : Type :=
  Localization.Away (Ideal.Quotient.mk (excChartIdeal b' a u) (graphFirst v * graphSecond u))

def excChartMap {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) :
    MRing (stackedBlocks T) →+* excChartRing b' a v u :=
  (algebraMap (MRing (stackedBlocks T) ⧸ excChartIdeal b' a u) (excChartRing b' a v u)).comp
    (Ideal.Quotient.mk (excChartIdeal b' a u))

def DualStackedGraphQuadRel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ),
    (∀ c₁ c₂ c₃ c₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' c₂) (latCombo b' c₃) (latCombo b' c₄) →
      graphFirstForm c₁ * graphFirstForm c₂ - graphFirstForm c₃ * graphFirstForm c₄ ∈ stackedGraph b' a) ∧
    (∀ c₁ d₂ c₃ d₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' fun t => d₂ t * a t) (latCombo b' c₃)
        (latCombo b' fun t => d₄ t * a t) →
      graphFirstForm c₁ * graphSecondForm d₂ - graphFirstForm c₃ * graphSecondForm d₄ ∈ stackedGraph b' a)

def DualStackedExcChartForms.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ σ₀ : k →+* excChartRing b' a v u,
        (∀ (ω : 𝓞 K) (c : T → ℤ), latCombo b' c = algebraMap (𝓞 K) K ω • (b' v : Fin i → K) →
          σ₀ (ρ ω) * excChartMap b' a v u (graphFirst v) = excChartMap b' a v u (graphFirstForm c)) ∧
        ∃ W : Fin (m + 1) → excChartRing b' a v u,
          ∀ t, ∑ j, σ₀ (M t j) * W j = excChartMap b' a v u (graphSecond t)

namespace DualStackedExcChartPartsExample

end DualStackedExcChartPartsExample

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedFormEval {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* MvPolynomial (Fin i) K :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => ∑ j, C ((b' t : Fin i → K) j) * X j
    | ⟨.inr _, t⟩ => ∑ j, C ((b t : Fin i → K) j) * X j

def bidegree (d e : ℕ) : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => d) (fun _ => e)

def DualStackedGraphBihomog.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ f ∈ stackedGraph b' a, ∃ (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MRing (stackedBlocks T)),
      f = ∑ p ∈ s, g p ∧ ∀ p ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g p) (bidegree p.1 p.2) ∧ stackedFormEval b b' (g p) = 0

def DualStackedExcLeadForm.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      ∀ (d e : ℕ) (f : MRing (stackedBlocks T)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (bidegree d e) →
        stackedFormEval b b' f = 0 → linPointMap α M f = 0

namespace DualStackedExcLeadExample

theorem stackedFormEval_first {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphFirst t) = ∑ j, C ((b' t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphFirst]

theorem stackedFormEval_second {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphSecond t) = ∑ j, C ((b t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphSecond]

end DualStackedExcLeadExample

end

end GroundTheory.Heights₂.Heights
end

