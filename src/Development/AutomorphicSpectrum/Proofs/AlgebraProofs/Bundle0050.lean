module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCoords
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ModelPushforwardFibreDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFurtherTermIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0063
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagFrameOfFullFlag
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagInd
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0097

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

section Scale

variable {T : Type} [Fintype T]

def blockVal {R : Type} (P Q : T → R) : (Σ κ, stackedBlocks T κ) → R
  | ⟨.inl _, t⟩ => P t
  | ⟨.inr _, t⟩ => Q t

def blockEval {R : Type} [CommRing R] (P Q : T → R) : MRing (stackedBlocks T) →+* R :=
  eval₂Hom (Int.castRingHom R) (blockVal P Q)

theorem blockEval_first {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphFirst t) = P t := by
  simp [blockEval, graphFirst, blockVal]

theorem blockEval_second {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphSecond t) = Q t := by
  simp [blockEval, graphSecond, blockVal]

theorem ringHom_block_ext {R : Type} [CommRing R] {f g : MRing (stackedBlocks T) →+* R}
    (h1 : ∀ t, f (graphFirst t) = g (graphFirst t)) (h2 : ∀ t, f (graphSecond t) = g (graphSecond t)) :
    f = g := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
    · exact h1 t
    · exact h2 t

theorem blockEval_scale {R : Type} [CommRing R] (P Q : T → R) (l μ : R) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e)) :
    blockEval (fun t => l * P t) (fun t => μ * Q t) f = l ^ d * μ ^ e * blockEval P Q f := by
  classical
  simp only [blockEval, coe_eval₂Hom]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ t : T, m ⟨Sum.inl (), t⟩ = d := hf m hm (Sum.inl ())
  have h2 : ∑ t : T, m ⟨Sum.inr (), t⟩ = e := hf m hm (Sum.inr ())
  have key : ∏ s, blockVal (fun t => l * P t) (fun t => μ * Q t) s ^ m s =
      l ^ d * μ ^ e * ∏ s, blockVal P Q s ^ m s := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique]
    change (∏ t : T, (l * P t) ^ m ⟨Sum.inl (), t⟩) * (∏ t : T, (μ * Q t) ^ m ⟨Sum.inr (), t⟩) =
      l ^ d * μ ^ e * ((∏ t : T, P t ^ m ⟨Sum.inl (), t⟩) * ∏ t : T, Q t ^ m ⟨Sum.inr (), t⟩)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1, h2]
    ring
  rw [key]
  ring

end Scale

section ThetaShiftProofs

variable {K : Type} [Field K] {i m : ℕ}

theorem arc_form (p : K) (y₀ : Fin i → K) (g : Fin m → Fin i → K) (φ : Fin i → K) :
    eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
        (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (∑ j, C (φ j) * X j) =
      C p * (C (φ ⬝ᵥ y₀) * X 0 + ∑ l, C (φ ⬝ᵥ g l) * X l.succ) := by
  have hj : ∀ j, eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
      (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (C (φ j) * X j) =
      C p * (C (φ j * y₀ j) * X 0 + ∑ l, C (φ j * g l j) * X l.succ) := by
    intro j
    rw [map_mul, eval₂Hom_C, eval₂Hom_X']
    simp only [C_mul, mul_assoc, ← Finset.mul_sum]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, Finset.sum_mul]

end ThetaShiftProofs

section Lead

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem lead_of_coords {b : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F)} {b' : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F')}
    {k : Type} [Field k] {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e))
    (h0 : GroundTheory.Heights₂.Heights.stackedFormEval b b' f = 0) : linPointMap α M f = 0 := by
  obtain ⟨-, hπ, -, hg, hα, hM0, hMj, ⟨t₀, ht₀⟩, -, -, -, -⟩ := hco
  choose cα hcα hcαρ using hα
  choose c0 hc0 hc0ρ using hM0
  choose c1 hc1 hc1ρ using hMj
  have hh : ∀ t l, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ g l :=
    fun t l => (b' t).2 _ (hg l)
  choose h hh using hh
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := by
    intro hp
    apply ht₀
    have hc : cα t₀ = 0 := hinj (by rw [hcα, hp, map_zero, zero_smul, dotProduct_zero])
    rw [← hcαρ t₀, hc, map_zero]

  let A : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (cα t) * X 0 + ∑ l, C (π * h t l) * X l.succ
  let L : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (c0 t) * X 0 + ∑ l, C (c1 t l) * X l.succ
  let ι : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Fin (m + 1)) K :=
    map (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι := map_injective _ hinj
  let p : K := algebraMap (𝓞 K) K π
  let Φ : MvPolynomial (Fin i) K →+* MvPolynomial (Fin (m + 1)) K :=
    eval₂Hom C (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ))
  have hΦ : Φ.comp (GroundTheory.Heights₂.Heights.stackedFormEval b b') =
      blockEval (fun t => 1 * ι (A t)) (fun t => C p * ι (L t)) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_first, blockEval_first]
      refine (arc_form p y₀ g _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A, ι, map_add (f := _), map_mul, map_C, map_X, map_sum, one_mul]
      rw [hcα, dotProduct_smul, smul_eq_mul, C_mul, mul_add, Finset.mul_sum, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hh]
      exact (mul_assoc _ _ _).symm
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_second, blockEval_second]
      refine (arc_form p y₀ g _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [L, ι, map_add (f := _), map_mul, map_C, map_X, map_sum, hc0, hc1]
  have hι2 : blockEval (fun t => ι (A t)) (fun t => ι (L t)) = ι.comp (blockEval A L) := by
    apply ringHom_block_ext
    · intro t
      simp only [RingHom.comp_apply, blockEval_first]
    · intro t
      simp only [RingHom.comp_apply, blockEval_second]
  have e1 : (C p) ^ e * ι (blockEval A L f) = 0 := by
    have h1 := congrArg (fun r => r f) hΦ
    simp only [RingHom.comp_apply, h0, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, hι2, one_pow, one_mul, RingHom.comp_apply] at h1
    exact h1.symm
  have e2 : blockEval A L f = 0 := by
    have hCp : (C p : MvPolynomial (Fin (m + 1)) K) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hπ0
    exact hι (by rw [map_zero]; exact (mul_eq_zero.mp e1).resolve_left (pow_ne_zero _ hCp))

  let ψ : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Option (Fin (m + 1))) k :=
    eval₂Hom (C.comp ρ) (fun j => X (some j))
  let ℓ : T → MvPolynomial (Option (Fin (m + 1))) k := fun t => ∑ j, C (M t j) * X (some j)
  have hψ : ψ.comp (blockEval A L) =
      blockEval (fun t => X (some 0) * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, blockEval_first, blockEval_first]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [A, ψ, map_add (f := _), map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hcαρ,
        hπ, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
      ring
    · intro t
      rw [RingHom.comp_apply, blockEval_second, blockEval_second]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [L, ψ, ℓ, map_add (f := _), map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hc0ρ,
        hc1ρ, one_mul, Fin.sum_univ_succ]
  have hlin : (linPointMap α M : MRing (stackedBlocks T) →+* _) =
      blockEval (fun t => X none * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [LinPrimeExample.linPointMap_first, blockEval_first, mul_comm]
    · intro t
      rw [LinPrimeExample.linPointMap_second, blockEval_second, one_mul]
  have e3 : blockEval (fun t => C (α t)) ℓ f = 0 := by
    have h1 := congrArg (fun r => r f) hψ
    simp only [RingHom.comp_apply, e2, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, one_pow, mul_one] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ (X_ne_zero _))
  rw [hlin, blockEval_scale _ _ _ _ hf, e3, mul_zero]

theorem centre_mem_of_coords {b : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F)} {b' : Module.Basis T ℤ (GroundTheory.Heights₂.Heights.dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k]
    {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨-, hπ, -, -, hα, hM0, -⟩ := hco
  obtain ⟨c, hc, hcρ⟩ := hα t
  obtain ⟨c', hc', -⟩ := hM0 t
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have h : ((a t : ℤ) : 𝓞 K) * c = π * c' := by
    apply hinj
    rw [map_mul, map_mul, map_intCast, hc, hc', hab t, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      zsmul_eq_mul]
    ring
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [← hcρ, ← map_intCast ρ, ← map_mul, h, map_mul, hπ, zero_mul]
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end Lead

theorem exc_base : DualStackedExcBase.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ ρ π y₀ m g α M hco
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, G, rfl, hG⟩ := graph_bihomog K i F F' T b b' a hab f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp => lead_of_coords hco (hG p hp).1 (hG p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem_of_coords hab hco

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem dualStackedExcCoords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedExcCoords.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyHodgeLatticeData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Conj.Fam GlobalTheory.CompanionTheory.Ar.Crv.Inhab

theorem mem_imLat_iff_stdLat {K : Type} [Field K] (C : ACurve K) {d : ℕ} (i : C.I)
    (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) (y : (Fin d → K) × (Fin d → K)) :
    y ∈ imLat C i T ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring T := by
  have hs : ∀ w : (Fin d → K) × (Fin d → K), w ∈ stdH C d i ↔
      ∀ j, w.1 j ∈ (C.v i).valuationSubring.toSubring ∧ w.2 j ∈ (C.v i).valuationSubring.toSubring := by
    intro w
    rw [mem_stdH]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
    exact Submodule.subset_span ⟨w, (hs w).1 hw, rfl⟩
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact (mem_imLat C).2 ⟨w, (hs w).2 hw, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
      refine (mem_imLat C).2 ⟨(a : K) • w, (hs _).2 fun j => ?_, ?_⟩
      · exact ⟨Subring.mul_mem _ a.2 ((hs w).1 hw j).1, Subring.mul_mem _ a.2 ((hs w).1 hw j).2⟩
      · rw [map_smul]
        rfl

theorem family_conj_H_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧
      ∀ i, D.H i = imLat C i (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.rho_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint K d O F.B
  have iso := fun i => _root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => _root_.GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ⟨(good i h).1, (good i h).2.1⟩)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi (by
              obtain ⟨g₁, g₂, g₃⟩ := good i h
              exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃))
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρH, fun _ => rfl⟩
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact _root_.GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act K p d O F.B a u
  · rw [hρ, hρH]
    exact _root_.GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq K p d O F.B a y

theorem family_conj_H_lattices : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρH a = rhoH F.B a) ∧ ∀ i y, y ∈ D.H i ↔ y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨D, h₁, h₂⟩ := family_conj_H_eq K C p d O F hI
  refine ⟨D, h₁, fun i y => ?_⟩
  rw [h₂ i]
  exact mem_imLat_iff_stdLat C i _ y

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FieldExtensionIntersectionInvariance
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.field_extension_intersection_invariance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁), IsModelOver (pointIdeal O (bcCoord x z)) d → ∀ (c : K → ℕ) (f : MRing ι O), IsMultiHomog f c → f ∉ (pointIdeal O x) → ∀ l : List (K → ℤ), l.length = d → (open Classical in cycEval (fun W => if (C ϖ : MRing (Sum.elim ι ι') O) ∈ W then vNumL W (l.map (pullDeg (K' := K'))) else 0) (divCycle (pointIdeal O (bcCoord x z)) (rename (liftVar ι') f))) = (modelDeg O x z : ℤ) * (open Classical in cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W l else 0) (divCycle (pointIdeal O x) f)) := by
  first | exact @PositivityTheory.Xgn.model_pushforward_fibre_degree | exact PositivityTheory.Xgn.model_pushforward_fibre_degree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatement
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem polyNum_eq_sum {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (V : Ideal (MRing ι F)) (e : ℕ)
    (hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V e) {N : ℕ} (d : Fin N → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (c n : ℕ) (Y : Fin n → K → ℤ) (hG : G.IsHomogeneous c)
    (hcn : c + n = e) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I V e (Fin.append d Y)
                              (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
      ∑ μ ∈ G.support, G.coeff μ * intNumL F V (classList d μ ++ List.ofFn Y) := by
  rw [SegreFlagIndep.prod_X_natAdd, SegreFlagIndep.polyNum_mul_monomial, SegreFlagIndep.monoList_ones]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  have hdeg : α.degree = c := by
    have := hG (mem_support_iff.mp hα)
    rwa [Finsupp.degree_eq_weight_one]
  have hlen : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList d α ++ List.ofFn Y).length = e := by
    rw [List.length_append, SegreFlagIndep.length_monoList, hdeg, List.length_ofFn, hcn]
  rw [SegreFlagIndep.listNum, dite_eq_left hlen,
    Numbers.agree FieldNumbers.IntNumUnique.full (IntNumPoint.proof FieldNumbers.IntNumBase.full)
      FieldNumbers.IntNumBase.full I hI V e _ hV,
    BundleExamples.intNum_get_cast F V _ e hlen]
  refine FlagTypings.intNumL_perm F V (List.Perm.append_right _ ?_)
  rw [BundleExamples.monoList_eq]
  exact FlagTypings.monoList_perm d α

theorem segreFlagIndep (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{0} F Ω ι := by
  classical
  intro x e hV N E _ _ B fl₁ fl₂ I hI G hG c n Y hGc hcn
  obtain ⟨w, hw⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₁
  obtain ⟨v, hv⟩ := BundleExamples.FlagFrameOfFullFlag.proof F Ω K ι x e hV N E B fl₂
  rw [polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn, polyNum_eq_sum I hI _ e hV _ G c n Y hGc hcn]
  have hI' := VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι (pointIdeal F x)
  have hP : IsMultiProjPrime (pointIdeal F x) := ⟨hV.1.1, hI'.1 hV.1.2.1, hV.1.2.2⟩
  exact _root_.PositivityTheory.HtPt.Pflag.field_flag_indep F Ω K ι x e hP hV.2 N E B w v _ _ hw hv c G hG hGc (List.ofFn Y)
    (by rw [List.length_ofFn]; omega)

end GlobalTheory.CompanionTheory.Ar.Num.FurtherIndep

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem flag_further_term_independent :
    GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.flagFurtherTerm_independent.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagVerticalSymmetric.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorFibreVariety.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.FullFlagRestriction.proof
      FurtherIndep.segreFlagIndep)

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullConeNullModP : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

