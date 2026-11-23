module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0075
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0025
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
section
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerSeq

theorem lseq_transport : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W)
    (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)),
    (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) →
    LSeq l S S' → Nonempty (LSeq l T T') := by
  intro W _ l S S' T T' e e' h h' L
  let E : ∀ n, S.M n ≃ₗ[W] T.M n := fun n => LinearEquiv.ofBijective (e.f n) (h n)
  let E' : ∀ n, S'.M n ≃ₗ[W] T'.M n := fun n => LinearEquiv.ofBijective (e'.f n) (h' n)
  have hc : ∀ n y, T.r n (E (n + 1) y) = E n (S.r n y) := fun n y => e.comm n y
  have hc' : ∀ n y, T'.r n (E' (n + 1) y) = E' n (S'.r n y) := fun n y => e'.comm n y
  have hr : ∀ n x, (E n).symm (T.r n x) = S.r n ((E (n + 1)).symm x) := by
    intro n x
    apply (E n).injective
    rw [LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]
  refine ⟨{
    ρ := fun c b => (E b).toLinearMap ∘ₗ L.ρ c b ∘ₗ (E c).symm.toLinearMap
    ν := fun a c => (E c).toLinearMap ∘ₗ L.ν a c ∘ₗ (E a).symm.toLinearMap
    δ := fun b a => (E' a).toLinearMap ∘ₗ L.δ b a ∘ₗ (E b).symm.toLinearMap
    kill := ?_, ρ_self := ?_, ρ_succ := ?_, ν_ρ := ?_, ν_r := ?_, ex₁ := ?_, δ_r := ?_, ex₂ := ?_ }⟩
  · intro n x
    apply (E n).symm.injective
    rw [map_smul, L.kill, map_zero]
  · intro c x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_self, LinearEquiv.apply_symm_apply]
  · intro c b hb x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_succ c b hb, hr]
  · intro a c ha x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [L.ν_ρ a c ha, map_smul, LinearEquiv.apply_symm_apply]
  · intro a c ha y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc, L.ν_r a c ha, hr]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.ρ c b ((E c).symm x) = 0 := by
      apply (E b).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₁ a b c hcab _ h0
    refine ⟨E a y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · intro b a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc', L.δ_r]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.δ b a ((E b).symm x) = 0 := by
      apply (E' a).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₂ a b c hcab _ h0
    refine ⟨E c y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.TowerSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProper
section
open MeasureTheory Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

theorem fibreFamily_eq_inter (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (W : Set V) (hW : IsOpen W)
    (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B' ∩ W) := (hB'.preimage hg).inter hW
  have hOU : g ⁻¹' B' ∩ W ⊆ g ⁻¹' B ∩ W := Set.inter_subset_inter_left _ (Set.preimage_mono hBB)
  have hbB : b ∈ B := hBB hb
  refine measure_eq_of_lintegral_eq (fib' b) (fib b) (g ⁻¹' B' ∩ W) hO ?_ ?_ ?_
  · refine measure_mono_null ?_ (h'.1 b)
    intro v hv hv'
    exact hv hv'.2
  · refine measure_mono_null ?_ (h.1 b)
    intro v hv hv'
    have hgv : g v = b := hι (by rw [← hf v]; exact hv'.1)
    exact hv ⟨show g v ∈ B' from hgv ▸ hb, hv'.2.2⟩
  · intro φ hφc hφs hφO hφnn
    have hφU : tsupport φ ⊆ g ⁻¹' B ∩ W := hφO.trans hOU
    obtain ⟨hint', hcont'⟩ := h'.2.2 φ hφc hφs hφO
    obtain ⟨hint, hcont⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨hint' b hb, ?_⟩
    have hψm : Measurable (fun v => ENNReal.ofReal (φ v)) := hφc.measurable.ennreal_ofReal
    have hψ0 : ∀ v, v ∉ g ⁻¹' B' ∩ W → ENNReal.ofReal (φ v) = 0 := by
      intro v hv
      have hz : φ v = 0 := by
        by_contra hne
        exact hv (hφO (subset_tsupport φ (Function.mem_support.mpr hne)))
      simp [hz]
    have hF : ∀ c ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = ENNReal.ofReal (∫ v, φ v ∂(fib c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint c hc) (ae_of_all _ hφnn)).symm
    have hF' : ∀ c ∈ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) =
        ENNReal.ofReal (∫ v, φ v ∂(fib' c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint' c hc) (ae_of_all _ hφnn)).symm
    have hset : ∀ S, MeasurableSet S →
        ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν =
          ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := by
      intro S hS
      have hS' : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
      have e1 := lintegral_preimage hι hg hf hO hOU h (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'
      have e2 := lintegral_preimage hι hg hf hO Set.Subset.rfl h' (fun v => ENNReal.ofReal (φ v))
        hψm hψ0 _ hS'
      exact e1.symm.trans e2
    have key : ∀ (k k' : X → ℝ≥0∞) (T : Set X), MeasurableSet T → (∀ c ∈ T, k c = k' c) →
        ∫⁻ c in T, k c ∂ν = ∫⁻ c in T, k' c ∂ν := fun k k' T hT hkk =>
      lintegral_congr_ae ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall hkk))
    have hae : (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib c))) =ᵐ[ν.restrict B']
        (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib' c))) := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ ?_ ?_ ?_
      · exact ((hcont.mono hBB).aemeasurable hB'.measurableSet).ennreal_ofReal
      · exact (hcont'.aemeasurable hB'.measurableSet).ennreal_ofReal
      · intro S hS _
        rw [Measure.restrict_restrict hS]
        have hT : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
        calc ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib c)) ∂ν
            = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν :=
              key _ _ _ hT (fun c hc => (hF c (hBB hc.2)).symm)
          _ = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := hset S hS
          _ = ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib' c)) ∂ν :=
              key _ _ _ hT (fun c hc => hF' c hc.2)
    have heq := Measure.eqOn_open_of_ae_eq hae hB'
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono hBB))
      (ENNReal.continuous_ofReal.comp_continuousOn hcont') hb
    rw [hF' b hb, hF b hbB]
    exact heq.symm

end GlobalTheory.CompanionTheory.SW.FibreUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
section
open scoped TensorProduct
open IsLocalRing

namespace GlobalTheory.CompanionTheory.UnitNorm

noncomputable section

section Basics

variable {O O' R : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]

def tw (τ : O' ≃ₐ[O] O') (j : ℕ) : O' ⊗[O] R →ₐ[O] O' ⊗[O] R :=
  Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R)

def nrm (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R) : O' ⊗[O] R :=
  ∏ j ∈ Finset.range ℓ, tw τ j s

abbrev inc : R →ₐ[O] O' ⊗[O] R := Algebra.TensorProduct.includeRight

theorem nrm_mul (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (x y : O' ⊗[O] R) :
    nrm ℓ τ (x * y) = nrm ℓ τ x * nrm ℓ τ y := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_mul, Finset.prod_mul_distrib]

theorem nrm_one (ℓ : ℕ) (τ : O' ≃ₐ[O] O') : nrm ℓ τ (1 : O' ⊗[O] R) = 1 := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_one, Finset.prod_const_one]

theorem map_tw (τ : O' ≃ₐ[O] O') (j : ℕ) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (tw τ j s) = tw τ (j + 1) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
      AlgHom.id_apply, pow_succ', AlgEquiv.mul_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tw_period {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    tw τ ℓ s = tw τ 0 s := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, hτ, pow_zero]

theorem nrm_fixed {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (nrm ℓ τ s) = nrm ℓ τ s := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod, GlobalTheory.CompanionTheory.UnitNorm.map_tw]
  rw [Finset.prod_range_succ, Finset.prod_range_succ', GlobalTheory.CompanionTheory.UnitNorm.tw_period hτ]

theorem map_inc_map (A : Ideal O) :
    Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) (Ideal.map (algebraMap O R) A) =
      Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← AlgHom.commutes (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

theorem tw_mem (τ : O' ≃ₐ[O] O') (j : ℕ) (A : Ideal O) {x : O' ⊗[O] R}
    (hx : x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    tw τ j x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  have h : Ideal.map (algebraMap O (O' ⊗[O] R)) A ≤
      Ideal.comap (GlobalTheory.CompanionTheory.UnitNorm.tw τ j) (Ideal.map (algebraMap O (O' ⊗[O] R)) A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem nrm_sub_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (A : Ideal O) {x y : O' ⊗[O] R}
    (h : x - y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    nrm ℓ τ x - nrm ℓ τ y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  rw [← Ideal.Quotient.eq]
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.Quotient.eq, ← map_sub]
  exact GlobalTheory.CompanionTheory.UnitNorm.tw_mem τ j A h

theorem step [Module.Finite O O'] [Module.Free O O'] [Nontrivial O'] {ℓ : ℕ} {τ : O' ≃ₐ[O] O'}
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfixS : ∀ s : O' ⊗[O] R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s →
      s ∈ Set.range (inc : R →ₐ[O] O' ⊗[O] R))
    (a : O')
    (hcong : ∀ m : ℕ, 1 ≤ m → ∀ r ∈ (⊥ : Ideal R).jacobson ^ m,
      nrm ℓ τ (1 + a ⊗ₜ[O] r) - (inc : R →ₐ[O] O' ⊗[O] R) (1 + r) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)))
    (u : R) (m : ℕ) (hm : 1 ≤ m) (P : (O' ⊗[O] R)ˣ)
    (h : (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P : O' ⊗[O] R) ∈
      Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) :
    ∃ P' : (O' ⊗[O] R)ˣ, (P' : O' ⊗[O] R) - (P : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) ∧
      (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P' : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
  have hfix_incR : ∀ x : R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
      ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x) = (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x := by
    intro x
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply]
  obtain ⟨r, hr⟩ := hfixS ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R)) (by
    rw [map_sub, hfix_incR, GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ])
  obtain ⟨v, hv⟩ := hfixS (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R))
    (GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ _)
  have hrm : r ∈ (⊥ : Ideal R).jacobson ^ m := by
    have h' := h
    rw [← hr] at h'
    exact _root_.GlobalTheory.CompanionTheory.Descent.mem_of_includeRight_mem_map O O' R _ r h'
  have hvr : v * r ∈ (⊥ : Ideal R).jacobson ^ m := Ideal.mul_mem_left _ v hrm
  have hsplit : a ⊗ₜ[O] (v * r) = (a ⊗ₜ[O] (1 : R)) * (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (v * r) := by
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  have hmem : a ⊗ₜ[O] (v * r) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) := by
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hvr)
  have hJ : a ⊗ₜ[O] (v * r) ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson :=
    Ideal.map_mono (Ideal.pow_le_self (by omega)) hmem
  have hU : IsUnit (1 + a ⊗ₜ[O] (v * r)) :=
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R _ hJ
  have hPP : GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R) = 1 := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, Units.mul_inv, GlobalTheory.CompanionTheory.UnitNorm.nrm_one]
  have hc' : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
    have h'' := neg_mem (hcong m hm (v * r) hvr)
    rwa [neg_sub] at h''
  have key : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u -
        GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) =
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
        ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r))) := by
    rw [map_add (f := _), map_one, map_mul]
    linear_combination (-1 : O' ⊗[O] R) * hr +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R))) * hv +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r)) * hPP
  refine ⟨P * hU.unit, ?_, ?_⟩
  · rw [Units.val_mul, IsUnit.unit_spec,
      show (P : O' ⊗[O] R) * (1 + a ⊗ₜ[O] (v * r)) - P = P * (a ⊗ₜ[O] (v * r)) by ring]
    exact Ideal.mul_mem_left _ _ hmem
  · rw [Units.val_mul, IsUnit.unit_spec, GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, key]
    exact Ideal.mul_mem_left _ _ hc'

end Basics

theorem norm_units_surjective : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  intro hInt hConj
  unfold PositivityTheory.Rg.Tf.Loc.N3
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hbasis r
  by_cases hO' : Nontrivial O'
  swap
  · haveI : Subsingleton O' := not_nontrivial_iff_subsingleton.mp hO'
    have h1 : (1 : O' ⊗[O] R) = 0 := by
      calc (1 : O' ⊗[O] R) = (1 : O') ⊗ₜ[O] (1 : R) := Algebra.TensorProduct.one_def
        _ = (0 : O') ⊗ₜ[O] (1 : R) := by rw [Subsingleton.elim (1 : O') 0]
        _ = 0 := by rw [TensorProduct.zero_tmul]
    haveI : Subsingleton (O' ⊗[O] R) := subsingleton_of_zero_eq_one h1.symm
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI := hO'
  obtain ⟨hfixS, a, ha1, hcong⟩ := hConj O O' R ℓ τ hℓ hτ hfix hbasis
  obtain ⟨hle, N, hN⟩ := _root_.GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le O R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) (O' ⊗[O] R) :=
    _root_.GlobalTheory.CompanionTheory.FiniteComplete.isAdicComplete_of_finite O (O' ⊗[O] R)
  obtain ⟨P₁, hP₁⟩ :=
    _root_.GlobalTheory.CompanionTheory.FirstApprox.main hInt O O' R ℓ τ hℓ hτ hfix hbasis ⟨a, ha1⟩ r
  have h2 : ∀ k : ℕ, Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (N * k + 1)) ≤
      Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O ^ k) := by
    intro k
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_pow]
    exact le_trans (Ideal.pow_le_pow_right (Nat.le_succ _))
      (by rw [pow_mul]; exact Ideal.pow_right_mono hN k)
  have h3 : Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O) ≤
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map, pow_one]
    exact Ideal.map_mono hle
  have h4 : ∀ x ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1),
      IsUnit (1 + x) := fun x hx =>
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R x (by rwa [pow_one] at hx)
  have h6 : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P₁ : O' ⊗[O] R) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [pow_one, ← neg_sub]
    exact neg_mem hP₁
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.CompanionTheory.AdicApprox.exists_unit_eq_of_successive_approximation O (O' ⊗[O] R)
    (IsLocalRing.maximalIdeal O)
    (fun m => Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) N
    (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ) ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R)) P₁
    (fun m => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ m))) h2 h3 h4
    (fun k x y hxy => GlobalTheory.CompanionTheory.UnitNorm.nrm_sub_mem ℓ τ _ hxy) h6
    (fun m hm P hP => GlobalTheory.CompanionTheory.UnitNorm.step hℓ hτ hfixS a hcong (r : R) m hm P hP)
  exact ⟨L, hL⟩

end

end GlobalTheory.CompanionTheory.UnitNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
section
noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.MassCount

variable {F : Type} [Field F] [NumberField F]

theorem count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB

theorem norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by
  have hw := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ev : InfiniteAdeleRing F →+* w.Completion := Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w
  have h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h1 : e (ev (θ ε)) = ε := DFunLike.congr_fun h0 ε
  have hn : ∀ a : w.Completion, ‖a‖ = |e a| := by
    intro a
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm
  have h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w := rfl
  rw [h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

theorem countBd : PositivityTheory.Rg.Mass.CountBd := by
  intro F _ _ hF θ _ K hK N hN
  haveI := hF
  have hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c := fun w =>
    hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w)
      (continuous_apply w).continuousOn
  choose c hc using hb
  set R : ℝ := ∑ w, |c w| with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcR : ∀ w, c w ≤ R := fun w =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))
  refine ⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩
  have hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆
      {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε} := by
    rintro x ⟨hx, hy, hxK⟩
    refine ⟨hx, hy, fun w => ?_⟩
    have h := hc w _ hxK
    rw [norm_theta_mul, abs_of_pos hε] at h
    rw [le_div_iff₀ hε, mul_comm]
    exact h.trans (hcR w)
  obtain ⟨hfin, hcount⟩ := count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)
  refine ⟨hfin.subset hsub, ?_⟩
  have hI0 : (0 : ℝ) < Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hle := Set.ncard_le_ncard hsub hfin
  rw [le_div_iff₀ hI0]
  have hle' := (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount
  calc _ ≤ ε ^ Module.finrank ℚ F * (4 * (R / ε) * N) ^ Module.finrank ℚ F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = (4 * R * N) ^ Module.finrank ℚ F := by
        rw [← mul_pow]
        congr 1
        field_simp

end GlobalTheory.CompanionTheory.MassCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjMemFixedPiN
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem proj_mem_fixed_piN (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (v : fixed π D.J) : D.proj π (v : V) ∈ fixed (D.piN π) D.JT := by
  intro t
  have ht : ((t : D.T) : G) ∈ D.J := Subgroup.mem_comap.mp t.2
  have hv : π ((t : D.T) : G) (v : V) = (v : V) := by
    have h := v.2 ⟨((t : D.T) : G), ht⟩
    simpa using h
  have hq : (D.piN π) (t : D.T) (D.proj π (v : V)) = D.proj π (π ((t : D.T) : G) (v : V)) := rfl
  rw [hq, hv, MonoidHom.one_apply, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Mass.MeanV

variable {F : Type} [Field F] [NumberField F]

def IntOut (T : Finset (HeightOneSpectrum (𝓞 F))) : Set F :=
  {x | ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F}

def GoodFac (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ) : Prop :=
  ContinuousOn g {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g s = 0) ∧
    (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
    (∀ s : Fv F v, Valued.v s = 1 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g s ∂lam = 1

def truncSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
    (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1

def fullSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0},
    G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

