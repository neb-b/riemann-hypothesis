module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0782
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
section
open NumberField IsDedekindDomain

noncomputable section
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_pureA_bound {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖thetaSum F (pureA F f g)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hw := ZLattice.summable_norm_pow_inv (denomLattice F κ N) (Module.finrank ℤ (denomLattice F κ N) + 1)
    (Nat.lt_succ_self _)
  set k := Module.finrank ℤ (denomLattice F κ N) + 1 with hkdef
  set W := ∑' z : denomLattice F κ N, ‖z‖⁻¹ ^ k with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  refine ⟨{(0, 0), (k, 0)}, max B 0 * (1 + W), mul_nonneg (le_max_right _ _) (by linarith), fun f => ?_⟩
  set M := (({(0, 0), (k, 0)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f with hMdef
  have h00 : ∀ x, ‖f x‖ ≤ M := fun x => (SchwartzMap.norm_le_seminorm ℂ f x).trans
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (0, 0)) (by simp))
  have hk0 : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ M := fun x => by
    have := SchwartzMap.le_seminorm ℂ k 0 f x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (k, 0)) (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h00 0)
  have hpt : ∀ z : denomLattice F κ N, ‖f z‖ ≤ (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M := fun z => by
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      have := h00 0
      have h2 : 0 ≤ ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M := by positivity
      simpa using (show ‖f 0‖ ≤ M + ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M by linarith)
    · rw [if_neg hz, zero_add]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hz0 _), mul_comm]
      exact hk0 z
  have hs1 : HasSum (fun z : denomLattice F κ N => if z = 0 then M else 0) M := by
    convert hasSum_ite_eq (0 : denomLattice F κ N) M
  have hsumL : Summable fun z : denomLattice F κ N => (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M :=
    hs1.summable.add (hw.mul_right M)
  have hfL : Summable fun z : denomLattice F κ N => ‖f z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumL
  have hLbound : ∑' z : denomLattice F κ N, ‖f z‖ ≤ (1 + W) * M := by
    refine (hfL.tsum_le_tsum hpt hsumL).trans (le_of_eq ?_)
    rw [hs1.summable.tsum_add (hw.mul_right M), hs1.tsum_eq, tsum_mul_right]
    ring

  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  have hsupp : Function.support (fun ξ : κ → F => ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖)
      ⊆ S := by
    intro ξ hξ
    rw [Function.mem_support, norm_ne_zero_iff, pureA_algebraMap] at hξ
    have h0 := right_ne_zero_of_mul hξ
    show ∀ i, _
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hterm : ∀ ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ ≤
      max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := fun ξ => by
    rw [pureA_algebraMap, norm_mul, mul_comm, Function.comp_apply]
    exact mul_le_mul (le_max_of_le_left (hB _)) le_rfl (norm_nonneg _) (le_max_right _ _)
  have hsumS : Summable ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) := hfL.comp_injective hj
  calc ‖thetaSum F (pureA F f g)‖
      ≤ ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_of_mem_schA F hmem)
    _ = ∑' ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ ≤ ∑' ξ : S, max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ :=
        ((summable_norm_of_mem_schA F hmem).subtype (fun x => x ∈ S)).tsum_le_tsum hterm (hsumS.mul_left _)
    _ = max B 0 * ∑' ξ : S, ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := tsum_mul_left
    _ ≤ max B 0 * ∑' z : denomLattice F κ N, ‖f z‖ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hfL (fun _ => norm_nonneg _) hj) (le_max_right _ _)
    _ ≤ max B 0 * ((1 + W) * M) := mul_le_mul_of_nonneg_left hLbound (le_max_right _ _)
    _ = max B 0 * (1 + W) * M := by ring

theorem exists_adm_eq_thetaSum_of_locallyCompact (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    (κ : Type) [Fintype κ] : ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
      ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := by
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F κ)
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ h => by
    have := LinearMap.congr_fun hl ⟨Φ, h⟩
    simpa using this
  refine ⟨l, fun g hg => ?_, hl'⟩
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hadd : ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') g = pureA F f g + pureA F f' g := fun f f' => by
    funext x; simp [pureA, add_mul]
  have hsmul : ∀ (a : ℂ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) g = a • pureA F f g := fun a f => by
    funext x; simp [pureA, mul_assoc]
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => thetaSum F (pureA F f g))
      (fun f f' => by rw [hadd]; exact thetaSum_add F (hmem f) (hmem f'))
      (fun a f => by rw [hsmul, thetaSum_smul]; rfl) (thetaSum_pureA_bound F hg)
  exact ⟨T, fun f => hl' _ (hmem f)⟩

end GlobalTheory.WeilM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDiaStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (exact GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (intros; apply GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.Rounding.exists_rounding | exact GlobalTheory.Rounding.exists_rounding | (intros; apply GlobalTheory.Rounding.exists_rounding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := by
  obtain ⟨p, U, V, h1, h2⟩ := exists_factor P hP
  refine ⟨p, by rw [← h1, Matrix.trace_mul_comm, h2]; simp, fun a => ?_⟩
  have e : P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 + (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (V ⊗ₖ (a - 1)) := by
    rw [← Matrix.mul_kronecker_mul, h1, Matrix.one_mul, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  have e2 : 1 + (V ⊗ₖ (a - 1)) * (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ a := by
    rw [← Matrix.mul_kronecker_mul, h2, Matrix.mul_one, ← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply]
    ring
  rw [e, Matrix.det_one_add_mul_comm, e2, Matrix.det_kronecker]
  simp

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := by
  obtain ⟨P, hPd⟩ : ∃ P, P = (1 / 2 : ℂ) • (1 + s) := ⟨_, rfl⟩
  have hQ : (1 / 2 : ℂ) • (1 - s) = 1 - P := by rw [hPd]; module
  have hP : P * P = P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, hs, one_mul, mul_one, one_mul]; module
  obtain ⟨p, hp, hd⟩ := det_idem_kron (n := n) P hP
  refine ⟨p, ?_, fun a b hb => ?_⟩
  · rw [hPd, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at hp
    linear_combination 2 * hp
  have hc : P * b = b * P := by
    rw [hPd, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hb, one_mul, mul_one]
  have hc2 : P * b * P = P * b := by rw [mul_assoc, ← hc, ← mul_assoc, hP]
  rw [← hPd, hQ]
  constructor
  · have e1 : (1 / 2 : ℂ) • ((1 + s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) * (b ⊗ₖ aᵀ)) +
        (1 / 2 : ℂ) • (1 - s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
        (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hQ, hPd, Matrix.transpose_one, add_mul, ← Matrix.mul_kronecker_mul, Matrix.smul_mul, add_mul, one_mul, one_mul,
        one_mul, ← Matrix.one_kronecker_one]
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : (P * b) ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
        ((P * b + (1 - P)) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) *
          (P ⊗ₖ aᵀ + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      have f1 : (P * b + (1 - P)) * P = P * b := by rw [add_mul, hc2, sub_mul, one_mul, hP, sub_self, add_zero]
      have f2 : (P * b + (1 - P)) * (1 - P) = 1 - P := by rw [mul_sub, f1, mul_one]; abel
      rw [mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, f1, f2, one_mul, one_mul]
    unfold GlobalTheory.WeilParts.detPlus
    rw [e1, e2, Matrix.det_mul, hd, Matrix.det_kronecker]
    simp
  · rw [← Matrix.det_mul]
    congr 1
    have f3 : P * b * ((1 - P) * b) = 0 := by
      rw [← mul_assoc, mul_sub, mul_one, hc2, sub_self, zero_mul]
    have f4 : (1 - P) * ((1 - P) * b) = (1 - P) * b := by
      rw [← mul_assoc, sub_mul, mul_sub, mul_sub, hP]; simp
    have f5 : (1 - P) * P = 0 := by rw [sub_mul, hP, one_mul, sub_self]
    rw [add_mul, mul_add, mul_add, f3, f4, f5, hc2, sub_mul]; simp

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := by
  obtain ⟨n, hn, h0, h⟩ := hχ
  obtain ⟨n', hn', -, h'⟩ := hη
  have e : n' = 1 := by
    have : (n' : ℚ) = 1 := by rw [hn']; norm_num
    exact_mod_cast this
  subst e
  refine ⟨n - k, by push_cast; rw [hn]; ring, h0, fun θ hθ x h1 h2 => ?_⟩
  have hne : θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
    have := h' θ hθ x h1 h2
    rw [zpow_one] at this
    rw [← this]; exact Circle.coe_ne_zero _
  rw [zpow_sub₀ hne, ← h θ hθ x h1 h2, zpow_natCast]
  have := h' θ hθ x h1 h2
  rw [zpow_one] at this
  rw [← this]
  simp [div_eq_mul_inv]

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]


open Classical in
theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  choose x hx1 hx2 using fun τ => exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν c hc => ?_⟩
  · refine adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine Finset.prod_congr rfl fun τ _ => ?_
    obtain ⟨n, hn, -, h⟩ := hc τ
    have e : n = 2 * c τ := by exact_mod_cast hn
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2, e, ← hw1, _root_.zpow_mul]
    simp

end GlobalTheory.VacuumCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralModelOfGaloisStableTorsion
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.modelAt_of_stable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro L β u V N hβ hβim hu12 hN hNodd F ι _ T hg2 hg3 huF hst hT hcard
  have hΔ := latticeCurve_Δ_ne_zero L
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (by norm_num)] at hu12
    exact hΔ ((Valuation.zero_iff _).mp hu12.symm)
  have hj : (latticeCurve L).j ∈ V := by
    have hi : _root_.IsIntegral V (latticeCurve L).j := (_root_.GlobalTheory.CMModel.LatticeJInt.main L β hβ hβim).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    rw [← hy]; exact y.2
  obtain ⟨r, s, t, hint⟩ := GlobalTheory.T.exists_variableChange_intV_of_j_mem (latticeCurve L) V (Units.mk0 u hu) hj hu12
  have htm := fun i => _root_.GlobalTheory.CMModel.torsion_coords_mem_of_odd L β u V N hβ hβim hu12 hN hNodd hu r s t hint (T i) (hT i).1 (hT i).2
  have hud := fun i => _root_.GlobalTheory.valuation_derivWeierstrassP_torsion_odd L β u V N hβ hβim hu12 hN hNodd (T i) (hT i).1 (hT i).2
  have havg := GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables V (-L.g₂ / 4) (-L.g₃ / 4) r s t (Units.mk0 u hu) ι
    (fun i => L.weierstrassP (T i)) (fun i => L.derivWeierstrassP (T i) / 2) hint hcard
    (fun i => (htm i).1) (fun i => (htm i).2)
    (fun i => by
      show V.valuation (2 * (L.derivWeierstrassP (T i) / 2)) = V.valuation u ^ 3
      rw [mul_div_cancel₀ _ two_ne_zero]; exact hud i)
  obtain ⟨h1, h2, h3, -⟩ := _root_.GlobalTheory.CMModel.stable_sym_mem F L ι T hg2 hg3 hst (fun i => (hT i).1)
  have hnF : ((Fintype.card ι : ℕ) : ℂ) ∈ F := natCast_mem F _
  refine ⟨⟨Units.mk0 u hu, (∑ i, L.weierstrassP (T i)) / Fintype.card ι,
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) / Fintype.card ι,
    (∑ i, L.derivWeierstrassP (T i) / 2) / Fintype.card ι⟩, huF, div_mem h1 hnF, div_mem h3 hnF,
    div_mem h2 hnF, havg, ?_⟩
  have hv : V.valuation u ^ 12 ≠ 0 := by
    rw [hu12]; exact (Valuation.ne_zero_iff _).mpr hΔ
  rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, map_one,
    ← hu12, inv_pow, inv_mul_cancel₀ hv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfReductions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgComplete

open GlobalTheory.CechPic GlobalTheory.ZV

theorem exists_lineBundle_of_reductions : GlobalTheory.Published.FormalAlgebraisation → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → ∃ M : LB X.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro hP R _ _ I hI X hX Y β b hb hc N hN hv
  have hpr : IsProper X.hom := isProper_of_isProjBy R _ _ hX
  obtain ⟨H, hH, m, σ, hσ⟩ := hX
  have hA : IsAmpleLB H := isAmpleLB_of_veryAmpleBy hσ
  have hY : ∀ e, IsProper (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @IsProper) (hb e) hpr
  have hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := b (e + 1)) (h₂₂ := thick R I (e + 1)) (v₁₃ := X.hom) ?_ ?_ (hb (e + 1))
    · rw [hc, thickTrans_comp]
      exact hb e
    · have : Mono (thick R I (e + 1)) := by
        have : IsClosedImmersion (thick R I (e + 1)) :=
          IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
        infer_instance
      rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp, ← (hb (e + 1)).w,
        ← Category.assoc, hc, (hb e).w]
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => LB.isLB_pull hH _
  have hA₀ : IsAmpleLB (H.pull (b 0)) := by
    have : IsClosedImmersion (thick R I 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (b 0) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb 0).flip this
    exact hA.pull_of_isClosedImmersion _
  have := hY 0
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isAmpleLB (Y 0).hom hA₀ (hN 0)).exists
  have hT : ∀ e, (LB.div (lbPow (H.pull (b e)) t) (N e)).IsLB := fun e =>
    LB.isLB_div (isLB_lbPow (hL e) t) (hN e)
  have eT : ∀ e, cls _ (hT e) = t • CechPic.pull (b e) (cls H hH) - cls _ (hN e) := fun e => by
    rw [cls_div (isLB_lbPow (hL e) t) (hN e), cls_lbPow (hL e), cls_pull hH]
  obtain ⟨X', M, b', hX', hM, -, hb', hc', hM'⟩ := hP.2 R I hI Y β hβ hY
    (fun e => LB.div (lbPow (H.pull (b e)) t) (N e)) hT
    (fun e => (cls_eq_iff (hT e) (LB.isLB_pull (hT (e + 1)) _)).1 (by
      rw [cls_pull (hT (e + 1)), eT, eT, (cls_eq_iff (hN e) (LB.isLB_pull (hN (e + 1)) _)).2 (hv e),
        cls_pull (hN (e + 1)), map_sub, map_nsmul, ← CechPic.pull_comp, hc]))
    ((relAmple_iff_isAmpleLB_of_isAffine (Y 0) (hT 0)).2 ht)
  obtain ⟨g, hg, -⟩ := hP.1.exists_iso hI hb hc hb' hc'
  have hMg : (M.pull g.hom.left).IsLB := LB.isLB_pull hM _
  have hF : (LB.div (lbPow H t) (M.pull g.hom.left)).IsLB := LB.isLB_div (isLB_lbPow hH t) hMg
  refine ⟨_, hF, fun e => (cls_eq_iff (hN e) (LB.isLB_pull hF _)).1 ?_⟩
  have e₁ := (cls_eq_iff (hT e) (LB.isLB_pull hM _)).2 (hM' e)
  rw [eT, cls_pull hM] at e₁
  rw [cls_pull hF, cls_div (isLB_lbPow hH t) hMg, cls_lbPow hH, cls_pull hM, map_sub, map_nsmul,
    ← CechPic.pull_comp, hg, ← e₁, sub_sub_cancel]

end GlobalTheory.LBAlgComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebrasStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  first | (exact @GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (exact GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (intros; apply GlobalTheory.QUnits.tensorFractionRing_units_pow_surj  <;> assumption)
end

