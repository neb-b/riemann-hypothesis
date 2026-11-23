module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSpanCommonDenominator
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort


open NumberField MvPolynomial in
theorem _root_.GlobalTheory.det_span_common_denominator : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (M : Submodule (𝓞 F) V), M.FG → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ M) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F) := by
  intro F V _ _ _ _ _ _ d β M hM
  obtain ⟨S, hS⟩ := hM
  obtain ⟨c₀, hc₀⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ ×ˢ S) (fun p : Fin d × V => β.repr p.2 p.1)
  have hcoord : ∀ x ∈ M, ∀ i, (c₀ : 𝓞 F) • β.repr x i ∈ (1 : Submodule (𝓞 F) F) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, hr⟩ := hc₀ (i, g) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hg⟩)
      exact Submodule.mem_one.mpr ⟨r, hr⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), Finsupp.add_apply, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      convert Submodule.smul_mem _ a hx using 1
      rw [← algebraMap_smul F a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      ring
  refine ⟨(c₀ : 𝓞 F) ^ d, pow_ne_zero _ (nonZeroDivisors.ne_zero c₀.2), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    choose B hB using fun i j => Submodule.mem_one.mp (hcoord (w j) (hw j) i)
    rw [Submodule.mem_one]
    refine ⟨(Matrix.of B).det, ?_⟩
    have hmat : (algebraMap (𝓞 F) F).mapMatrix (Matrix.of B) =
        algebraMap (𝓞 F) F (c₀ : 𝓞 F) • β.toMatrix w := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hB, Algebra.smul_def]
    rw [RingHom.map_det, hmat, Matrix.det_smul, Fintype.card_fin, Module.Basis.det_apply,
      Algebra.smul_def, map_pow]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diagonalBlockOfMatrix {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  ⅟(2 : AF F) • ((matD g).toBlocks₁₁ + (matD g).toBlocks₁₂ + (matD g).toBlocks₂₁ + (matD g).toBlocks₂₂)

def BigCell {σ : E →ₐ[F] E} {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : UD σ W) : Prop :=
  ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * diagonalBlockOfMatrix g = 1 ∧
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v

end GlobalTheory.DblVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegral
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDbl

theorem diag_mulVec_mem_latAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : M * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * t)
    (hM : ∀ z ∈ latAtD W v, M *ᵥ z ∈ latAtD W v) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have key : ∀ y : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ y = Sum.elim y y := by
    intro y
    simp [diagCols, Matrix.fromRows_mulVec]
  have h1 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ latAtD W v := by
    rw [key]; exact ⟨hz, hz⟩
  have h2 := hM _ h1
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, key] at h2
  exact h2.1

theorem parD_diag_action :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ d W v p hp t h'
  have h : matD p * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := h'
  obtain ⟨⟨hAt, hK⟩, -⟩ := hp
  have hinv : matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have h1 : matD p⁻¹ * matD p = 1 := p.1.inv_mul
    have h2 : (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1 := t.mul_inv
    calc matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        = matD p⁻¹ * ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
            ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) := by rw [h2, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, fun z hz => ⟨diag_mulVec_mem_latAt W v _ _ h (fun y hy => (hK y hy).1) z hz,
    diag_mulVec_mem_latAt W v _ _ hinv (fun y hy => (hK y hy).2) z hz⟩⟩
  intro u hu
  have h0 := hAt u hu
  have h3 : (matD p - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h4 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
      (u • ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
    rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  ext i j
  have h5 := congrFun (congrFun h4 (Sum.inl i)) j
  rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
  exact h5

end GlobalTheory.InertDbl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

@[reducible] def invTwoE : Invertible (2 : AE F E) :=
  (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm

theorem invOf_two_eq [Invertible (2 : AE F E)] :
    (⅟(2 : AE F E)) = algebraMap (AF F) (AE F E) (⅟(2 : AF F)) :=
  invOf_eq_right_inv (by rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one])

theorem valued_two {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv F v) = 1 := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at this
  convert this using 2
  exact (map_ofNat _ 2).symm

theorem evFin_half_mem {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h := congrArg Valued.v e
  rw [map_mul, valued_two h2, mul_one, map_one] at h
  rw [h]

theorem half_smul_mem {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (⅟(2 : AF F)) • y ∈ GlobalTheory.InertSph.latAt W v := by
  have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.InertSph.latAt W v).comap
      (DistribSMul.toAddMonoidHom (Fin d → AE F E) (⅟(2 : AF F))) := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨a, ha, hint, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply, smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, fun u hu => ?_, ?_, y, hy, rfl⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem (evFin_half_mem h2) hint
  exact hle hy

section Lat

variable {d : ℕ} {W : Spc F E d} {v : Pl (F := F)}

theorem latD_add {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z + w ∈ latD W v :=
  ⟨add_mem hz.1 hw.1, add_mem hz.2 hw.2⟩

theorem latD_sub {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z - w ∈ latD W v :=
  ⟨sub_mem hz.1 hw.1, sub_mem hz.2 hw.2⟩

theorem latD_half [Invertible (2 : AE F E)] (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ latD W v) : (⅟(2 : AE F E)) • z ∈ latD W v := by
  rw [invOf_two_eq, algebraMap_smul]
  exact ⟨half_smul_mem h2 hz.1, half_smul_mem h2 hz.2⟩

theorem latD_diag {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec]
  exact ⟨hy, hy⟩

theorem latD_anti {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact ⟨hy, neg_mem hy⟩

theorem lat_diagT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, one_mulVec]
  exact add_mem hz.1 hz.2

theorem lat_antiT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact add_mem hz.1 (neg_mem hz.2)

end Lat

section Group

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)}

theorem KD_mul {a b : UD σ W} (ha : a ∈ KD σ W v) (hb : b ∈ KD σ W v) : a * b ∈ KD σ W v := by
  have hm : matD (a * b) = matD a * matD b := rfl
  have hi : matD (a * b)⁻¹ = matD b⁻¹ * matD a⁻¹ := by rw [_root_.mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [hm, show matD a * matD b - 1 = (matD a - 1) * matD b + (matD b - 1) by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel, smul_add, ← Matrix.smul_mul, ha.1 u hu, hb.1 u hu,
      Matrix.zero_mul, add_zero]
  · rw [hm, hi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha.2 _ (hb.2 z hz).1).1, (hb.2 _ (ha.2 z hz).2).2⟩

theorem KD_inv {a : UD σ W} (ha : a ∈ KD σ W v) : a⁻¹ ∈ KD σ W v := by
  have h1 : matD a⁻¹ * matD a = 1 := by
    rw [show matD a⁻¹ * matD a = matD (a⁻¹ * a) from rfl, inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [show matD a⁻¹ - 1 = -(matD a⁻¹ * (matD a - 1)) by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel,
      smul_neg, ← Matrix.mul_smul, ha.1 u hu, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(ha.2 z hz).2, (ha.2 z hz).1⟩

end Group

end GlobalTheory.DblVacFactor

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell

theorem factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  intro F E _ _ _ _ _ σ d W v h2 g hg hdet hC
  letI : Invertible (2 : AE F E) := invTwoE
  have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
    rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  rw [hNt] at hdet hC
  unfold antiCols at hdet hC
  set G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := matD g with hGdef
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 (-1) := by rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  set D : Matrix (Fin d) (Fin d) (AE F E) := (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) :
    Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : AE F E) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : AE F E))).pow _).mul hdet
  let s : GL (Fin d) (AE F E) := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit

  have hΔtN : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = 0 := by
    simp [fromCols_mul_fromRows]
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hE : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (G - 1) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hΔtN, sub_zero]
    have hu' : u • (G - 1) = 0 := hg.1 u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (u • (G - 1)) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) * (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef, hE]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
  refine ⟨p, p⁻¹ * g, hpK, ⟨1, ?_⟩, KD_mul (KD_inv hpK) hg, ⟨s, ?_⟩, (mul_inv_cancel_left p g).symm⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _ (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1, Matrix.mul_zero,
        smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · show (1 - ⅟(2 : AE F E) • M) * G * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (s : Matrix (Fin d) (Fin d) (AE F E))
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ e2 hD'

end GlobalTheory.DblVacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingRepresentationInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_representation_injective : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V), Function.Injective (envRepAll R) := by
  first | exact @GlobalTheory.CentralOps.envRepAll_injective | exact GlobalTheory.CentralOps.envRepAll_injective | (intros; apply GlobalTheory.CentralOps.envRepAll_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommute
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaCommutant

theorem finrank_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) :
    Module.finrank F (EA P p N) = N ^ P.g := by
  obtain ⟨-, -, hdim, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have h := rank_eq_of_equiv_equiv (R := F) (R' := Γ((Over.mk p).left, ⊤)) σ j.symm σ.bijective
    (fun c w => j.injective (by rw [j.apply_symm_apply, hj, j.apply_symm_apply]))
  have h' : Module.finrank F (EA P p N) = Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) := by
    unfold Module.finrank
    simpa using congrArg Cardinal.toNat h
  rw [h', hdim]

theorem eq_smul_of_commute {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) (T : EA P p N →ₗ[F] EA P p N)
    (hT : ∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → IsActOf P.A P.L (N : ℤ) θ (T v).sec (T v').sec) :
    ∃ c : F, ∀ v, T v = c • v := by
  have hN1 : 0 < N := Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero])
  have hfr := finrank_eq P F p N hN
  have hpos : 0 < Module.finrank F (EA P p N) := by rw [hfr]; positivity
  haveI : Module.Finite F (EA P p N) := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial (EA P p N) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  obtain ⟨ρ, hact, -, hsame, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns S P (N : ℤ) (Over.mk p)
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have hσ : ∀ c : F, σ.symm (σ c) = c := σ.symm_apply_apply
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have key := hirr (Module.End.eigenspace T c) fun θ hθ v v' hvv hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    obtain ⟨θ₀, h₀, hcomm⟩ := hT θ.pt hθ
    obtain ⟨u, hu⟩ := hsame θ₀ θ h₀
    have e₁ : ρ θ (j.symm v) = j.symm v' := (hact θ _ _).1 hvv
    have e₂ : IsActOf P.A P.L (N : ℤ) θ₀ v.sec (j (ρ θ₀ (j.symm v))).sec := (hact θ₀ _ _).2 rfl
    have e₃ : ρ θ₀ (j.symm (T v)) = j.symm (T (j (ρ θ₀ (j.symm v)))) := (hact θ₀ _ _).1 (hcomm _ _ e₂)
    have e₄ : v' = σ.symm (u : Γ((Over.mk p).left, ⊤)) • j (ρ θ₀ (j.symm v)) := by
      rw [← hj, σ.apply_symm_apply, ← hu, e₁, j.apply_symm_apply]
    have e₅ : T (j (ρ θ₀ (j.symm v))) = c • j (ρ θ₀ (j.symm v)) := by
      have e₆ : j.symm (c • v) = σ c • j.symm v := rfl
      rw [← j.apply_symm_apply (T (j (ρ θ₀ (j.symm v)))), ← e₃, hv, e₆, map_smul, hj]
    rw [e₄, map_smul, e₅, smul_comm]
  rcases key with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · intro v
    exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)

end GlobalTheory.ThetaCommutant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralCircleOneParameterUnitaryRealPlaceStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type)
    [Fintype β] [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (w₀ : InfinitePlace F), IsCMExt F E σ →
    ∃ z : ℝ → (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, ∃ γ ∈ RLines (σ := σ) J,
      IsGen τ C γ (fun w => if w = w₀ then Complex.I • (1 : Mat R S) else 0) ∧
      (∀ t : ℝ, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧
      (∀ t : ℝ, At (evI F) ((z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) ∧
      ∀ (t : ℝ) (w : InfinitePlace F), piInf (τ w) (z t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = if w = w₀ then Complex.exp (t * Complex.I) else 1 := by
  first | exact @GlobalTheory.CentralLine.exists_central_line | exact GlobalTheory.CentralLine.exists_central_line | (intros; apply GlobalTheory.CentralLine.exists_central_line <;> assumption)
end

