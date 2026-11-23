module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

namespace GlobalTheory.QuadricSection

section general

variable {n : Type} [Fintype n] [DecidableEq n]

def coef (J : Matrix n n ℂ) (x y : n → ℂ) : ℂ := star (x - y) ⬝ᵥ (J *ᵥ x)

def qrefl (J : Matrix n n ℂ) (x y : n → ℂ) : Matrix n n ℂ :=
  1 - (coef J x y)⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.qrefl_mulVec (J : Matrix n n ℂ) (x y : n → ℂ)
    (hc : _root_.GlobalTheory.QuadricSection.coef J x y ≠ 0) :
    _root_.GlobalTheory.QuadricSection.qrefl J x y *ᵥ x = y := by
  have hdot : (star (x - y) ᵥ* J) ⬝ᵥ x = _root_.GlobalTheory.QuadricSection.coef J x y := by
    rw [_root_.GlobalTheory.QuadricSection.coef, dotProduct_mulVec]
  rw [_root_.GlobalTheory.QuadricSection.qrefl, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    hdot, op_smul_eq_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_sub_cancel]

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
private lemma star_dotProduct_mulVec_of_hermitian {J : Matrix n n ℂ} (hJ : Jᴴ = J) (a b : n → ℂ) :
    star (star a ⬝ᵥ (J *ᵥ b)) = star b ⬝ᵥ (J *ᵥ a) := by
  rw [← star_dotProduct_star, star_mulVec, star_star, hJ, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.qrefl_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (x y : n → ℂ)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (hc : _root_.GlobalTheory.QuadricSection.coef J x y ≠ 0) :
    (_root_.GlobalTheory.QuadricSection.qrefl J x y)ᴴ * J * _root_.GlobalTheory.QuadricSection.qrefl J x y = J := by
  set c := _root_.GlobalTheory.QuadricSection.coef J x y with hcdef
  set d := x - y with hd
  set e := star d ᵥ* J with he
  have hstar_e : star e = J *ᵥ d := by rw [he, star_vecMul, hJ, star_star]
  have hq : e ⬝ᵥ d = star d ⬝ᵥ (J *ᵥ d) := by rw [he, dotProduct_mulVec]
  have hsum : c + star c = star d ⬝ᵥ (J *ᵥ d) := by
    have h1 : star c = star x ⬝ᵥ (J *ᵥ d) := by
      rw [hcdef, _root_.GlobalTheory.QuadricSection.coef, star_dotProduct_mulVec_of_hermitian hJ]
    rw [h1, hcdef, _root_.GlobalTheory.QuadricSection.coef, ← hd]
    simp only [hd, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct]
    linear_combination hxy
  have hcs : star c ≠ 0 := star_ne_zero.mpr hc
  have hJe : J * vecMulVec d e = vecMulVec (J *ᵥ d) e := mul_vecMulVec _ _ _
  have heJ : vecMulVec (J *ᵥ d) (star d) * J = vecMulVec (J *ᵥ d) e := by
    rw [vecMulVec_mul]
  have hVV : vecMulVec (J *ᵥ d) e * vecMulVec d e = (e ⬝ᵥ d) • vecMulVec (J *ᵥ d) e := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  have hR : (_root_.GlobalTheory.QuadricSection.qrefl J x y)ᴴ = 1 - (star c)⁻¹ • vecMulVec (J *ᵥ d) (star d) := by
    rw [_root_.GlobalTheory.QuadricSection.qrefl, ← hcdef, ← hd, ← he, conjTranspose_sub, conjTranspose_one,
      conjTranspose_smul, conjTranspose_vecMulVec, hstar_e, star_inv₀]
  rw [hR, _root_.GlobalTheory.QuadricSection.qrefl, ← hcdef, ← hd, ← he]
  have hexp : (1 - (star c)⁻¹ • vecMulVec (J *ᵥ d) (star d)) * J * (1 - c⁻¹ • vecMulVec d e) =
      J - (c⁻¹ + (star c)⁻¹ - (star c)⁻¹ * c⁻¹ * (e ⬝ᵥ d)) • vecMulVec (J *ᵥ d) e := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, heJ, hJe, hVV,
      smul_smul]
    module
  rw [hexp, hq, ← hsum]
  have hzero : c⁻¹ + (star c)⁻¹ - (star c)⁻¹ * c⁻¹ * (c + star c) = 0 := by
    field_simp
    ring
  rw [hzero, zero_smul, sub_zero]

open MeasureTheory Matrix in
variable {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.QuadricSection.measurable_qrefl (J : Matrix n n ℂ) (x : n → ℂ) (i j : n) :
    Measurable fun y => _root_.GlobalTheory.QuadricSection.qrefl J x y i j := by
  have hd : Continuous fun y : n → ℂ => x - y := by fun_prop
  have hcoef : Measurable fun y => _root_.GlobalTheory.QuadricSection.coef J x y := by
    refine Continuous.measurable ?_
    unfold _root_.GlobalTheory.QuadricSection.coef
    exact (continuous_star.comp hd).dotProduct continuous_const
  have hvec : Continuous fun y : n → ℂ => vecMulVec (x - y) (star (x - y) ᵥ* J) i j := by
    simp only [vecMulVec_apply]
    refine ((continuous_apply i).comp hd).mul ?_
    exact (continuous_apply j).comp ((continuous_star.comp hd).matrix_vecMul continuous_const)
  simp only [_root_.GlobalTheory.QuadricSection.qrefl, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.sub (hcoef.inv.mul hvec.measurable)

end general

open GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.jpq_conjTranspose (P Q : ℕ) : (_root_.Formalism.UG.Jpq P Q)ᴴ = _root_.Formalism.UG.Jpq P Q := by
  unfold _root_.Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.form_self {P Q : ℕ} (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    star x ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x) = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x : ℂ) := by
  rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_self, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform]
  unfold _root_.Formalism.UG.hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_add]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.measurable_qf {P Q : ℕ} :
    Measurable (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  refine Continuous.measurable ?_
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf
  fun_prop


open Classical in
def sectMat {P Q : ℕ} (β : ℝ) (x₀ y : Sp P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  if qf y = β then
    (if coef (Formalism.UG.Jpq P Q) x₀ y = 0 then -qrefl (Formalism.UG.Jpq P Q) x₀ (-y)
      else qrefl (Formalism.UG.Jpq P Q) x₀ y)
  else 1

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.qf_neg {P Q : ℕ} (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf (-y) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf
  simp [Complex.normSq_neg]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.sectMat_spec {P Q : ℕ} {β : ℝ} {x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q}
    (hβ : β ≠ 0) (hx : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β) (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * _root_.Formalism.UG.Jpq P Q * _root_.GlobalTheory.QuadricSection.sectMat β x₀ y = _root_.Formalism.UG.Jpq P Q ∧
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β → _root_.GlobalTheory.QuadricSection.sectMat β x₀ y *ᵥ x₀ = y) := by
  have hJ := _root_.GlobalTheory.QuadricSection.jpq_conjTranspose P Q
  by_cases hy : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β
  · have hxy : star x₀ ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x₀) = star y ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ y) := by
      rw [_root_.GlobalTheory.QuadricSection.form_self, _root_.GlobalTheory.QuadricSection.form_self, hx, hy]
    by_cases hc : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0
    · have hxy' : star x₀ ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ x₀) = star (-y) ⬝ᵥ (_root_.Formalism.UG.Jpq P Q *ᵥ -y) := by
        rw [hxy, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]
      have hc' : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ (-y) ≠ 0 := by
        have hsum : _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y +
            _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ (-y) = 2 * (β : ℂ) := by
          rw [← hx, ← _root_.GlobalTheory.QuadricSection.form_self]
          simp only [_root_.GlobalTheory.QuadricSection.coef, sub_neg_eq_add, star_sub, star_add,
            sub_dotProduct, add_dotProduct]
          ring
        rw [hc, zero_add] at hsum
        rw [hsum]
        exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hβ)
      have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y =
          -_root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ (-y) := by
        simp [_root_.GlobalTheory.QuadricSection.sectMat, hy, hc]
      rw [hsect]
      refine ⟨?_, fun _ => ?_⟩
      · rw [conjTranspose_neg, neg_mul, neg_mul, mul_neg, neg_neg]
        exact _root_.GlobalTheory.QuadricSection.qrefl_unitary _ hJ x₀ (-y) hxy' hc'
      · rw [neg_mulVec, _root_.GlobalTheory.QuadricSection.qrefl_mulVec _ x₀ (-y) hc', neg_neg]
    · have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y =
          _root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ y := by
        simp [_root_.GlobalTheory.QuadricSection.sectMat, hy, hc]
      rw [hsect]
      exact ⟨_root_.GlobalTheory.QuadricSection.qrefl_unitary _ hJ x₀ y hxy hc,
        fun _ => _root_.GlobalTheory.QuadricSection.qrefl_mulVec _ x₀ y hc⟩
  · have hsect : _root_.GlobalTheory.QuadricSection.sectMat β x₀ y = 1 := by
      simp [_root_.GlobalTheory.QuadricSection.sectMat, hy]
    rw [hsect]
    exact ⟨by simp, fun h => absurd h hy⟩

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.measurable_sectMat {P Q : ℕ} (β : ℝ) (x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q)
    (i j : Fin P ⊕ Fin Q) :
    Measurable fun y => _root_.GlobalTheory.QuadricSection.sectMat β x₀ y i j := by
  classical
  have hset1 : MeasurableSet {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q | _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β} :=
    _root_.GlobalTheory.QuadricSection.measurable_qf (measurableSet_singleton β)
  have hcoef : Measurable fun y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q =>
      _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y := by
    refine Continuous.measurable ?_
    unfold _root_.GlobalTheory.QuadricSection.coef
    exact (continuous_star.comp (continuous_const.sub continuous_id)).dotProduct continuous_const
  have hset2 : MeasurableSet {y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q |
      _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0} :=
    hcoef (measurableSet_singleton 0)
  have heq : (fun y => _root_.GlobalTheory.QuadricSection.sectMat β x₀ y i j) = fun y =>
      if _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf y = β then
        (if _root_.GlobalTheory.QuadricSection.coef (_root_.Formalism.UG.Jpq P Q) x₀ y = 0 then
          -_root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ (-y) i j
        else _root_.GlobalTheory.QuadricSection.qrefl (_root_.Formalism.UG.Jpq P Q) x₀ y i j)
      else (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j := by
    funext y
    unfold _root_.GlobalTheory.QuadricSection.sectMat
    split_ifs <;> rfl
  rw [heq]
  refine Measurable.ite hset1 (Measurable.ite hset2 ?_ ?_) measurable_const
  · exact ((_root_.GlobalTheory.QuadricSection.measurable_qrefl _ x₀ i j).comp measurable_neg).neg
  · exact _root_.GlobalTheory.QuadricSection.measurable_qrefl _ x₀ i j


open MeasureTheory Matrix in
theorem _root_.GlobalTheory.QuadricSection.exists_isSection : ∀ (P Q : ℕ) (β : ℝ) (x₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q), β ≠ 0 →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x₀ = β →
    ∃ s : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → _root_.Formalism.BasicNotions.UpqT P Q, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection β x₀ s := by
  intro P Q β x₀ hβ hx
  have hspec := fun y => _root_.GlobalTheory.QuadricSection.sectMat_spec hβ hx y
  have hunit : ∀ y, IsUnit (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y).det := by
    intro y
    refine isUnit_det_of_left_inverse
      (B := _root_.Formalism.UG.Jpq P Q * (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * _root_.Formalism.UG.Jpq P Q) ?_
    have hU : (_root_.GlobalTheory.QuadricSection.sectMat β x₀ y)ᴴ * (_root_.Formalism.UG.Jpq P Q * _root_.GlobalTheory.QuadricSection.sectMat β x₀ y) =
        _root_.Formalism.UG.Jpq P Q := by
      rw [← Matrix.mul_assoc]
      exact (hspec y).1
    simp only [Matrix.mul_assoc]
    rw [hU, _root_.GlobalTheory.UpqTopology.jpq_sq]
  have hcT : ∀ M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, _root_.Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    unfold _root_.Formalism.UG.cT
    ext i j
    simp [conjTranspose_apply]
  have hmem : ∀ y, Matrix.nonsingInvUnit _ (hunit y) ∈ _root_.Formalism.UG.Upq P Q := by
    intro y
    unfold _root_.Formalism.UG.Upq _root_.Formalism.UG.UJ
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    rw [hcT]
    exact (hspec y).1
  refine ⟨fun y => (⟨Matrix.nonsingInvUnit _ (hunit y), hmem y⟩ : _root_.Formalism.UG.Upq P Q), ?_⟩
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.IsSection
  refine ⟨?_, ?_⟩
  · letI : MeasurableSpace (_root_.Formalism.BasicNotions.UpqT P Q) := _root_.Formalism.BasicNotions.instMeasurableSpaceUpqT P Q
    haveI : BorelSpace (_root_.Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩
    letI : MeasurableSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := MeasurableSpace.pi
    haveI : BorelSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
      inferInstanceAs (BorelSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
    apply (_root_.GlobalTheory.UpqTopology.isClosedEmbedding_mat.measurableEmbedding.measurable_comp_iff).mp
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    exact _root_.GlobalTheory.QuadricSection.measurable_sectMat β x₀ i j
  · intro y hy
    exact (hspec y).2 hy

end GlobalTheory.QuadricSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInvStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧ HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M) := by
  first | exact @GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | exact GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | (intros; apply GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvariantMeasureQuadricMulHaarStabilizer
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal Pointwise

namespace GlobalTheory.QuadricHaar

theorem exists_const {G H X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (a : G → X → X) (a_mul : ∀ g h x, a (g * h) x = a g (a h x)) (a_one : ∀ x, a 1 x = x)
    (a_meas : ∀ g, Measurable (a g)) (x₀ : X) (a_cont : Continuous fun g => a g x₀)
    (S : X → Prop) (j : H →* G) (ν : Measure X) (μ : Measure G) (μ' : Measure H)
    (hj : IsClosedEmbedding j) (hr : Set.range j = {g | a g x₀ = x₀})
    [IsFiniteMeasureOnCompacts ν] (hS : ∀ᵐ y ∂ν, S y) (hν : ∀ g, ν.map (a g) = ν)
    [μ.IsHaarMeasure] [μ'.IsHaarMeasure] :
    ∃ κ : ℝ≥0, ∀ s : X → G, (Measurable s ∧ ∀ y, S y → a (s y) x₀ = y) →
      ∀ f : G → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  by_cases hex : ∃ s : X → G, Measurable s ∧ ∀ y, S y → a (s y) x₀ = y
  swap
  · exact ⟨0, fun s hs => (hex ⟨s, hs⟩).elim⟩
  obtain ⟨s₀, hs₀, hs₀'⟩ := hex
  have hjm : Measurable j := hj.continuous.measurable
  have key : ∀ (f : G → ℝ≥0∞) (b c : G), a b x₀ = a c x₀ →
      ∫⁻ g', f (b * j g') ∂μ' = ∫⁻ g', f (c * j g') ∂μ' := by
    intro f b c h
    have : b⁻¹ * c ∈ Set.range j := by
      rw [hr]
      change a (b⁻¹ * c) x₀ = x₀
      rw [a_mul, ← h, ← a_mul, inv_mul_cancel, a_one]
    obtain ⟨k, hk⟩ := this
    rw [← lintegral_mul_left_eq_self (fun g' => f (b * j g')) k]
    refine lintegral_congr fun g' => ?_
    rw [map_mul, hk, ← mul_assoc, mul_inv_cancel_left]
  have hp : Measurable fun p : X × H => s₀ p.1 * j p.2 :=
    (hs₀.comp measurable_fst).mul (hjm.comp measurable_snd)
  set m : Measure G := (ν.prod μ').map fun p : X × H => s₀ p.1 * j p.2 with hm
  have hint : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂m = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
    intro f hf
    rw [hm, lintegral_map hf hp]
    exact lintegral_prod _ (hf.comp hp).aemeasurable
  have hmeas : ∀ f : G → ℝ≥0∞, Measurable f →
      Measurable fun y => ∫⁻ g', f (s₀ y * j g') ∂μ' := fun f hf =>
    (hf.comp hp).lintegral_prod_right'
  haveI : m.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul h),
      hint (fun g => f (h * g)) (hf.comp (measurable_const_mul h)), hint f hf]
    have e : ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν =
        ∫⁻ y, (∫⁻ g', f (s₀ (a h y) * j g') ∂μ') ∂ν := by
      conv_lhs => rw [← hν h]
      rw [lintegral_map (hmeas f hf) (a_meas h)]
    rw [e]
    have hS' : ∀ᵐ y ∂ν, S (a h y) := by
      refine ae_of_ae_map (p := S) (a_meas h).aemeasurable ?_
      rw [hν h]; exact hS
    refine lintegral_congr_ae ?_
    filter_upwards [hS, hS'] with y h1 h2
    rw [← key f (h * s₀ y) _ (by rw [a_mul, hs₀' y h1, hs₀' _ h2])]
    simp only [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g => a g x₀) '' K) := hK.image a_cont
    have hC : IsCompact (j ⁻¹' (K⁻¹ * K)) := hj.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, hint _ (measurable_one.indicator hKm)]
    have hle : ∀ᵐ y ∂ν, ∫⁻ g', K.indicator (1 : G → ℝ≥0∞) (s₀ y * j g') ∂μ' ≤
        ((fun g => a g x₀) '' K).indicator (fun _ => μ' (j ⁻¹' (K⁻¹ * K))) y := by
      filter_upwards [hS] with y hy
      by_cases hyL : y ∈ (fun g => a g x₀) '' K
      · rw [Set.indicator_of_mem hyL]
        obtain ⟨b, hb, hby⟩ := hyL
        rw [key _ (s₀ y) b (by rw [hs₀' y hy]; exact hby.symm),
          ← lintegral_indicator_one hC.measurableSet]
        refine lintegral_mono fun g' => ?_
        by_cases hg : b * j g' ∈ K
        · have : g' ∈ j ⁻¹' (K⁻¹ * K) :=
            ⟨b⁻¹, by simpa using hb, b * j g', hg, by simp⟩
          simp [Set.indicator_of_mem hg, Set.indicator_of_mem this]
        · simp [Set.indicator_of_notMem hg]
      · rw [Set.indicator_of_notMem hyL]
        refine le_of_eq ((lintegral_congr fun g' => ?_).trans lintegral_zero)
        refine Set.indicator_of_notMem (fun hg => hyL ⟨_, hg, ?_⟩) _
        have : j g' ∈ {g | a g x₀ = x₀} := hr ▸ Set.mem_range_self g'
        change a (s₀ y * j g') x₀ = y
        rw [a_mul, this, hs₀' y hy]
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_indicator_const hL.measurableSet]
    exact ENNReal.mul_lt_top hC.measure_lt_top hL.measure_lt_top
  refine ⟨Measure.haarScalarFactor m μ, fun s hs f hf => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul m μ
  calc ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν
      = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hS] with y hy
        exact key f _ _ (by rw [hs.2 y hy, hs₀' y hy])
    _ = ∫⁻ g, f g ∂m := (hint f hf).symm
    _ = _ := by
        conv_lhs => rw [e]
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem quadric_haar : ∀ (P Q P' Q' : ℕ) (β : ℝ) (x₀ : Sp P Q) (j : UpqT P' Q' →* UpqT P Q)
    (ν : Measure (Sp P Q)) (μ : Measure (UpqT P Q)) (μ' : Measure (UpqT P' Q')),
    Topology.IsClosedEmbedding j → Set.range j = {g | act g x₀ = x₀} →
    IsFiniteMeasureOnCompacts ν → (∀ᵐ y ∂ν, qf y = β) → (∀ g : UpqT P Q, ν.map (act g) = ν) →
    μ.IsHaarMeasure → μ'.IsHaarMeasure →
    ∃ κ : ℝ≥0, ∀ s : Sp P Q → UpqT P Q, IsSection β x₀ s →
      ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  intro P Q P' Q' β x₀ j ν μ μ' hj hr h1 hS hν h2 h3
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  refine exists_const act (fun g h x => ?_) (fun x => Matrix.one_mulVec x) (fun g => ?_) x₀ ?_
    (fun y => qf y = β) j ν μ μ' hj hr hS hν
  · exact (Matrix.mulVec_mulVec x (UpqT.mat g) (UpqT.mat h)).symm
  · exact (continuous_const.matrix_mulVec continuous_id).measurable
  · exact GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

end GlobalTheory.QuadricHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrthogonalComplementUnitaryEmbeddingConjBlock
section
noncomputable section

namespace GlobalTheory.CompactDualQuot.PerpConj

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem jpq_apply (a b : Fin P ⊕ Fin Q) :
    Formalism.UG.Jpq P Q a b = if a = b then (sg a : ℂ) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, sg, Matrix.one_apply]
  all_goals (split_ifs <;> simp)

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

theorem herm_swap (x y : Sp P Q) : herm y x = star (herm x y) := by
  simp [herm_eq_sum, mul_comm]

theorem gram_apply (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i l : Fin P ⊕ Fin Q) :
    (uᴴ * Formalism.UG.Jpq P Q * u) i l = herm (fun a => u a l) (fun a => u a i) := by
  simp only [Matrix.mul_apply, jpq_apply, herm_eq_sum, conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem herm_single (a b : Fin P ⊕ Fin Q) :
    herm (Pi.single b 1 : Sp P Q) (Pi.single a 1) = if a = b then (sg a : ℂ) else 0 := by
  rw [herm_eq_sum, Finset.sum_eq_single a]
  · by_cases h : a = b <;> simp [h]
  · intro c _ hc; simp [hc]
  · simp

theorem perp_conj : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ →
    ∀ (x₀ : Sp P Q) (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q),
    qf x₀ = sg (e none) → IsPerpEmb x₀ A j →
    ∃ g₀ : UpqT P Q, act g₀ (baseVec e) = x₀ ∧ ∀ g, j g = g₀ * j₀ g * g₀⁻¹ := by
  intro P Q P' Q' e he j₀ hj₀ x₀ A j hx ⟨h1, h2, h3⟩
  let u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    Matrix.of fun a l => (e.symm l).elim (x₀ a) (fun b => A a b)
  have un : ∀ a, u a (e none) = x₀ a := fun a => by simp [u]
  have us : ∀ a b, u a (e (some b)) = A a b := fun a b => by simp [u]
  have cn : (fun a => u a (e none)) = x₀ := funext un
  have cs : ∀ b, (fun a => u a (e (some b))) = A *ᵥ Pi.single b 1 := fun b => by
    funext a; simp [us]
  have hu : u ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    ext i l
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [gram_apply, jpq_apply]
    rcases i with _ | i <;> rcases l with _ | l
    · rw [cn, herm_self, hx, if_pos rfl]
    · rw [cn, cs, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp)]
    · rw [cn, cs, herm_swap, (h2 _).2 ⟨_, rfl⟩, if_neg (by simp), star_zero]
    · rw [cs, cs, h1, herm_single, he i]
      simp
  obtain ⟨g₀, hg₀⟩ := hu
  refine ⟨g₀, ?_, fun g => ?_⟩
  · funext a
    simp [act, baseVec, hg₀, un]
  · rw [eq_mul_inv_iff_mul_eq]
    apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
    change UpqT.mat (j g) * UpqT.mat g₀ = UpqT.mat g₀ * UpqT.mat (j₀ g)
    rw [hg₀]
    obtain ⟨b1, b2, b3, b4⟩ := hj₀ g
    ext a l
    obtain ⟨l, rfl⟩ := e.surjective l
    rw [Matrix.mul_apply (M := u), ← e.sum_comp, Fintype.sum_option]
    rcases l with _ | l
    · have := congrFun (h3 g).1 a
      simp only [b1, b3, un, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← this]
      simp [act, Matrix.mul_apply, Matrix.mulVec, dotProduct, un]
    · have := congrFun ((h3 g).2 (Pi.single l 1)) a
      simp only [b2, b4, us, mul_zero, zero_add]
      simp only [act, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, us] using this

end GlobalTheory.CompactDualQuot.PerpConj
end
end

