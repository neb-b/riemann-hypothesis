module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBound
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedCount
open NumberField GlobalTheory.LatCount

theorem weighted_count : ∀ (D : D7) (κ : Type) [Fintype κ] (L : ℕ), 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : κ → ℝ, (∀ k, 0 < s k) → ∑' η : κ → D.host.E,
      {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)}.indicator
        (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^ N)⁻¹)) η ≤
      ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
  intro D κ _ L hL
  classical
  obtain ⟨C₀, hC₀, hCb⟩ := exists_repr_le D
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let P := κ × ι
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨2 * Fintype.card P, (1 + 2 * C₀ * L) ^ Fintype.card P, by positivity, fun s hs => ?_⟩
  set S := {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)} with hS
  rw [← tsum_subtype S]
  let b : P → ℝ := fun p => 1 / (C₀ * L * s p.1)
  have hb : ∀ p, 0 < b p := fun p => by have := hs p.1; positivity
  let kap : (κ → D.host.E) → P → ℤ := fun η p =>
    ⌊(integralBasis D.host.E).repr ((L : D.host.E) * η p.1) p.2⌋
  have hint : ∀ η ∈ S, ∀ p : P, (((kap η p : ℤ) : ℚ)) =
      (L : ℚ) * (integralBasis D.host.E).repr (η p.1) p.2 := by
    intro η hη p
    rw [← repr_nat_mul]
    exact repr_int (hη p.1) p.2
  let G : (P → ℤ) → ℝ≥0∞ := fun z => ∏ p, ENNReal.ofReal (((1 + b p * |((z p : ℤ) : ℝ)|) ^ 2)⁻¹)
  have hpt : ∀ η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η) := by
    rintro ⟨η, hη⟩
    show ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η)
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k := ⟨_, rfl⟩
    rw [← hT]
    have hterm : ∀ k, 0 ≤ (∑ τ, ‖tauE D τ (η k)‖) / s k := fun k =>
      div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hs k).le
    have hT0 : 0 ≤ T := by rw [hT]; exact Finset.sum_nonneg fun k _ => hterm k
    have hkp : ∀ p : P, 1 + b p * |((kap η p : ℤ) : ℝ)| ≤ 1 + T := by
      rintro ⟨k, l⟩
      have e1 : |((kap η (k, l) : ℤ) : ℝ)| =
          L * |((integralBasis D.host.E).repr (η k) l : ℝ)| := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hint η hη (k, l))
        simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hsk := hs k
      have h1 : |((integralBasis D.host.E).repr (η k) l : ℝ)| ≤
          ∑ l', |((integralBasis D.host.E).repr (η k) l' : ℝ)| :=
        Finset.single_le_sum (f := fun l' => |((integralBasis D.host.E).repr (η k) l' : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
      have h2 := hCb (η k)
      have h3 : (∑ τ, ‖tauE D τ (η k)‖) / s k ≤ T := by
        rw [hT]
        exact Finset.single_le_sum (f := fun k => (∑ τ, ‖tauE D τ (η k)‖) / s k)
          (fun k _ => hterm k) (Finset.mem_univ k)
      have e2 : b (k, l) * |((kap η (k, l) : ℤ) : ℝ)| =
          |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) := by
        rw [e1]; simp only [b]; field_simp
      have h4 : |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) ≤
          (∑ τ, ‖tauE D τ (η k)‖) / s k := by
        rw [div_le_div_iff₀ (by positivity) hsk]
        nlinarith
      linarith
    show ENNReal.ofReal (((1 + T) ^ (2 * Fintype.card P))⁻¹) ≤
      ∏ p, ENNReal.ofReal (((1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2)⁻¹)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.prod_inv_distrib]
    apply inv_anti₀ (Finset.prod_pos fun p _ => by have := hb p; positivity)
    calc ∏ p, (1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2 ≤ ∏ _p : P, (1 + T) ^ 2 :=
          Finset.prod_le_prod₀ (fun p _ => by have := hb p; positivity)
            (fun p _ => pow_le_pow_left₀ (by have := hb p; positivity) (hkp p) 2)
      _ = (1 + T) ^ (2 * Fintype.card P) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hinj : Function.Injective (fun η : S => kap η) := by
    rintro ⟨η, hη⟩ ⟨η', hη'⟩ h
    apply Subtype.ext
    funext k
    have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    apply mul_left_cancel₀ hL0
    apply (integralBasis D.host.E).repr.injective
    ext l
    have h1 := hint η hη (k, l)
    have h2 := hint η' hη' (k, l)
    have h3 : kap η (k, l) = kap η' (k, l) := congrFun h (k, l)
    rw [repr_nat_mul, repr_nat_mul]
    rw [← h1, ← h2, h3]
  have hcard : Fintype.card ι = Module.finrank ℚ D.host.E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hbnd : ∀ p : P, 1 + 2 / b p ≤ (1 + 2 * C₀ * L) * max 1 (s p.1) := by
    intro p
    have e : 2 / b p = 2 * C₀ * L * s p.1 := by simp only [b]; field_simp
    rw [e]
    have h1 : (1 : ℝ) ≤ max 1 (s p.1) := le_max_left _ _
    have h2 : s p.1 ≤ max 1 (s p.1) := le_max_right _ _
    have : 0 ≤ 2 * C₀ * L := by positivity
    nlinarith
  calc ∑' η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
        (2 * Fintype.card P))⁻¹)
      ≤ ∑' η : S, G (kap η) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' z, G z := ENNReal.tsum_comp_le_tsum_of_injective hinj G
    _ = ∏ p : P, ∑' z : ℤ, ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹) :=
        GlobalTheory.HL.tsum_pi_prod_ennreal (X := fun _ : P => ℤ)
          (fun (p : P) (z : ℤ) => ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹))
    _ ≤ ∏ p : P, ENNReal.ofReal (1 + 2 / b p) := Finset.prod_le_prod' fun p _ => tsum_int_le (hb p)
    _ = ENNReal.ofReal (∏ p : P, (1 + 2 / b p)) :=
        (ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + 2 * C₀ * L) ^ Fintype.card P *
          ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∏ p : P, (1 + 2 / b p) ≤ ∏ p : P, ((1 + 2 * C₀ * L) * max 1 (s p.1)) :=
              Finset.prod_le_prod₀ (fun p _ => by have := hb p; positivity) (fun p _ => hbnd p)
          _ = (1 + 2 * C₀ * L) ^ Fintype.card P * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
              congr 1
              rw [Fintype.prod_prod_type]
              refine Finset.prod_congr rfl fun k _ => ?_
              show ∏ _y : ι, max 1 (s k) = _
              rw [Finset.prod_const, Finset.card_univ, hcard]

end GlobalTheory.WeightedCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]


open Classical in
def pre (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : L := if h : ∃ x, ι x = z then h.choose else 0

theorem pre_spec (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : ∃ x, ι x = z) : ι (pre ι z) = z := by
  unfold pre
  rw [dite_eq_left h]
  exact h.choose_spec

def tJ (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {m n : Type} (J : Matrix m n E) : Matrix m n L :=
  fun i j => pre ι (ι 1 * inclR (F := F) (AF F) (J i j))

def gram (σL : L →+* L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n : ℕ} (P : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL

def xm (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) :
    Matrix (Fin d) (Fin n) L →+ Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun x := ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem xm_apply (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {n d : ℕ} (PV : GL (Fin n) L) (PW : GL (Fin d) L) (x : Matrix (Fin d) (Fin n) L) :
    xm ι PV PW x = ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ).map ι := rfl

end GlobalTheory.InertLocFrame

end
end

