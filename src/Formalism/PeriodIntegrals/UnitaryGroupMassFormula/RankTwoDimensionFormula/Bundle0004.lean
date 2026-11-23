module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAUni
section
namespace PI.UnitaryDimensionFormula

open Matrix

section Core

variable {F : Type} [Field F] {k : ℕ}

theorem uniA_mul_diag (A B : Matrix (Fin k) (Fin k) F) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  first | exact UpperTheory.Reformulated.B.Qh23.uniA_mul_diag .. | (apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB i | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F

theorem uniA_tri (x : GL (Fin k) F) (hx : ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0) :
    (x : Matrix (Fin k) (Fin k) F).BlockTriangular id := fun i j h => hx i j h

theorem uniA_mul (x y : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x)
    (hy : Formalism.L2.SG.GGMirabolic.IsUni k y) : Formalism.L2.SG.GGMirabolic.IsUni k (x * y) := by
  have tx := uniA_tri x hx.2
  have ty := uniA_tri y hy.2
  have txy : ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F)).BlockTriangular id :=
    tx.mul ty
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · rw [Units.val_mul, uniA_mul_diag _ _ tx ty, hx.1 i, hy.1 i, one_mul]
  · rw [Units.val_mul]; exact txy h

theorem uniA_inv (x : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x) :
    Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹ := by
  have tx := uniA_tri x hx.2
  have : Invertible (x : Matrix (Fin k) (Fin k) F) := Units.invertible x
  have tinv : ((x : Matrix (Fin k) (Fin k) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular tx
  have hc : ((x⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (x : Matrix (Fin k) (Fin k) F)⁻¹ :=
    Matrix.coe_units_inv x
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · have h1 : ((x : Matrix (Fin k) (Fin k) F)⁻¹ * (x : Matrix (Fin k) (Fin k) F)) i i = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq]
    rw [uniA_mul_diag _ _ tinv tx, hx.1 i, mul_one] at h1
    rw [hc]; exact h1
  · rw [hc]; exact tinv h

end Core

theorem uniSub : UniSub := by
  intro F _ k x y hx hy
  exact ⟨uniA_mul x y hx hy, uniA_inv x hx⟩

end PI.UnitaryDimensionFormula
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

def hrow (x : Fin n → A) : Fin n → A := fun q => ∑ p, σ (x p) * J p q

def sMat (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  1 + ∑ i, ∑ j, ((C - 1) i j • Matrix.vecMulVec (b i) (hrow σ J (bs j)) +
    (D - 1) i j • Matrix.vecMulVec (bs i) (hrow σ J (b j)))

def IsSplitFrame (ε : A) (b bs : Fin k → Fin n → A) : Prop :=
  ε * ε = ε ∧ ε * σ ε = 0 ∧ (∀ i, b i = ε • b i) ∧ (∀ i, bs i = σ ε • bs i) ∧
    ∀ i j, Formalism.UG.hform σ J (bs i) (b j) = if i = j then ε else 0

end Alg

def IdxDAlg : Prop :=
  ∀ (A : Type) [CommRing A] (σ : A →+* A) (n k : ℕ) (J : Matrix (Fin n) (Fin n) A) (ε : A)
    (b bs : Fin k → Fin n → A), (∀ a, σ (σ a) = a) → Formalism.UG.IsHerm σ J → IsSplitFrame σ J ε b bs →
    (∀ (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A),
      (∀ j, Formalism.UG.hform σ J (b j) y = 0 ∧ Formalism.UG.hform σ J (bs j) y = 0) → sMat σ J b bs C D *ᵥ y = y) ∧
    (∀ C₁ D₁ C₂ D₂ : Matrix (Fin k) (Fin k) A,
      sMat σ J b bs C₁ D₁ * sMat σ J b bs C₂ D₂ = sMat σ J b bs (C₁ * C₂) (D₁ * D₂)) ∧
    (∀ C D : Matrix (Fin k) (Fin k) A, ε • (C - 1) = 0 → σ ε • (D - 1) = 0 → sMat σ J b bs C D = 1) ∧
    ∀ C C' : Matrix (Fin k) (Fin k) A, C' * C = 1 →
      Formalism.UG.cT σ (sMat σ J b bs C (C'.map σ)ᵀ) * J * sMat σ J b bs C (C'.map σ)ᵀ = J

def EgProp (F : Type) [Field F] [NumberField F] (g : ℕ) (e : Af F) : Prop :=
  e ∈ Formalism.UG.intAd F ∧ e * e = e ∧
    (∃ t ∈ Formalism.UG.intAd F, 1 - e = (g : Af F) * t) ∧
    ∀ c ∈ Formalism.UG.intAd F, ∃ y ∈ Formalism.UG.intAd F, e * (1 + (g : Af F) * c) * y = e

def IdxDAd : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ), ∃ e : Af F, EgProp F g e

def IdxDJacE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : ℕ)
    (e : Af F), EgProp F g e →
    ∀ m ∈ IntAf F E, ∃ y ∈ IntAf F E,
      ((1 : E) ⊗ₜ[F] e) * (1 + (g : E ⊗[F] Af F) * m) * y = (1 : E) ⊗ₜ[F] e

def IdxDInt : Prop :=
  ∀ I : AutInst, (∀ x ∈ I.Lf, ∀ y ∈ I.Lf, hA I x y ∈ IntAf I.F I.E) ∧
    ∀ c ∈ IntAf I.F I.E, sigA I c ∈ IntAf I.F I.E

def fixV {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Set (VA X.B.I) :=
  Set.range (fun a => incl X.B.I (X.eR a)) ∪ Set.range (fun a => incl X.B.I (X.fR a)) ∪
    {X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)}

abbrev JA (I : AutInst) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def epsX {D : D7} (X : HidaSetting D) (e : Af X.B.I.F) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * X.ew

def IdxDFrame : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∃ b bs : Fin D.R.k → VA X.B.I,
      IsSplitFrame (sigA X.B.I) (JA X.B.I) (epsX X e) b bs ∧
      (∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf) ∧
      (∀ i, ∀ y ∈ fixV X u, hA X.B.I (b i) y = 0 ∧ hA X.B.I (bs i) y = 0) ∧
      ∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (bs i) (X.bw j) - if i = j then X.ew else 0) ∧
        ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0)

def IdxDMat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (TR : TypedRed X) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∀ A : Iof TR, ∃ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      C' * C = 1 ∧ (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) ∧
      ∀ v i j, resT TR v (epsX X e * C i j) = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j

def IdxDLevi : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (TR : TypedRed X) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
    ∀ b bs : Fin D.R.k → VA X.B.I, IsSplitFrame (sigA X.B.I) (JA X.B.I) (epsX X e) b bs →
      (∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf) →
      (∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (bs i) (X.bw j) - if i = j then X.ew else 0) ∧
        ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0)) →
      ∀ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), C' * C = 1 →
        (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) →
        ∀ v i j, resT TR v (hA X.B.I (X.bwd i)
            (sMat (sigA X.B.I) (JA X.B.I) b bs C (C'.map (sigA X.B.I))ᵀ *ᵥ X.bw j)) =
          resT TR v (epsX X e * C i j)

def IdxDSig : Prop :=
  ∀ I : AutInst, (∀ a, sigA I (sigA I a) = a) ∧ Formalism.UG.IsHerm (sigA I) (JA I)

end PI.UnitaryDimensionFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.UnitriangularReductionOfMemLevel
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  calc TR.res v ⟨X.ew, X.ew_int⟩
      = TR.res v ⟨X.ew * ((1 : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
          (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (1 : IntAf X.B.I.F X.B.I.E).2⟩ := by
        congr 1
        ext
        simp
    _ = TR.res v 1 := TR.res_ew v 1
    _ = 1 := map_one _

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  by_cases hb : b
  · rw [if_pos hb] at hZ ⊢
    have hmem : c - X.ew ∈ IntAf X.B.I.F X.B.I.E := sub_mem hc X.ew_int
    have hk := (TR.res_ker ⟨c - X.ew, hmem⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v
    have e : (⟨c - X.ew, hmem⟩ : IntAf X.B.I.F X.B.I.E) = ⟨c, hc⟩ - ⟨X.ew, X.ew_int⟩ := rfl
    rw [e, map_sub, res_ew_one, sub_eq_zero] at hk
    exact hk
  · rw [if_neg hb, sub_zero] at hZ
    rw [if_neg hb]
    exact (TR.res_ker ⟨c, hc⟩).mpr (Z_smul X.B.I X.B.g X.ew_int hZ) v

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  obtain ⟨hK, -, -, hc3⟩ := hk
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  have hbb : ∀ i j : Fin D.R.k, i ≠ j → ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.bw j)) := by
    intro i j hij
    have h := X.bw_dual i j
    rwa [if_neg hij, sub_zero] at h
  have key : ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
    intro i j hji
    have hmv : X.B.I.fmat x *ᵥ X.bw j ∈ X.B.I.Lf := K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1
    have hc : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
      hA_int X.B.I (hbwd i) hmv
    have hsub : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤ Qs X.B.I X.B.g (X.bwd i) :=
      le_trans (Mo_mono X.B.I (Set.union_subset_union_right _
          (Set.image_mono (lt_sub (Fin.le_iff_val_le_val.mp hji)))))
        (Mb_Q X.B.I X.B.g X.e0 X.bw X.bwd hbwd (fun i a => dual_beta_reference_congruence i a) hbb i)
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) := hsub (hc3 j)
    have hZ : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
      have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - (if i = j then X.ew else 0) =
          (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) +
            hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
        ring
      rw [e]
      exact Z_add X.B.I X.B.g (X.bw_dual i j) h2
    show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
    rw [resT_of_mem TR v hc]
    exact res_of_Z_delta TR v hc (i = j) hZ
  show (∀ i : Fin D.R.k, ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i i = 1) ∧
    ∀ i j : Fin D.R.k, j < i →
      ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
  rw [levi_coe TR hx v]
  exact ⟨fun i => by rw [key i i le_rfl, if_pos rfl],
    fun i j hji => by rw [key i j hji.le, if_neg (ne_of_lt hji).symm]⟩

end K2iff

end PI.UnitaryDimensionFormula.NormCutK
end
end

