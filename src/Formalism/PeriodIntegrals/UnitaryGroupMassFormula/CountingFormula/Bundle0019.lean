module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LinearIndependentOfDetGram
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_comb {K V ι κ : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι → V) (A : Matrix ι κ K) (x : κ → V)
    (hx : ∀ j, x j = ∑ i, A i j • v i) : gram h x = A.conjTranspose * gram h v * A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gram, Matrix.of_apply, hx, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem linearIndependent_of_det_gram {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) (hd : (gram h x).det ≠ 0) :
    LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.mulVec (gram h x) c = 0 := by
    funext j
    have hj := congrArg (h (x j)) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
    rw [← hj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd hv
  intro i
  exact congrFun h0 i

variable {D : Formalism.BasicNotions.D7}

theorem flag_gram {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
  · simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, Fin.castSucc_ne_last]
    rw [hs (F.e j) F.z, F.z_orth j, star_zero]
  · simp [FlagG.fvec, F.z_norm]

theorem gram_pair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    gram (VS D).hT (Sum.elim F0.fvec F'.fl.fvec) = Ga T T' Z := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  subst hZ
  ext (a | a) (b | b)
  · simp [gram, Ga, flag_gram]
  · simp [gram, Ga, ZhatL, Zhat, brS]
  · simp [gram, Ga, ZhatL, Zhat, brS, Matrix.conjTranspose_apply, hs (F'.fl.fvec a)]
  · simp [gram, Ga, flag_gram]

def flagDifferenceMatrix (D : Formalism.BasicNotions.D7) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.fromBlocks 1 (-(((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))) 0
    (((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))

theorem flagDifference_comb {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    ∀ j, flagDifferenceVectors D F0 F' j = ∑ i, flagDifferenceMatrix D i j • Sum.elim F0.fvec F'.fl.fvec i := by
  intro j
  rcases j with b | b
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]

theorem det_flagDifference_matrix (D : Formalism.BasicNotions.D7) : (flagDifferenceMatrix D).det = ((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ ^ (D.R.rS + 1) := by
  rw [flagDifferenceMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

theorem star_gS (D : Formalism.BasicNotions.D7) : star ((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ = ((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ := by
  rw [star_inv₀, star_natCast]

theorem det_gram_flagDifference {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = ((Formalism.MainNotions.S.Lat.gS D : D.host.E))⁻¹ ^ (2 * (D.R.rS + 1)) * (Ga T T' Z).det := by
  rw [gram_comb (VS D).hT _ (flagDifferenceMatrix D) _ (flagDifference_comb F0 F'), gram_pair F0 F' Z hZ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_conjTranspose, det_flagDifference_matrix, star_pow, star_gS]
  ring

theorem span_flagDifferenceBasis {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range (flagDifferenceVectors D F0 F')) = UPair D F0 F' := by
  have hg : ((Formalism.MainNotions.S.Lat.gS D : D.host.E)) ≠ 0 := by
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    rw [Formalism.MainNotions.S.Lat.gS]
    exact_mod_cast mul_ne_zero h0 h1
  unfold UPair
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · simp only [flagDifferenceVectors, Sum.elim_inr]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span (Or.inr ⟨b, rfl⟩)) (Submodule.subset_span (Or.inl ⟨b, rfl⟩)))
  · rw [Submodule.span_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl b, rfl⟩
    · have h1 : F'.fl.fvec b = (Formalism.MainNotions.S.Lat.gS D : D.host.E) • flagDifferenceVectors D F0 F' (Sum.inr b) +
          flagDifferenceVectors D F0 F' (Sum.inl b) := by
        simp only [flagDifferenceVectors, Sum.elim_inr, Sum.elim_inl, smul_smul, mul_inv_cancel₀ hg, one_smul,
          sub_add_cancel]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.subset_span ⟨_, rfl⟩)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
section
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

def wPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Submodule K V1 := LinearMap.ker (h1 z)

def hPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : wPerp h1 z →ₗ⋆[K] wPerp h1 z →ₗ[K] K :=
  (h1.compl₂ (wPerp h1 z).subtype).comp (wPerp h1 z).subtype

def l0 (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Submodule (𝓞 K) (wPerp h1 z) :=
  M.comap ((wPerp h1 z).subtype.restrictScalars (𝓞 K))

def IsGlueLat (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Prop :=
  Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 M ∧ z ∈ M ∧
    ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c

def hz (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ Formalism.HermitianLatticesTheory.isom h1 ∧ σ z = z}

def stabZ (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ hz h1 z ∧ Formalism.HermitianLatticesTheory.gmap σ M = M}

def IsHzReps (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (s : Finset (Submodule (𝓞 K) V1)) : Prop :=
  (∀ M ∈ s, IsGlueLat h1 z M) ∧
    ∀ M, IsGlueLat h1 z M → ∃! M', M' ∈ s ∧ ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M

end Glue

def GlueHyp (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]
    (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ) : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram K ∧ IsFixF K F ∧ h1.IsSymm ∧ h1 z z = -((t : ℕ) : K) ∧ 0 < t ∧
    IsTotPosDef (hPerp h1 z)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

