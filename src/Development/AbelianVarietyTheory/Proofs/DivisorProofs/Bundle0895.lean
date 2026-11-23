module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealFormSpans
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.RealFormSpan

theorem jm_sq (n : ℕ) (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem jm_ct (n : ℕ) (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem inG_re (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (1/2 : ℂ) = 1/2 := by simp
  rw [hs]
  module

theorem inG_im (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.conj_I]
  rw [hs]
  module

end GlobalTheory.RealFormSpan

open GlobalTheory.RealFormSpan in
theorem GlobalTheory.realForm_spans : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [AddCommGroup W] [Module ℂ W] (u : Fin n → Fin n → W), (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∑ a, ∑ b, X a b • u a b = 0) → ∀ a b, u a b = 0 := by
  intro n ε W _ _ u h a b
  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] W :=
    { toFun := fun X => ∑ a, ∑ b, X a b • u a b
      map_add' := by intro X Y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c X; simp [Finset.smul_sum, smul_smul] }
  have hZ : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = (1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)
      + Complex.I • ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
    intro Z
    rw [smul_smul]
    have : Complex.I * (-Complex.I / 2) = (1/2 : ℂ) := by
      have := Complex.I_mul_I; linear_combination (-1/2:ℂ) * this
    rw [this, smul_sub, smul_add]
    rw [show ((1/2 : ℂ) • Z - (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε) + ((1/2:ℂ) • Z + (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε)))
      = ((1/2 : ℂ) + 1/2) • Z by rw [add_smul]; abel]
    norm_num
  have hf : ∀ Z, f Z = 0 := by
    intro Z
    have e1 := h _ (inG_re n ε Z)
    have e2 := h _ (inG_im n ε Z)
    change f _ = 0 at e1 e2
    rw [hZ Z, map_add (f := _), e1, map_smul, e2, smul_zero, add_zero]
  have := hf (Matrix.single a b 1)
  simpa [f, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroCentralizerParabolicCosetStabilize
section
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc.StabIndex

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def bdiag (e : ι ≃ Fin a ⊕ Fin b) (A : Matrix ι ι K) : Matrix ι ι K :=
  Matrix.of fun i j => if side e i = side e j then A i j else 0

theorem bdiag_mul (e : ι ≃ Fin a ⊕ Fin b) {A B : Matrix ι ι K}
    (hA : A.BlockTriangular (side e)) (hB : B.BlockTriangular (side e)) :
    bdiag e (A * B) = bdiag e A * bdiag e B := by
  ext i j
  simp only [bdiag, Matrix.of_apply, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : side e i = side e k
    · rw [if_pos hik, if_pos (hik.symm.trans hij)]
    · rw [if_neg hik, zero_mul]
      rcases lt_or_gt_of_ne (Ne.symm hik) with h | h
      · rw [hA h, zero_mul]
      · rw [hB (hij ▸ h), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : side e i = side e k
    · rw [if_neg (fun h => hij (hik.trans h)), mul_zero]
    · rw [if_neg hik, zero_mul]

theorem bdiag_one (e : ι ≃ Fin a ⊕ Fin b) : bdiag e (1 : Matrix ι ι K) = 1 := by
  ext i j
  simp only [bdiag, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2 <;> simp_all

theorem bdiag_of_levi (e : ι ≃ Fin a ⊕ Fin b) {g : GL ι K} (hg : g ∈ blockLevi e) :
    bdiag e (g : Matrix ι ι K) = g := by
  ext i j
  simp only [bdiag, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have h1 : (g : Matrix ι ι K).BlockTriangular (side e) := hg.1
    have h2 : (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i)) := hg.2
    rcases lt_or_gt_of_ne (Ne.symm h) with h' | h'
    · exact (h1 h').symm
    · exact (h2 (show OrderDual.toDual (side e j) < OrderDual.toDual (side e i) from h')).symm

theorem uMat_blockTriangular (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) :
    (uMat e X).BlockTriangular (side e) := by
  intro i j hij
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  simp only [side] at hij
  rcases hi : e i with x | x <;> rcases hj : e j with y | y <;> simp_all
  all_goals exact absurd hij (by decide)

theorem bdiag_uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) :
    bdiag e (uMat e X) = 1 := by
  ext i j
  simp only [bdiag, uMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.of_apply,
    Matrix.one_apply]
  split_ifs with hs hij hij
  · subst hij
    generalize e i = u
    rcases u with x | x <;> simp
  · have h' : e i ≠ e j := e.injective.ne hij
    simp only [side] at hs
    revert hs h'
    generalize e i = u
    generalize e j = v
    rcases u with x | x <;> rcases v with y | y <;> simp_all
  · exact absurd (by rw [hij]) hs
  · rfl

section Top

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {a b : ℕ}

def bdiagHom (e : ι ≃ Fin a ⊕ Fin b) : blockPar (K := K) e →* GL ι K where
  toFun p := ⟨bdiag e (p : GL ι K), bdiag e (((p : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← bdiag_mul e p.2 ((blockPar e).inv_mem p.2)]; simp [bdiag_one],
    by rw [← bdiag_mul e ((blockPar e).inv_mem p.2) p.2]; simp [bdiag_one]⟩
  map_one' := Units.ext (by simp [bdiag_one])
  map_mul' p q := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact bdiag_mul e p.2 q.2)

theorem continuous_bdiag (e : ι ≃ Fin a ⊕ Fin b) : Continuous (bdiag (K := K) e) :=
  continuous_matrix fun i j => by
    by_cases h : side e i = side e j
    · simp only [bdiag, Matrix.of_apply, if_pos h]
      exact continuous_id.matrix_elem i j
    · simp only [bdiag, Matrix.of_apply, if_neg h]
      exact continuous_const

theorem continuous_bdiagHom (e : ι ≃ Fin a ⊕ Fin b) : Continuous (bdiagHom (K := K) e) := by
  refine Units.continuous_iff.2 ⟨(continuous_bdiag e).comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
  show Continuous fun p : blockPar (K := K) e => bdiag e (((p : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)
  exact (continuous_bdiag e).comp (Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val))

theorem isClosed_blockPar (e : ι ≃ Fin a ⊕ Fin b) (h0 : IsClosed ({0} : Set K)) :
    IsClosed (blockPar (K := K) e : Set (GL ι K)) := by
  have : (blockPar (K := K) e : Set (GL ι K)) = ⋂ i, ⋂ j, ⋂ (_ : side e j < side e i),
      {g : GL ι K | (g : Matrix ι ι K) i j ∈ ({0} : Set K)} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rfl
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    h0.preimage (Units.continuous_val.matrix_elem i j)

end Top

theorem relIndex_ne_zero_of_subset_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] {W S : Subgroup G} (hW : IsOpen (W : Set G)) {Q : Set G} (hQ : IsCompact Q)
    (hS : (S : Set G) ⊆ Q) : W.relIndex S ≠ 0 := by
  set C := S.topologicalClosure
  have hCQ : (C : Set G) ⊆ Q := by
    rw [Subgroup.topologicalClosure_coe]; exact closure_minimal hS hQ.isClosed
  have hC : IsCompact (C : Set G) := hQ.of_isClosed_subset S.isClosed_topologicalClosure hCQ
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hWo : IsOpen ((W.subgroupOf C : Subgroup C) : Set C) := by
    rw [Subgroup.coe_subgroupOf]; exact hW.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo
  have h1 : W.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  exact h1 (Subgroup.relIndex_eq_zero_of_le_right S.le_topologicalClosure h)

theorem relIndex_twCent_inf_ne_zero : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b) (γ : GL ι K),
  GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ≤ GlobalTheory.OrbDesc.blockLevi e →
  ∀ K' : Subgroup (GL ι K), IsOpen (K' : Set (GL ι K)) → IsCompact (K' : Set (GL ι K)) →
  ∀ x ∈ GlobalTheory.OrbDesc.blockPar e,
    (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ (GlobalTheory.OrbDesc.blockPar e ⊓ K').map (MulAut.conj x).toMonoidHom).relIndex
      (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓
        ((GlobalTheory.OrbDesc.blockPar e ⊓ K') ⊔ GlobalTheory.OrbDesc.blockUni e).map (MulAut.conj x).toMonoidHom) ≠ 0 := by
  intro K _ _ _ _ ι _ _ a b e γ hT K' hK'o hK'c x hx
  set T := GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ
  set P := blockPar (K := K) e
  set cx := (MulAut.conj x).toMonoidHom
  set W := K'.map cx
  set S := T ⊓ ((P ⊓ K') ⊔ blockUni e).map cx
  set A := T ⊓ (P ⊓ K').map cx
  have hTP : T ≤ P := hT.trans inf_le_left
  have hWmem : ∀ g, g ∈ W ↔ x⁻¹ * g * x ∈ K' := fun g => by
    simp only [W, cx]; rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hWo : IsOpen (W : Set (GL ι K)) := by
    have : (W : Set (GL ι K)) = (fun g => x⁻¹ * g * x) ⁻¹' (K' : Set (GL ι K)) := Set.ext hWmem
    rw [this]; exact hK'o.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hSWA : W ⊓ S ≤ A := by
    rintro g ⟨hgW, hgT, -⟩
    refine ⟨hgT, Subgroup.mem_map_equiv.2 ?_⟩
    rw [MulAut.conj_symm_apply]
    exact ⟨P.mul_mem (P.mul_mem (P.inv_mem hx) (hTP hgT)) hx, (hWmem g).1 hgW⟩
  have key : W.relIndex S ≠ 0 := by
    by_cases h0 : IsClosed ({0} : Set K)
    · haveI : T1Space K := IsTopologicalAddGroup.t1Space K h0
      haveI : T2Space (GL ι K) := Units.isEmbedding_embedProduct.t2Space
      have hPc : IsClosed (P : Set (GL ι K)) := isClosed_blockPar e h0
      set π := bdiagHom (K := K) e
      have hWc : IsCompact (W : Set (GL ι K)) := by
        have : (W : Set (GL ι K)) = (fun g => x * g * x⁻¹) '' (K' : Set (GL ι K)) := rfl
        rw [this]; exact hK'c.image ((continuous_const.mul continuous_id).mul continuous_const)
      have hQ : IsCompact (π '' {p : P | (p : GL ι K) ∈ W}) :=
        (hPc.isClosedEmbedding_subtypeVal.isCompact_preimage hWc).image (continuous_bdiagHom e)
      refine relIndex_ne_zero_of_subset_compact hWo hQ ?_
      rintro s ⟨hsT, hsmap⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hsmap
      set L' := (P ⊓ K').subgroupOf P
      have hZ : (P ⊓ K') ⊔ blockUni e ≤ ((L'.map π).comap π).map P.subtype := by
        refine sup_le ?_ ?_
        · intro g hg
          exact ⟨⟨g, hg.1⟩, ⟨⟨g, hg.1⟩, hg, rfl⟩, rfl⟩
        · rintro g ⟨X, rfl⟩
          have hgP : uHom e X ∈ P := uMat_blockTriangular e X.toAdd
          refine ⟨⟨_, hgP⟩, ?_, rfl⟩
          show π ⟨_, hgP⟩ ∈ L'.map π
          have : π ⟨_, hgP⟩ = 1 := Units.ext (bdiag_uMat e X.toAdd)
          rw [this]; exact (L'.map π).one_mem
      obtain ⟨p, hp, hpy⟩ := hZ hy
      obtain ⟨l, hl, hlp⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hp)
      set px : P := ⟨x, hx⟩
      refine ⟨px * l * px⁻¹, ?_, ?_⟩
      · show x * (l : GL ι K) * x⁻¹ ∈ W
        rw [hWmem]
        simpa [mul_assoc] using (Subgroup.mem_subgroupOf.1 hl).2
      · have hs : cx y ∈ P := hTP hsT
        have e1 : px * p * px⁻¹ = ⟨cx y, hs⟩ :=
          Subtype.ext (by simp [cx, px, ← hpy, MulAut.conj_apply])
        rw [map_mul, map_mul, hlp, ← map_mul, ← map_mul, e1]
        exact Units.ext (bdiag_of_levi e (hT hsT))
    · have hI : (⊥ : Ideal K).closure = ⊤ := by
        rcases Ideal.eq_bot_or_top (⊥ : Ideal K).closure with h | h
        · exfalso
          apply h0
          have h' := congrArg (fun I : Ideal K => (I : Set K)) h
          have : closure ({0} : Set K) = {0} := by
            simpa only [Ideal.coe_closure, Submodule.bot_coe] using h'
          exact closure_eq_iff_isClosed.mp this
        · exact h
      have hsp0 : ∀ y : K, (0 : K) ⤳ y := fun y => by
        rw [specializes_iff_mem_closure]
        have : y ∈ (⊥ : Ideal K).closure := hI ▸ Submodule.mem_top
        have h2 : y ∈ (((⊥ : Ideal K).closure : Ideal K) : Set K) := this
        simpa only [Ideal.coe_closure, Submodule.bot_coe] using h2
      have hsp : ∀ c y : K, c ⤳ y := fun c y => by
        have := (hsp0 (y - c)).map (show Continuous (fun z : K => z + c) from continuous_id.add continuous_const)
        simpa using this
      have hspM : ∀ A B : Matrix ι ι K, A ⤳ B := fun A B =>
        specializes_pi.2 fun i => specializes_pi.2 fun j => hsp _ _
      have hspG : ∀ g h : GL ι K, g ⤳ h := fun g h => by
        rw [← Units.isEmbedding_embedProduct.isInducing.specializes_iff]
        simp only [Units.embedProduct_apply]
        exact specializes_prod.2 ⟨hspM _ _, (hspM _ _).map MulOpposite.continuous_op⟩
      have hall : ∀ g, g ∈ W := fun g => (hspG g 1).mem_open hWo W.one_mem
      rw [Subgroup.relIndex_eq_one.mpr (fun g _ => hall g)]
      exact one_ne_zero
  intro h
  apply key
  rw [← Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_eq_zero_of_le_left hSWA h

end GlobalTheory.OrbDesc.StabIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjLToLiftReal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftResInj

theorem resInjL_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.models_inf → RecTie.ResInjL (RecTie.toLiftReal R F tupT hm hTop hinj) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hθ i w hw h0
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w
  have hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A)) _ _ := (Mult.mem_multT _ _ _ _ w).1 hw
  have hT : U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
      have e := LinearMap.congr_fun h0 (PiTensorProduct.tprod ℂ v)
      have e2 : w (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
      rw [PiTensorProduct.map_tprod] at e2
      show (PiTensorProduct.lift.symm w : MMap (R.MW i (sg0 D A))) (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0
      exact e2)
  have e3 : PiTensorProduct.lift U = w := LinearEquiv.apply_symm_apply _ w
  rw [← e3, hT]
  exact map_zero _

end GlobalTheory.LiftResInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZero
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem eq_zero_of_rigid_of_locally_zero : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 →
      (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
        GlobalTheory.CechPic.pull (A ◁ z).left c = 0) → c = 0 := by
  intro S A T _ hA c h₀ loc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hf := _root_.GlobalTheory.PicGlue.fnBij_snd S A T hA
  refine (cls_eq_zero_iff hL).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hL (snd A T).left
    (lift (1 : T ⟶ A) (𝟙 T)).left ?_ (GlobalTheory.CubeGlue.surjective_restrict _ fun V ↦ ?_)
    ((cls_eq_zero_iff (pull_isLB hL _)).1 h₀) fun p ↦ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · exact (ConcreteCategory.isIso_iff_bijective _).2 (hf V)
  · obtain ⟨Z, z, hz, hp, h⟩ := loc p
    obtain ⟨hw, hr⟩ := GlobalTheory.whiskerLeft_isOpenImmersion_range S A T Z z hz
    refine ⟨z.left.opensRange, hp, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    obtain ⟨m, hm⟩ : ∃ m : ((snd A T).left ⁻¹ᵁ z.left.opensRange).toScheme ⟶ (A ⊗ Z).left,
        m ≫ (A ◁ z).left = ((snd A T).left ⁻¹ᵁ z.left.opensRange).ι :=
      ⟨IsOpenImmersion.lift _ _ (by
        rw [Scheme.Opens.range_ι]
        exact fun x hx ↦ (hr x).2 hx), IsOpenImmersion.lift_fac _ _ _⟩
    rw [cls_pull hL, ← hm, pull_comp, h, map_zero]

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OActFinEt

variable {S : Scheme.{0}} {O : Type} [CommRing O] {A : Over S} [GrpObj A]

theorem act_zero (act : OAct O A) : act.act 0 = 1 :=
  mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one, ← act.add, add_zero])

theorem act_natCast (act : OAct O A) : ∀ n : ℕ, act.act (n : O) = 𝟙 A ^ n
  | 0 => by rw [Nat.cast_zero, act_zero, pow_zero]
  | n + 1 => by rw [Nat.cast_succ, act.add, act_natCast act n, act.one, pow_succ]

theorem exists_natCast_dvd {E : Type} [Field E] [NumberField E] (b : 𝓞 E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ b ∣ (n : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ) :
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 →
      IsFinite (act.act b).left ∧ Etale (act.act b).left ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  intro hA hg b hb
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  obtain ⟨n, hn0, b', hb'⟩ := exists_natCast_dvd b hb
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h1 : act.act b ≫ act.act b' = 𝟙 A ^ n := by rw [← act.mul, ← hb', act_natCast]
  have h2 : act.act b' ≫ act.act b = 𝟙 A ^ n := by rw [← act.mul, mul_comm, ← hb', act_natCast]
  haveI := act.hom b
  haveI := act.hom b'
  haveI hF : IsFinite (𝟙 A ^ n).left := GrpTangent.isFinite_id_pow A hu
  haveI hE : Etale (𝟙 A ^ n).left := GrpTangent.etale_id_pow A hu
  haveI : IsSeparated A.hom := inferInstance
  have hsep : ∀ f : A ⟶ A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left A.hom
  haveI := hsep (act.act b')
  haveI : IsFinite ((act.act b).left ≫ (act.act b').left) := by rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (act.act b).left := IsFinite.of_comp _ (act.act b').left
  haveI : FormallyUnramified ((act.act b).left ≫ (act.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (act.act b).left := FormallyUnramified.of_comp _ (act.act b').left
  haveI : Flat (act.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((act.act b).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (act.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ act.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEt
end

