module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  simp only [dotProduct, infE]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * _ = _ * _
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = (0 : FiniteAdeleRing (𝓞 F) F) * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem slice_schr (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    slice F (GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) Φ) y = schrInf F ψ v (slice F Φ y) := by
  funext z
  simp only [slice, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  congr 2
  · congr 1
    refine (dot_infE _ v.2).trans ?_
    congr 2
    funext i
    exact RingEquiv.apply_symm_apply _ _
  · funext i
    refine Prod.ext ?_ ?_
    · exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · exact add_zero _

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.add_apply, add_mul]

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g y • f, fun z => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, GlobalTheory.WeilM.pureA, RingEquiv.apply_symm_apply]
    exact mul_comm _ _
  | zero => exact ⟨0, fun z => rfl⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hx'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs, hs']; rfl⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨a • s, fun z => by rw [SchwartzMap.smul_apply, hs]; rfl⟩

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecInv
section
open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm


open GlobalTheory.FlagNorm in
theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormInert

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cT_aeval {K : Type} [Field K] (s : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    cT s (aeval A f) = aeval (cT s A) (f.map s) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map s)ᵀ ^ k = ((A ^ k).map s)ᵀ := by rw [← Matrix.transpose_pow, Matrix.map_pow]
    ext i j
    simp [cT, e, Algebra.algebraMap_eq_smul_one]

theorem exists_over (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  refine ⟨⟨P, hP.isPrime, fun h0 => v.ne_bot ?_⟩, HeightOneSpectrum.ext hPv.over.symm⟩
  rw [hPv.over, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem localEquiv (hU : Unr E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (w : Pl E)
    (hw : w.under (𝓞 (maximalRealSubfield E)) = v)
    (huniq : ∀ u : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v → u = w) :
    ∃ j : w.adicCompletion E ≃+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
      (∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e) ∧
      ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x) := by
  classical
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u (hu.trans hw))
  have hmain := GlobalTheory.ConjAtPlace.main E hU w
  have hσ := (hmain.2.2.2.1 hns).1
  have hinj : Function.Injective (GlobalTheory.LFun.toCompl hw) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
      (GlobalTheory.AdelicU.evalV_singleFin_self v) y
    have h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
      FiniteAdeleRing.ext _ fun u => by
        by_cases e : u.under (𝓞 (maximalRealSubfield E)) = v
        · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
          obtain rfl := huniq u e
          exact hy
        · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
            (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
          rfl
    rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]
  have hsurj := GlobalTheory.LFun.InertChart.toCompl_surjective hw
  let e := RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hw) ⟨hinj, hsurj⟩
  have hF : ∀ a, cj w (GlobalTheory.LFun.complMap hw a) = GlobalTheory.LFun.complMap hw a := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hw)) (GlobalTheory.LFun.InertChart.continuous_complMap hw)
      (funext fun x => by
        simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))
    exact fun a => congrFun this a
  have hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hw y) = GlobalTheory.LFun.toCompl hw
      (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨e.symm, fun x => e.symm_apply_eq.2 ?_, fun x => e.symm_apply_eq.2 ?_⟩
  · have h := GlobalTheory.LFun.toCompl_tmul hw 1 x
    rw [map_one, one_mul] at h
    exact h.symm
  · obtain ⟨y, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply]
    exact hcomp y

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ hU n γ hγ hell m hloc r Q hQ _ v huniq
  classical
  obtain ⟨w, hw⟩ := exists_over (E := E) v
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u w (hu.trans hw) hw)
  obtain ⟨c, hc1, hc2⟩ := hloc w hns
  obtain ⟨j, hj1, hj2⟩ := localEquiv hU v w hw (fun u hu => huniq u w hu hw)

  have hsep : γ.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val (γ⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]

  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ.val.map (algebraMap E (w.adicCompletion E)) with hA
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ.val.charpoly := Matrix.charpoly_map _ _
  have hc1' : A * c = c * A := hc1.symm
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c hAsep hc1'
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * A = 1 := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h0
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hns, Matrix.mul_one] at this
    exact this
  have hcT : cT (cj w) A = aeval A (atPl w r₀) := by
    calc cT (cj w) A = cT (cj w) A * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA, Matrix.one_mul]
  have hdiv : atPl w γ.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - atPl w m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h2 : cT (cj w) (aeval A f) * aeval A f = aeval A (atPl w m) := by
      rw [hc2, hA, aeval_map_mat]
    rw [cT_aeval, hcT, ← aeval_comp] at h2
    rw [map_sub, map_mul, h2, sub_self]

  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    ((inclBase Q k).toRingHom).comp j.toRingHom
  have hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e := by
    intro e
    change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinv : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = atPl w m + atPl w γ.val.charpoly * t := by
    rw [← ht]; ring
  refine ⟨Φ f, ?_⟩
  change Φ f * ib (Φ f) = _
  have h0 : Φ (atPl w γ.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  rw [hinv, ← map_mul, hft, map_add (f := _), map_mul, h0, zero_mul, add_zero, hΦ]

end GlobalTheory.NormInert
end
end

