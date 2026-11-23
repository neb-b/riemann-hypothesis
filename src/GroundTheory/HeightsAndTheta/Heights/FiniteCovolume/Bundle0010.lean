module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedNormSq
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem WeightedNormSq.proof (E : Type*) [Field E] [NumberField E] : WeightedNormSq.Statement E := by
  intro c hc a
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.sum_univ_two]
  simp only [weightedEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
    sq_abs, show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  rw [mul_pow, mul_pow, Real.sq_sqrt (hc w), Complex.sq_norm, Complex.normSq_apply]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem WittPartner.proof (h : HermitianForm F E W) : WittPartner.Statement h := by
  intro x₀ hx₀ hiso

  have hne : h.toSesq x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply h.nonsingular.1
    rw [h0, map_zero]
  obtain ⟨y', hy'⟩ : ∃ y', h.toSesq x₀ y' ≠ 0 := by
    by_contra hc
    exact hne (LinearMap.ext fun z => not_not.1 fun hz => hc ⟨z, hz⟩)

  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x₀ y = 1 :=
    ⟨(h.toSesq x₀ y')⁻¹ • y', by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy']⟩
  have hyx : h.toSesq y x₀ = 1 := by
    rw [← h.isSymm.eq x₀ y, hy, map_one]

  obtain ⟨a, ha_def⟩ : ∃ a, h.toSesq y y = a := ⟨_, rfl⟩
  have ha : conjHom F E a = a := by
    rw [← ha_def]
    exact h.isSymm.eq y y
  have ht : conjHom F E (a / 2) = a / 2 := by
    rw [map_div₀, ha, map_ofNat]

  have hl : ∀ z, h.toSesq (y - (a / 2) • x₀) z = h.toSesq y z - (a / 2) * h.toSesq x₀ z := by
    intro z
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, ht, smul_eq_mul]
  refine ⟨y - (a / 2) • x₀, ?_, ?_⟩
  · rw [map_sub, map_smul, hy, hiso, smul_zero, sub_zero]
  · rw [hl]
    simp only [map_sub, map_smul, smul_eq_mul, hyx, hy, hiso, ha_def]
    ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.RelIndexNeZeroAndLeOfNsmulMem
section
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

section Index

theorem relIndex_ne_zero_and_le_of_nsmul_mem {W : Type*} [AddCommGroup W]
    [Module.IsTorsionFree ℤ W] {L P : AddSubgroup W} {Q : Submodule ℤ W} [Module.Finite ℤ Q]
    (hLP : L ≤ P) (hPQ : P.toIntSubmodule ≤ Q) {n : ℕ} (hn : n ≠ 0) (hnL : ∀ y ∈ P, n • y ∈ L) :
    L.relIndex P ≠ 0 ∧ L.relIndex P ≤ n ^ finrank ℤ Q := by
  haveI : Module.Finite ℤ P.toIntSubmodule :=
    Module.Finite.of_injective (Submodule.inclusion hPQ) (Submodule.inclusion_injective hPQ)
  have key := AddSubgroup.relIndex_map_nsmul n P
  have hle : P.map (nsmulAddMonoidHom (α := W) n) ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnL y hy
  have hne : (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hn
  have hrank : finrank ℤ P.toIntSubmodule ≤ finrank ℤ Q := Submodule.finrank_mono hPQ
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hle h0), ?_⟩
  calc L.relIndex P ≤ (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P :=
        AddSubgroup.relIndex_le_of_le_left hle hne
    _ = n ^ finrank ℤ P.toIntSubmodule := key
    _ ≤ n ^ finrank ℤ Q := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hrank

end Index

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Coordinates


variable (F) in
def coordEquiv (v : Basis ι E W) : W ≃+ (ι → F ⊗[F] E) :=
  v.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (Algebra.TensorProduct.lid F E).symm.toAddEquiv)

theorem coordEquiv_apply (v : Basis ι E W) (x : W) (i : ι) :
    coordEquiv F v x i = (1 : F) ⊗ₜ[F] v.repr x i := by
  simp [coordEquiv, Algebra.TensorProduct.lid_symm_apply]

theorem coordEquiv_smul (v : Basis ι E W) (e : E) (x : W) :
    coordEquiv F v (e • x) = ((1 : F) ⊗ₜ[F] e) • coordEquiv F v x := by
  funext i
  simp only [coordEquiv_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, map_smul, Finsupp.smul_apply]

theorem pairE_coordEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x y : W) :
    pairE (gram h.toSesq v) (coordEquiv F v x) (coordEquiv F v y) = h.toSesq x y := by
  rw [sesq_eq_sum h.toSesq v x y, pairE, hermPair]
  simp only [dotProduct, mulVec, baseMatrix, Matrix.map_apply, coordEquiv_apply, conjBase_tmul,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Finset.mul_sum, ← TensorProduct.tmul_sum, Algebra.TensorProduct.lid_tmul, one_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecCoords_coordEquiv {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W) (x : W)
    (i : ι) (k : κ) : vecCoords F b (coordEquiv F v x) (i, k) = b.repr (v.repr x i) k := by
  rw [vecCoords, coordEquiv_apply, repr_one_tmul, Algebra.algebraMap_self, RingHom.id_apply]

end Coordinates

section Equivariance

variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem mulVec_coordEquiv (γ : h.unitaryGroup) (y : W) :
    unitaryMat ((unitaryPointsRationalEquivHermitian F E h v).symm γ) *ᵥ coordEquiv F v y =
      coordEquiv F v ((γ : W ≃ₗ[E] W) y) := by
  set γ' := (unitaryPointsRationalEquivHermitian F E h v).symm γ
  have h1 : unitaryPointsRationalEquiv F E (gram h.toSesq v) γ' = unitaryGroupEquivMatrix h v γ := by
    show unitaryPointsRationalEquiv F E _ (((unitaryPointsRationalEquiv F E _).trans
      (unitaryGroupEquivMatrix h v).symm).symm γ) = _
    rw [MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  have hM : (unitaryMat γ').map (Algebra.TensorProduct.lid F E) =
      LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [← unitaryGroupEquivMatrix_apply, ← h1]
    rfl
  funext i
  apply (Algebra.TensorProduct.lid F E).injective
  rw [coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul,
    show v.repr ((γ : W ≃ₗ[E] W) y) = v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) y) from rfl,
    ← LinearMap.toMatrix_mulVec_repr v v, ← hM]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, coordEquiv_apply,
    Algebra.TensorProduct.lid_tmul, one_smul]

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem adeleSplit_snd_hermitianDiagonal (γ : h.unitaryGroup) :
    (adeleSplit h v (hermitianDiagonal h v γ)).2 =
      finDiag (gram h.toSesq v) ((unitaryPointsRationalEquivHermitian F E h v).symm γ) := by
  apply unitaryCoords_injective _ _ (Module.finBasis F E)
  funext p
  simp [adeleSplit, unitaryCongr_apply, hermitianDiagonal, unitaryDiagonal, finDiag,
    unitaryCoords_unitaryMap, adeleRingEquivProd]
  have hprod (x : unitaryPoints F E (gram h.toSesq v)
      (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :
      (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v) x).2 =
        unitaryMap F E _ (AlgHom.snd F _ _) x := rfl
  rw [hprod]
  simp only [unitaryCoords_unitaryMap, Function.comp_apply]
  rfl

end Equivariance

section Lattice

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

def dictLattice (d : ℤ) (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) : AddSubgroup W :=
  (coreLattice b (gram h.toSesq v) g).comap
    ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp (DistribSMul.toAddMonoidHom W ((d : E)⁻¹)))

variable {b h v}

theorem mem_dictLattice {d : ℤ} {g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} {x : W} :
    x ∈ dictLattice b h v d g ↔ coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g :=
  Iff.rfl

theorem dictLattice_eq_iff {d : ℤ} (hd : d ≠ 0) {g g' : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} :
    dictLattice b h v d g = dictLattice b h v d g' ↔ g⁻¹ * g' ∈ coreStabilizer b (gram h.toSesq v) := by
  rw [← coreLattice_eq_iff b]
  have hsurj : Function.Surjective ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp
      (DistribSMul.toAddMonoidHom W ((d : E)⁻¹))) := by
    intro X
    refine ⟨(d : E) • (coordEquiv F v).symm X, ?_⟩
    show coordEquiv F v ((d : E)⁻¹ • ((d : E) • (coordEquiv F v).symm X)) = X
    rw [inv_smul_smul₀ (by exact_mod_cast hd), AddEquiv.apply_symm_apply]
  exact (AddSubgroup.comap_injective hsurj).eq_iff

theorem mem_smul_addSubgroup_iff (γ : h.unitaryGroup) (S : AddSubgroup W) (x : W) :
    x ∈ γ • S ↔ γ⁻¹ • x ∈ S := by
  exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem dictLattice_diagonal_mul (d : ℤ) (γ : h.unitaryGroup)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    dictLattice b h v d ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • dictLattice b h v d g := by
  ext x
  rw [mem_smul_addSubgroup_iff, mem_dictLattice, mem_dictLattice, adeleSplit_snd_hermitianDiagonal,
    ← mulVec_mem_coreLattice_iff b ((unitaryPointsRationalEquivHermitian F E h v).symm γ) g,
    mulVec_coordEquiv]
  have : ((γ : W ≃ₗ[E] W) ((d : E)⁻¹ • (γ⁻¹ • x))) = (d : E)⁻¹ • x := by
    rw [map_smul]
    congr 1
    show (γ : W ≃ₗ[E] W) (((γ⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) x) = x
    rw [Subgroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ x
  rw [this]

end Lattice

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def vecAtHom (v : Basis ι E W) : W →+ (InfinitePlace E → ι → ℂ) where
  toFun := vecAt v
  map_zero' := by funext w i; simp [vecAt]
  map_add' x y := by funext w i; simp [vecAt]

omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAtHom_apply (v : Basis ι E W) (x : W) : vecAtHom v x = vecAt v x := rfl

def archLattice (v : Basis ι E W) (La : AddSubgroup W) : Submodule ℤ (InfinitePlace E → ι → ℂ) :=
  AddSubgroup.toIntSubmodule (La.map (vecAtHom v))

omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem mem_archLattice {v : Basis ι E W} {La : AddSubgroup W} {y : InfinitePlace E → ι → ℂ} :
    y ∈ archLattice v La ↔ ∃ x ∈ La, vecAt v x = y := by
  change y ∈ La.map (vecAtHom v) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def ArchCovolumeBound.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ D : ℕ, ∃ c : ℝ, ∀ La : AddSubgroup W, IsDIntegral h D La →
    ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
      ZLattice.covolume (archLattice v La) ≤ c

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedGenerators
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def BoundedGenerators.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (t : ℝ), 0 < t →
    ∃ (n : ℕ) (C : ℝ), ∀ (La : AddSubgroup W) (g : archUnitary h v), IsDIntegral h D La →
      (∀ x ∈ La, x ≠ 0 → t ≤ M.len (invApply g (vecAt v x))) →
      ∃ e : Fin n → W, AddSubgroup.closure (Set.range e) = La ∧
        ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StBoundedInverseCompact
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def BoundedInverseCompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (n : ℕ) (e : Fin n → W), Submodule.span E (Set.range e) = ⊤ → ∀ C : ℝ,
    IsCompact {g : archUnitary h v | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordEmbedBasis
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]

def coordEmbed : (ι → E) →+ (InfinitePlace E → ι → ℂ) where
  toFun y := fun w i => w.embedding (y i)
  map_zero' := by funext w i; simp
  map_add' y z := by funext w i; simp

omit [Fintype ι] in
theorem coordEmbed_apply (y : ι → E) (w : InfinitePlace E) (i : ι) :
    coordEmbed E ι y w i = w.embedding (y i) := rfl

def CoordEmbedBasis.Statement [_root_.NumberField.IsTotallyComplex E] : Prop :=
  LinearIndependent ℝ (fun k => coordEmbed E ι (Pi.basis (fun _ : ι => integralBasis E) k)) ∧
    finrank ℝ (InfinitePlace E → ι → ℂ) = finrank ℚ (ι → E)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def CoordLatticeFullRank.Statement (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La →
    (La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom).FG ∧
      Submodule.span ℚ ((La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom : Set (ι → E))) = ⊤

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def DualLatticeMultiple.Statement (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ k : ℤ, k ≠ 0 ∧ ∀ La : AddSubgroup W, IsDIntegral h D La →
    (∀ x ∈ La, ∀ y ∈ La, ∃ n : ℤ, Algebra.trace ℚ E (h.toSesq x y) = n) ∧
    ∀ y : W, (∀ x ∈ La, ∃ n : ℤ, Algebra.trace ℚ E (h.toSesq y x) = n) → k • y ∈ La

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StGramDetermines
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def GramDetermines.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (n : ℕ) (e e' : Fin n → W), IsLattice E (AddSubgroup.closure (Set.range e)) →
    IsLattice E (AddSubgroup.closure (Set.range e')) →
    (∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) →
    ∃ γ : h.unitaryGroup, ∀ a, (γ : W ≃ₗ[E] W) (e a) = e' a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLenCauchySchwarz
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LenCauchySchwarz.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x y : W) (w : InfinitePlace E),
    ‖w.embedding (h.toSesq x y)‖ ≤ M.len (invApply g (vecAt v x)) * M.len (invApply g (vecAt v y))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

