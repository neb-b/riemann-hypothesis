module

public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def CosetMass {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (stabAt Γ K y)) ∧
  ∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m

def stabHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) : Subgroup (UAf hc W) :=
  (stabGL (hatL (F := F) (crdLat W N))).subgroupOf (UAf hc W)

def General : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → W.IsPosDef →
    ∀ N : Submodule (𝓞 E) W.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular W.hT N →
      CosetMass (UFin hc W) (stabHat hc W N) (Formalism.HermitianLatticesTheory.mass W.hT N)

def DefiniteSpaceClassStatement (D : D7) (_Lv : LevelData D) (_u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
    CosetMass
      ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      ((levelAfL D.sp.cm.sig D.sp.gram0 (D.sp.crdLat0 N)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def ClassesAsDoubleCosets : Prop :=
  General ∧ ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), DefiniteSpaceClassStatement D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CosetGroupMembership
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

def CosetSum {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (cosetGrp Γ K y)) ∧
  ∀ (ι : Type) [Fintype ι] (y : ι → G),
    Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
    ∑ i, ((Nat.card (cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def stabHat (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) : Subgroup (UAf hc S) :=
  (stabGL (hatL (F := F) (crdLat S N))).subgroupOf (UAf hc S)

def rat0 {R : Ranks} (sp : Spaces R F E) : Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (ratPts sp.cm.sig sp.gram0 (Af F)).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

def stabHat0 {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    Subgroup (UPts sp.cm.sig sp.gram0 (Af F)) :=
  (stabGL (hatL (F := F) (sp.crdLat0 N))).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F))

end Obj

def GeneralForm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (S : HSpace E), S.SigOK → S.IsPosDef →
    ∀ N : Submodule (𝓞 E) S.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular S.hT N →
      CosetSum (UFin hc S) (stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N)

def ColumnForm (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
      CosetSum (rat0 D.sp) (stabHat0 D.sp N) (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def MassAsCosetSum : Prop := GeneralForm ∧ ∀ D : D7, ColumnForm D

theorem mem_cosetGrp {G : Type} [Group G] (Γ K : Subgroup G) (y x : G) :
    x ∈ cosetGrp Γ K y ↔ x ∈ Γ ∧ y⁻¹ * x * y ∈ K := by
  simp only [cosetGrp, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by group⟩⟩
  rintro ⟨k, hk, rfl⟩
  have : y⁻¹ * (y * k * y⁻¹) * y = k := by group
  rwa [this]

theorem stabHat_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    stabHat hc S N = (levelAfL hc.sig S.gram (crdLat S N)).subgroupOf (UAf hc S) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CosetGroupMembership

end
end

