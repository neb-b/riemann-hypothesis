module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith
open scoped TensorProduct

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]


omit [NumberField LL] in
def IsCentralIdem (eC : G → LL) : Prop :=
  (∀ g h, eC (h * g * h⁻¹) = eC g) ∧ ∀ g, ∑ h, eC h * eC (h⁻¹ * g) = eC g

end Abstract

variable {D : D7}

section Comparison₂

variable (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

end Comparison₂

section Level

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ} {LL : Type} [Field LL]
  {G : Type} [Group G]

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.KappaLatticeEvaluation
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

def latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) :
    f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  unfold latIn latOf
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.2, hF⟩
  · rintro ⟨hC, hv⟩
    exact ⟨⟨f, hC⟩, hv, rfl⟩

end Generic

variable {D : D7}

abbrev cuspW (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

def supLat (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule (𝓞 T.Q.c.F) (T.R j) :=
  latIn (cuspW T j w) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet

def FullAt (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j) : Prop :=
  (supLat T j w).FG ∧ Submodule.span T.Q.c.F (supLat T j w : Set (T.R j)) = cuspW T j w

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SupremumLattice
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Ambient

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
  (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)

def supIn : Submodule (𝓞 K) R := (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem supIn_full_iff :
    ((supIn C Vs hV).FG ∧ Submodule.span K (supIn C Vs hV : Set R) = C) ↔
      Submodule.IsFullLattice K (latOf C Vs hV) := by
  have h1 : (supIn C Vs hV).FG ↔ (latOf C Vs hV).FG :=
    ⟨Submodule.fg_of_fg_map_injective (C.subtype.restrictScalars (𝓞 K)) C.injective_subtype, fun h => h.map _⟩
  have h2 : Submodule.span K (supIn C Vs hV : Set R) =
      (Submodule.span K (latOf C Vs hV : Set C)).map C.subtype := by
    rw [← Submodule.span_image]; rfl
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact { toIsLattice := Submodule.IsLattice.of_fg K a
            span_eq_top := Submodule.map_injective_of_injective C.injective_subtype (by
              rw [b, Submodule.map_subtype_top]) }
  · intro h
    exact ⟨h.fg, by rw [Submodule.IsFullLattice.span_eq_top (self := h), Submodule.map_subtype_top]⟩

end Ambient

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice
end
end

