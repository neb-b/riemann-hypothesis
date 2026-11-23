module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG

namespace PositivityTheory.SphericalProduct

def IsLowUniM {L : Type} [Field L] {n : ℕ} (g : GL (Fin n) L) : Prop :=
  (∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) L) i j = 0) ∧ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1

theorem twKer_eq_jacSub {G : Type} [Group G] [TopologicalSpace G] (D : CassData G) (P : G → Prop)
    (hP : ∀ g, g ∈ D.N ↔ P g) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    twKer ρ D.N 1 = jacSub ρ P := by
  unfold twKer jacSub
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨n, (hP _).1 n.2, v, rfl⟩
  · rintro ⟨u, hu, v, rfl⟩
    exact ⟨⟨u, (hP _).2 hu⟩, v, rfl⟩

def IwahoriU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ n : ℕ, ∃ D : CassData (GU σ n), D.J = IwU σ n ∧
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) ∧ (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) ∧
      ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)

def DomU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (D : CassData (GU σ n)), D.J = IwU σ n →
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) → (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) →
      (∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) → ∀ t : D.T,
      ((∀ i j : Fin n, i ≤ j → ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
          ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) → D.IsDom t) ∧
      (IsStrictDom ((t : GU σ n) : GL (Fin n) L) → D.IsStrDom t)

end PositivityTheory.SphericalProduct

end
