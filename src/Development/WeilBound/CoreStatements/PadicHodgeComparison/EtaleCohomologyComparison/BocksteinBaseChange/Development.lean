module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

end CrystallineSemistableComparison
