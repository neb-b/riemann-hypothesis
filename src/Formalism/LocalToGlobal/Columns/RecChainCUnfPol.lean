module

public import Formalism.LocalToGlobal.Columns.Bundle0029
public import Formalism.LocalToGlobal.Columns.Bundle0014

@[expose] public section

open NumberField IsDedekindDomain Module Matrix MvPolynomial
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

structure LevCh (X : Fields) (Pr : Primes X) (R : Ranks) where
  β : ℕ → Type
  [finβ : ∀ j, Fintype (β j)]
  [decβ : ∀ j, DecidableEq (β j)]
  lev : ∀ j, β j → LevFam X.E X.K (R.N j) Pr.vGs

attribute [instance] LevCh.finβ LevCh.decβ

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)



end Step

section RhoPt

variable {X : Fields} {Pr : Primes X} {R : Ranks}


open Classical in
def rhoPt (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs)) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N i) := ⟨(R.N_pos i).ne'⟩
    (Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^
        (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  else 1


open Classical in
def rhoPt' (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs)) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N (i + 1)) := ⟨(R.N_pos (i + 1)).ne'⟩
    Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
              (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi
        (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^ (((R.N i / 2 : ℕ) : ℤ))
  else 1

end RhoPt

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

variable {W Λ}

end Chain

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFamC (Λ : LevCh X Pr R) (u : Pr.Word) : Type :=
  ∀ i, Λ.β i → Λ.β (i + 1) → DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs) → DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs) →
    HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFamC Λ u)


variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
