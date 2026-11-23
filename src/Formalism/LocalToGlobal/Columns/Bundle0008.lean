module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0006
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.LocalToGlobal.Divisibility.LiftLatInst
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LogVandermondeBounds.Bundle0001
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0001
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentArithmeticBound

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.AtTOwedV
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.IsUp.sameAt {d d' : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (h : Deco.IsUp P q d d') {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P.1) (hQ' : Q ≠ conjPrime₂ P.1) :
    SameAt Q d.N d'.N := by
  obtain ⟨x, hx, -, rfl⟩ := h
  exact (upN_spec hd.lat hd.uni P.1 hP.ne hx).2.2.1 Q hQ hQ'

theorem Deco.IsUp.f_ne {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') {Q : ST}
    (hQ : Q ≠ P) : d'.f Q = d.f Q := by
  obtain ⟨x, _, _, rfl⟩ := h
  simp only [Deco.up, Function.update, dif_neg hQ]

theorem Deco.IsUp.be_eq {d d' : Deco E n ST SG} {P : ST} {q : 𝓞 E} (h : Deco.IsUp P q d d') : d'.be = d.be := by
  obtain ⟨x, _, _, rfl⟩ := h
  rfl

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawPhi
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section PhiLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def PhiGSLaw (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) : Prop :=
  ∀ γ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ ∈ LocE.JGsym P q k₀ rS r t n' c', ∀ x : HomE E (n' + c') (n + c),
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
        (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
          LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x

structure PhiGSLawHyp (P : HeightOneSpectrum (𝓞 E)) (q k₀ rS r t j c' n' c n : ℕ) : Prop where
  hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal
  hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2
  hj : 1 ≤ j
  hk' : k₀ ≤ n'
  hk : k₀ ≤ n
  hr : k₀ + rS < r
  ht : 0 < t
  hsrc : n' + c' = r + (j - 1) * t
  htgt : n + c = r + j * t

end PhiLaw

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainOne
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def oneIdx (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (m2 : ℕ) : ChIdx X Pr R Q where
  β j := {_u : Unit // j ≤ m2 + 1}
  h _ _ _ := 1
  levG j _ := Λ j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


open Classical in
def OneYbSym (m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0 →
      ∀ l : Fin (R.N (m2 + 1)), IntAt P.1 ((qOf P.1 : X.E) * y' l) ∧ redP P.1 ((qOf P.1 : X.E) * y' l) = if l.1 = R.k then 1 else 0

variable {Ch sel mu cst Λ}

end One

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HeckeInertTr
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section NbFunI

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

def nbFunI (P : Ideal (𝓞 E)) (s : List ℕ) : (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) →ₗ[K] (DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → V) where
  toFun ψ d := ∑ d₁ ∈ d.inertNb P s, ψ d₁
  map_add' ψ ψ' := by
    funext d
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext d
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

end NbFunI

section Tr

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem trF_nbFunI {V : Type} [AddCommGroup V] [Module X.K V] (a : GLG (E := X.E) (n := n) (SG := SG)) (P : Ideal (𝓞 X.E)) (s : List ℕ)
    (ψ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → V) :
    trF X n ST SG V a (nbFunI X.K V P s ψ) = nbFunI X.K V P s (trF X n ST SG V a ψ) := by
  funext d
  show ∑ d₁ ∈ (((1 : UF X.E n), a⁻¹) • d).inertNb P s, ψ d₁ =
    ∑ d₁ ∈ d.inertNb P s, ψ (((1 : UF X.E n), a⁻¹) • d₁)
  exact DecoSet.sum_inertNb_smul P s _ d ψ

variable (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem heckeFamI_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ)
    (φ : (formGSD C Λ).EqFun) :
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
      nbFunI X.K C.V y.1.1.asIdeal y.2 (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) := by
  funext d
  show ((heckeI (Formalism.L2.DIV.formPts C Λ) y.1.1.asIdeal y.2).op φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d =
    ∑ d₁ ∈ DecoSet.inertNb y.1.1.asIdeal y.2 d, (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d₁
  rw [heckeI_op_apply]
  simp [DecoPts.nbI, Formalism.L2.DIV.formPts]

theorem heckeFamI_comm_trRep {A : Type} [Group A] (ι : A →* GLG (E := X.E) (n := n) (SG := SG)) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : LevOffI ST SG S0 × List ℕ) (a : A) :
    Commute (trRep C Λ ι hι a) (heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y) := by
  show trRep C Λ ι hι a * heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y =
    heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y * trRep C Λ ι hι a
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Module.End.mul_apply, Module.End.mul_apply]
  show trF X n ST SG C.V (ι a)
      ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y φ : (formGSD C Λ).EqFun) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) =
    ((heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y (trRep C Λ ι hι a φ) : (formGSD C Λ).EqFun) :
      DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V)
  rw [heckeFamI_formPts_apply, heckeFamI_formPts_apply, trF_nbFunI]
  rfl

end Tr

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.Inputs
section
noncomputable section

namespace Formalism.L2.Col

open Module Module.End Polynomial

section Link

variable {L Pl Pt : Type} [Field L]

end Link

section Conc

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Conc

section Genus

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def UnimodGenusLoc (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  IsCMUnram E → ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
    SameGenus (hStd E n) (stdLat E n) N

def UnimodGenusLocAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), UnimodGenusLoc E n

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def UnimodGenus : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N →
    ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

end Genus

section Counting

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def wSeq {n : ℕ} (lam : DomWeight n) : ℕ → ℝ := fun i => if h : i < n then ((lam.w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylDim {n : ℕ} (lam : DomWeight n) : Prop :=
  (Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ℝ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n

end Counting

section Alcove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Alcove

abbrev MinkowskiBound : Prop := Formalism.HermitianLatticeCounting.S6.MinkowskiBound

section FormalDegree

open MeasureTheory

end FormalDegree

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def formAt {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)
    (v : InfinitePlace K) (x y : V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (b.repr x i)) * v.embedding (P (b i) (b j)) * v.embedding (b.repr y j)

end Forms

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

abbrev oneW (lam : DomWeight n) : Unit → DomWeight n := fun _ => lam

end Std

def kap (R : Ranks) : ℕ := R.N 0 - 1

theorem kap_succ (R : Ranks) : kap R + 1 = R.N 0 := by
  have h : R.N 0 = R.k := by simp [Ranks.N]
  have := R.m_add_three_le_k
  unfold kap
  omega

def castW {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : Fin (κ + 1) → ℤ := fun i => lam.w (Fin.cast h i)

section Nums

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def lamZ (u : Pr.Word) (τ : X.Tau) : Fin (kap R + 1) → ℤ := castW (kap_succ R) (W.lamTrue u 0 τ)






end Nums

section Named

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (K) {n : ℕ}

end Named

section NamedCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end NamedCol

section Main

end Main

section PartI

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


variable (hX : X.Ok)

end PartI

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TargetChF
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end Chain

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQThetaOpen
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
end
end

