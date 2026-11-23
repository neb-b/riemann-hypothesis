module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.RepGApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def expo (ψ : Fin n → kˣ →* ℂˣ) (d : Fin n → kˣ) : ℂ :=
  ((torusChar ψ d * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom d)⁻¹ : ℂˣ) : ℂ)

def Reg (a : kˣ →* ℂˣ) : Prop := (∀ u ∈ Hi.Uo k, a u = 1) ∧ ∀ m : ℤ, |m| ≤ 2 → a ^ 2 ≠ absPow k (m : ℂ)

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

abbrev Kw (w : Plc L) : Type := w.adicCompletion L


open Classical in
def secW (n : ℕ) (w : Plc L) : GL (Fin n) (Kw w) →* UA L n :=
  if h : ∃ j : GL (Fin n) (Kw w) →* UA L n, (∀ g, j g ∈ locU n w) ∧ ∀ g, cLoc w (j g) = g then h.choose else 1


variable (L) in
def infC (n : ℕ) : UA L n →* (InfinitePlace L → GL (Fin n) ℂ) := Pi.monoidHom fun v => cEmb v.embedding


variable (L) in
def Kall (n : ℕ) : Subgroup (UA L n) := finU (E := L) (n := n) ⊓ ⨅ w : Plc L, (GlobalTheory.LFun.KGL w (n := n)).comap (cLoc w)

variable {n : ℕ}

def IsLevel (U : Subgroup (UA L n)) : Prop := U ≤ Kall L n ∧ IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}

def lev (U : Subgroup (UA L n)) (S : Finset (Plc L)) (V : ∀ w : Plc L, Sig.Lev (Kw w)) : Subgroup (UA L n) :=
  U ⊓ ⨅ w ∈ S, ((V w).J n).comap (cLoc w)

abbrev iw (w : Plc L) : Sig.Lev (Kw w) := Sig.Lev.iw _

abbrev deep (c : ℕ) (w : Plc L) : Sig.Lev (Kw w) := Sig.Lev.deep _ c

structure Places (S : Set (Plc L)) : Prop where
  split : ∀ w ∈ S, IsSplitAt w
  inj : Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) S

def HasTwo (S : Finset (Plc L)) : Prop :=
  ∀ w : Plc L, (2 : 𝓞 L) ∈ w.asIdeal → ∃ w' ∈ S, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))

def repE {I : Type} [Fintype I] (j : ℕ) (e : I → ℤ) : Representation ℂ (I → GL (Fin 2) ℂ) (Wt.VD I j) where
  toFun g := ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) • Wt.mRep 2 _ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, smul_mul_smul_comm, ← Units.val_mul, ← Finset.prod_mul_distrib]
    simp [mul_zpow]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure IsAF (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)) (φ : UA L n → V) : Prop where
  left : ∀ γ ∈ ratU L n, ∀ g, φ (γ * g) = φ g
  inf : ∀ x ∈ infU L n, ∀ g, φ (g * x) = R (infC L n x⁻¹) (φ g)
  level : ∀ u ∈ U, ∀ g, φ (g * u) = φ g

def EigAt (φ : UA L n → V) (w : Plc L) (W : Sig.Lev (Kw w)) (d : Fin n → (Kw w)ˣ) (c : ℂ) : Prop :=
  Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) (W.J n) (W.J n) (Sig.dg d) φ = c • φ

def EigS (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (a : (Kw w)ˣ →* ℂˣ) : Prop :=
  ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 → EigAt φ w W ![t, t⁻¹] (expo ![a, 1] ![t, t⁻¹])

def EigT (φ : UA L n → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  ∀ d, Sig.SDom d → EigAt φ w W d (expo ψ d)

def CoefIn (φ : UA L n → V) (π : Submodule ℂ (UA L n → ℂ)) : Prop := ∀ f : V →ₗ[ℂ] ℂ, f ∘ φ ∈ π

abbrev Comp (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (τ : SmIrr (GL (Fin n) (Kw w))) : Prop :=
  IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ

def CompSub (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  (∀ i, IsSmoothChar (ψ i)) ∧ ∃ τ, Comp π w τ ∧ IsSubquotient τ.ρ (prinSeries ψ)

def CompEq (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  (∀ i, IsSmoothChar (ψ i)) ∧ ∃ τ, Comp π w τ ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ))


variable (L) in
abbrev Unr : Prop := ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal

end UpperTheory.V.Z.Sym.Dict

namespace UpperTheory.V.Z.Sym

open Dict

end UpperTheory.V.Z.Sym

end
