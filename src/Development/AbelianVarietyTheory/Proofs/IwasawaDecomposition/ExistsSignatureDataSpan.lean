module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0336

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eigenvalue_integral_of_baseChange {O M : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (f : Module.End O M)
    (x : FractionRing O ⊗[O] M) (hx : x ≠ 0) (c : FractionRing O)
    (h : f.baseChange (FractionRing O) x = c • x) : ∃ a : O, algebraMap O (FractionRing O) a = c := by
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hev : (Module.End.baseChangeHom O (FractionRing O) M f).HasEigenvector c x :=
    ⟨Module.End.mem_eigenspace_iff.mpr h, hx⟩
  have key := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O (FractionRing O))) hev
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, hpf, map_zero,
    Polynomial.eval_map_algebraMap] at key
  have h0 : Polynomial.aeval c p = 0 := by
    by_contra hne
    exact hx ((smul_eq_zero.mp key.symm).resolve_left hne)
  exact IsIntegrallyClosed.isIntegral_iff.mp ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

section SigMake

variable (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S)

def sigVal (i : T.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i

def sigLam (i : T.Tw) (j : ℕ) (b : Bool) (σ : D.what₂.FT) (k : ℕ) (P : PlE D.host) : FractionRing (T.O i) :=
  algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)

def SigIdx (i : T.Tw) : Type :=
  {x : Fin (D.R.m + 1) × Bool × D.what₂.FT // 1 ≤ (x.1 : ℕ) ∧ D.what₂.isot (x.1 : ℕ) x.2.2 ≠ ⊥ ∧ D.nd.goodRow x.2.2 ∧
    ∀ k P, sigVal D T i k P → ∃ a : T.O i, algebraMap (T.O i) (FractionRing (T.O i)) a = sigLam D T In i x.1 x.2.1 x.2.2 k P}

instance finSigIdx (i : T.Tw) : Finite (SigIdx D T In i) := Subtype.finite


open Classical in
def sigEig (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) : T.O i :=
  if h : sigVal D T i k P then (x.2.2.2.2 k P h).choose else 1

theorem sigEig_on (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : sigVal D T i k P) :
    algebraMap (T.O i) (FractionRing (T.O i)) (sigEig D T In i x k P) = sigLam D T In i x.1.1 x.1.2.1 x.1.2.2 k P := by
  unfold sigEig
  rw [dite_eq_left h]
  exact (x.2.2.2.2 k P h).choose_spec

theorem sigEig_off (i : T.Tw) (x : SigIdx D T In i) (k : ℕ) (P : PlE D.host) (h : ¬ sigVal D T i k P) :
    sigEig D T In i x k P = 1 := by
  unfold sigEig
  rw [dite_eq_right h]

def sigSys (i : T.Tw) (x : SigIdx D T In i) : ℕ × Bool × (ℕ → PlE D.host → T.O i) :=
  ((x.1.1 : ℕ), x.1.2.1, sigEig D T In i x)

def sigDataOf : SigData D T where
  Sig i := ↥(Set.range (sigSys D T In i))
  fin i := @Fintype.ofFinite _ (Set.finite_range (sigSys D T In i)).to_subtype
  jS i s := s.1.1
  jS_range i s := by
    obtain ⟨x, hx⟩ := s.2
    rw [← hx]
    exact ⟨x.2.1, Nat.lt_succ_iff.mp x.1.1.2⟩
  side i s := s.1.2.1
  hEig i s := s.1.2.2
  rowS i s := s.2.choose.1.2.2

end SigMake

theorem sigDataOf_spec (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (i : T.Tw)
    (s : (sigDataOf D T In).Sig i) :
    sigSys D T In i s.2.choose = s.1 := s.2.choose_spec

theorem hkB_coe_of_val (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S) (hst : HkStab D T S In)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : sigVal D T i k P)
    (x : ↥(BI D T S In i j b)) :
    ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) = hkT D T S In i j b k P x := by
  unfold hkB
  rw [dite_eq_left ⟨h1, h2, hv⟩]
  rfl

end GlobalTheory.HeightCounting.FormsStep
