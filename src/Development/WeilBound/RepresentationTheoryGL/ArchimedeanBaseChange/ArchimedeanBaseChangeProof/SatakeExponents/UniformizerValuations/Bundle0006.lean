module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Shuf (n : ℕ) where
  a : ℕ
  b : ℕ
  e : Fin a ⊕ Fin b ≃ Fin n
  monoL : StrictMono fun i : Fin a => e (Sum.inl i)
  monoR : StrictMono fun j : Fin b => e (Sum.inr j)
  eps : Fin n → ℂˣ

def resL (s : Shuf n) (x : Fin n → ℤ) : Fin s.a → ℤ := fun i => x (s.e (Sum.inl i))
def resR (s : Shuf n) (x : Fin n → ℤ) : Fin s.b → ℤ := fun j => x (s.e (Sum.inr j))

def qU (w : Pl E) (k : ℤ) : ℂˣ := if h : (qh w : ℂ) ≠ 0 then Units.mk0 _ h ^ k else 1

def chiOf (w : Pl E) (s : Shuf n) (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) : Fin n → ℂˣ :=
  fun k => s.eps k * Sum.elim (fun i => ξa i * qU w ((s.a : ℤ) - 1 - 2 * (i : ℕ)))
    (fun j => ξb j * qU w ((s.b : ℤ) - 1 - 2 * (j : ℕ))) (s.e.symm k)

def ChiEval : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) (x : Fin n → ℤ),
  ((∏ k, s.eps k ^ x k : ℂˣ) : ℂ) * ev2 w ξa ξb (resL s x) (resR s x) = ((∏ k, chiOf w s ξa ξb k ^ x k : ℂˣ) : ℂ)

def GapRes : Prop := ∀ (n : ℕ) (s : Shuf n) (x : Fin n → ℤ), x ∈ coneGL n 2 → Gap (resL s x) ∧ Gap (resR s x)

def ChoiceT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ι : Type) [Fintype ι]
  (s : ι → Shuf n) (Z : ∀ i, Set ((Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ))) (α : Fin n → ℂˣ), (∀ i, (Z i).Finite) →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) ∧ evalGL c α = 1 ∧
    ∀ i, ∀ p ∈ Z i, (c.sum fun x a => a * ((∏ k, (s i).eps k ^ x k : ℂˣ) : ℂ) *
        ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x)) ≠ 0 → chiOf w (s i) p.1 p.2 = α

def ChoiceS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (GLw n w)),
  IsOpen (K' : Set (GLw n w)) → IsCompact (K' : Set (GLw n w)) → ∀ P : SmIrr (GLw n w), (∃ v ∈ fixed P.ρ K', v ≠ 0) →
  ∀ (k : ℕ) (D : Fin k → Pre E n),
  ∃ e : GLw n w → ℂ, IsHk K' e ∧ (∃ v₀ ∈ fixed P.ρ K', ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed P.ρ K', hk P.ρ K' e v = l v • v₀) ∧
    ∀ j, ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (D j) w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0

def ChoiceTOf : Prop := PeakCone → ChiEval → GapRes → ChoiceT

end PositivityTheory.Rg.BcB.F.Choice

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupAlgPf
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F

namespace SetupAlgPf

section Gen

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ}

def evB (s : ι) : Prod' H d →⋆ₐ[ℂ] (H s →L[ℂ] H s) where
  toFun a := a.1 s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def evU : Prod' H d →⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def eigSub (v : EuclideanSpace ℂ (Fin d)) : StarSubalgebra ℂ (Prod' H d) where
  carrier := {a | ∃ c : ℂ, a.2 v = c • v ∧ (star a.2) v = starRingEnd ℂ c • v}
  mul_mem' := by
    rintro a b ⟨ca, ha1, ha2⟩ ⟨cb, hb1, hb2⟩
    refine ⟨ca * cb, ?_, ?_⟩
    · simp only [Prod.snd_mul, ContinuousLinearMap.mul_apply, hb1, map_smul, ha1, smul_smul, mul_comm]
    · simp only [Prod.snd_mul, star_mul, ContinuousLinearMap.mul_apply, ha2, map_smul, hb2, smul_smul, map_mul]
  add_mem' := by
    rintro a b ⟨ca, ha1, ha2⟩ ⟨cb, hb1, hb2⟩
    refine ⟨ca + cb, ?_, ?_⟩
    · simp only [Prod.snd_add, ContinuousLinearMap.add_apply, ha1, hb1, add_smul]
    · simp only [Prod.snd_add, star_add, ContinuousLinearMap.add_apply, ha2, hb2, map_add (f := _), add_smul]
  algebraMap_mem' r := by
    refine ⟨r, ?_, ?_⟩
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, star_smul]
  star_mem' := by
    rintro a ⟨c, h1, h2⟩
    refine ⟨starRingEnd ℂ c, ?_, ?_⟩
    · simpa [Prod.snd_star] using h2
    · simpa [Prod.snd_star] using h1

def pFun (v : EuclideanSpace ℂ (Fin d)) (a : Prod' H d) : ℂ := inner ℂ v (a.2 v) / inner ℂ v v

theorem pFun_eq {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0) {a : Prod' H d} {c : ℂ} (h : a.2 v = c • v) :
    pFun v a = c := by
  rw [pFun, h, inner_smul_right, mul_div_assoc, div_self (inner_self_ne_zero.2 hv), mul_one]

theorem commute_of_adjoin {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Ring B]
    [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (f : A →⋆ₐ[ℂ] B) (b : B) (t : Set A)
    (h : ∀ x ∈ t, Commute b (f x) ∧ Commute b (star (f x))) :
    ∀ x ∈ StarAlgebra.adjoin ℂ t, Commute b (f x) := by
  intro x hx
  have hle : StarAlgebra.adjoin ℂ t ≤ (StarSubalgebra.centralizer ℂ ({b} : Set B)).comap f := by
    apply StarAlgebra.adjoin_le
    intro y hy
    show f y ∈ StarSubalgebra.centralizer ℂ ({b} : Set B)
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro g rfl
    refine ⟨(h y hy).1.eq, ?_⟩
    have := congrArg star (h y hy).2.eq
    simp only [star_mul, star_star] at this
    exact this.symm
  have hm : f x ∈ StarSubalgebra.centralizer ℂ ({b} : Set B) := hle hx
  rw [StarSubalgebra.mem_centralizer_iff] at hm
  exact (hm b rfl).1

end Gen

theorem coe_pow_clm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : V →L[ℂ] V) (k : ℕ) :
    ((f ^ k : V →L[ℂ] V) : V →ₗ[ℂ] V) = (f : V →ₗ[ℂ] V) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ContinuousLinearMap.toLinearMap_mul, ih]

section Build

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

abbrev Alg (gen : Γ → Prod' H d) : Type := StarAlgebra.adjoin ℂ (Set.range gen)

abbrev algCR (gen : Γ → Prod' H d) (h1 : ∀ x y, Commute (gen x) (gen y))
    (h2 : ∀ x y, Commute (gen x) (star (gen y))) : CommRing (Alg gen) :=
  { (inferInstance : Ring (Alg gen)) with
    mul_comm := by
      haveI := StarAlgebra.isMulCommutative_adjoin ℂ (s := Set.range gen)
        (by rintro _ ⟨x, rfl⟩; exact ⟨(h2 x x).symm.eq⟩)
        (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _; exact h1 x y)
        (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _; exact h2 x y)
      exact mul_comm' }

def Rb (gen : Γ → Prod' H d) (s : ι) : Alg gen →⋆ₐ[ℂ] (H s →L[ℂ] H s) :=
  (evB s).comp (StarSubalgebra.subtype _)

def ρU (gen : Γ → Prod' H d) : Alg gen →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin d)) where
  toFun a := ((a : Prod' H d).2 : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    ext w
    simp [Algebra.algebraMap_eq_smul_one]

theorem mem_eig (gen : Γ → Prod' H d) (v : EuclideanSpace ℂ (Fin d))
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (a : Prod' H d) ∈ eigSub v :=
  StarAlgebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact heig x) a.2

theorem hpv (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (a : Prod' H d).2 v = pFun v (a : Prod' H d) • v := by
  obtain ⟨c, h1, _⟩ := mem_eig gen v heig a
  rw [pFun_eq hv h1, h1]

theorem hps (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) (a : Alg gen) :
    (star (a : Prod' H d).2) v = starRingEnd ℂ (pFun v (a : Prod' H d)) • v := by
  obtain ⟨c, h1, h2⟩ := mem_eig gen v heig a
  rw [pFun_eq hv h1, h2]

def pU (gen : Γ → Prod' H d) {v : EuclideanSpace ℂ (Fin d)} (hv : v ≠ 0)
    (heig : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v) :
    Alg gen →⋆ₐ[ℂ] ℂ where
  toFun a := pFun v (a : Prod' H d)
  map_one' := pFun_eq hv (by simp)
  map_mul' a b := pFun_eq hv (by
    show (a : Prod' H d).2 ((b : Prod' H d).2 v) = _
    rw [hpv gen hv heig b, map_smul, hpv gen hv heig a, smul_smul, mul_comm])
  map_zero' := pFun_eq hv (by simp)
  map_add' a b := pFun_eq hv (by
    show (a : Prod' H d).2 v + (b : Prod' H d).2 v = _
    rw [hpv gen hv heig a, hpv gen hv heig b, add_smul])
  commutes' r := pFun_eq hv (by simp [Algebra.algebraMap_eq_smul_one])
  map_star' a := pFun_eq hv (by
    show (star (a : Prod' H d).2) v = _
    rw [hps gen hv heig a, starRingEnd_apply])

theorem commU_lem (gen : Γ → Prod' H d) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hu : ∀ x, Commute u (gen x).2 ∧ Commute u (star (gen x).2)) (g : Alg gen) :
    Commute (u : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (ρU gen g) := by
  have h := commute_of_adjoin (evU (H := H)) u _ (by rintro _ ⟨x, rfl⟩; exact hu x) _ g.2
  have h' := congrArg (fun f : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) =>
    (f : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))) h.eq
  simp only [ContinuousLinearMap.toLinearMap_mul] at h'
  exact h'

theorem comm_lem (gen : Γ → Prod' H d) (β : ∀ s, H s →L[ℂ] H s)
    (hb : ∀ s x, Commute (β s) ((gen x).1 s) ∧ Commute (β s) (star ((gen x).1 s))) (s : ι) (g : Alg gen) :
    Commute (β s) (Rb gen s g) :=
  commute_of_adjoin (evB s) (β s) _ (by rintro _ ⟨x, rfl⟩; exact hb s x) _ g.2

end Build

end SetupAlgPf

open SetupAlgPf in
theorem setupAlg : SetupAlg := by
  intro E _ _ _ n π S T K W X
  let _ := X.ft; let _ := X.ne; let _ := X.ng; let _ := X.ip; let _ := X.cs
  have hg0 : X.gen X.a₀ ∈ StarAlgebra.adjoin ℂ (Set.range X.gen) := StarAlgebra.subset_adjoin ℂ _ ⟨X.a₀, rfl⟩
  refine ⟨{
      A := Alg X.gen
      cr := algCR X.gen X.comm X.commStar
      sr := (inferInstance : StarRing (Alg X.gen))
      al := (inferInstance : Algebra ℂ (Alg X.gen))
      sm := (inferInstance : StarModule ℂ (Alg X.gen))
      ι := X.ι
      H := X.H
      R := Rb X.gen
      β := X.β
      m := X.m
      V := EuclideanSpace ℂ (Fin X.d)
      ρ := ρU X.gen
      u := (X.u : EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d))
      p := pU X.gen X.v_ne X.eigv
      a₀ := ⟨X.gen X.a₀, hg0⟩
      pa₀ := ?_
      comm := comm_lem X.gen X.β X.βcomm
      commU := commU_lem X.gen X.u X.ucomm
      bound := ?_
      eig := ⟨X.v, X.v_ne, X.uv, fun g => hpv X.gen X.v_ne X.eigv g⟩
      read := ?_ }⟩
  · obtain ⟨c, hc, h⟩ := X.a₀v
    show pFun X.v (X.gen X.a₀) ≠ 0
    rw [pFun_eq X.v_ne h]
    exact hc
  · intro g hg
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hg
    obtain ⟨C, N, j, h⟩ := X.bound g.1 g.2 ⟨b.1, b.2, by rw [← hb]; rfl⟩
    refine ⟨C, N, j, h.mono fun k hk => ?_⟩
    have e : ((X.u : EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d)) * ρU X.gen g) ^ k =
        (((X.u * (g : Prod' X.H X.d).2) ^ k : EuclideanSpace ℂ (Fin X.d) →L[ℂ] EuclideanSpace ℂ (Fin X.d)) :
          EuclideanSpace ℂ (Fin X.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin X.d)) := by
      rw [coe_pow_clm, ContinuousLinearMap.toLinearMap_mul]
      rfl
    rw [e]
    exact hk
  · intro s χ hb hp h3
    exact X.read s χ hb (fun a _ => ⟨pU X.gen X.v_ne X.eigv a, hpv X.gen X.v_ne X.eigv a, hp a⟩) h3

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
section
namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg (_root_.GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg) _root_.GlobalTheory.CompanionTheory.CompUnitary.compUnit PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg (_root_.GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg) _root_.GlobalTheory.CompanionTheory.CompUnitary.compUnit PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U
end

