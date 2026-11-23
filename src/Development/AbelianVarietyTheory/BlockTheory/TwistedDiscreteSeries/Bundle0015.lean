module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

variable {D : D7}


variable (D) in
def Sizes : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m),
    2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

section Arrow

variable (θ : InfFam D)

def IsCuspOfType (N : Node D) (φ : GA D N.V → ℂ) : Prop :=
  IsAutFunSm θ N.V φ ∧ IsCuspFun N.V φ ∧ ∀ τ, IsTypeAt θ N.V τ (N.S τ) φ

variable {A B : Node D} {P : Type} (m : A.MeasDat)

def LiftsMult (K : P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M) : Prop :=
  ∀ F ∈ A.Cusp θ, ∃ F' ∈ B.Cusp θ, ∀ (p : P) (v : SmT A.M) (h : GA D B.V),
    IntegrableOn (fun g => K p h g * F v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F v g ∂m.ν = F' (It p v) h

def LiftsSmooth (K : GA D B.V → GA D A.V → ℂ) : Prop :=
  ∀ φ, IsCuspOfType θ A φ → (∀ h, IntegrableOn (fun g => K h g * φ g) m.fd m.ν) ∧
    IsCuspOfType θ B fun h => ∫ g in m.fd, K h g * φ g ∂m.ν

end Arrow

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure RowBase : Prop where

  lev : R.toLevCh.Is A.μ0

  inf : IsInfFam R.θ

  measY : R.models_νY

  measY' : R.models_νY'

  measX : R.models_νX

variable {R}

variable (G : GridPre R)

structure CuspAlong : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f →
    LiftsMult R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j)
      (fun p h g => thetaKO (G.X i j).ω h g (fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f p)) fun p v => (G.X i j).It p v

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f →
    LiftsMult R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1))
      (fun p h g => thetaKO (G.th t i j).ω h g (fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) f p)) fun p v => (G.th t i j).It p v

  up : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i)
      (fun p h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p))) fun p v => G.ItU i p v

  dn : ∀ i, i < D.R.m → ∀ f, IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) f →
    LiftsMult R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1))
      (fun p h g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f p)) fun p v => (G.dn i).It p v

  col : ∀ t j, j < D.R.m → ∀ f, IsFinVec R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f →
    LiftsMult R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j)
      (fun p h g => thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) f p)) fun p v => (G.col t j).It p v

structure CuspAlongSmooth : Prop where

  X : ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.V (i + 1) j).V) (G.V i j).V Φ →
    LiftsSmooth R.θ (A := G.V i j) (B := G.V (i + 1) j) (G.meas t i j) fun h g => thetaKO (G.X i j).ω h g Φ

  th : ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.V i (j + 1)) (B := G.V i j) (G.meas t i (j + 1)) fun h g => thetaKO (G.th t i j).ω h g Φ

  up : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P i) (B := G.P (i + 1)) (G.mP i) fun h g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ)

  dn : ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V Φ →
    LiftsSmooth R.θ (A := G.P (i + 1)) (B := G.P i) (G.mP (i + 1)) fun h g => thetaKO (G.dn i).ω g h Φ

  col : ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    LiftsSmooth R.θ (A := G.Xp j) (B := G.Xp (j + 1)) (G.measX j) fun h g => thetaKO (G.col t j).ω g h Φ

end Grid

def LiftsCuspidalAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlong G

def LiftsCuspidal : Prop := ∀ D : D7, LiftsCuspidalAt D

def LiftsCuspidalSmoothAt (D : D7) : Prop :=
  Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GridPre R),
    RowBase R → G.Is → CuspAlongSmooth G

theorem LiftsMult.exists_linear {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {K : P → GA D B.V → GA D A.V → ℂ}
    {It : P → SmT A.M → SmT B.M} (H : LiftsMult θ m K It) :
    ∃ io : A.Cusp θ →ₗ[ℂ] B.Cusp θ, ∀ (F : A.Cusp θ) p v h,
      IntegrableOn (fun g => K p h g * F.1 v g) m.fd m.ν ∧ ∫ g in m.fd, K p h g * F.1 v g ∂m.ν = (io F).1 (It p v) h := by
  classical
  let b := Module.Free.chooseBasis ℂ (A.Cusp θ)
  choose F' hF'mem hF' using fun i => H (b i).1 (b i).2
  let io := b.constr ℂ (fun i => (⟨F' i, hF'mem i⟩ : B.Cusp θ))
  refine ⟨io, fun F => ?_⟩
  have hF : F ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro p v h
    simp only [io, b.constr_basis]
    exact hF' i p v h
  | zero =>
    intro p v h
    simp
  | add x y _ _ hx hy =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    obtain ⟨hy1, hy2⟩ := hy p v h
    have e : (fun g => K p h g * (x + y).1 v g) = fun g => K p h g * x.1 v g + K p h g * y.1 v g := by
      funext g
      simp [mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.add hy1
    · rw [e, integral_add hx1 hy1, hx2, hy2, map_add (f := _)]
      simp
  | smul c x _ hx =>
    intro p v h
    obtain ⟨hx1, hx2⟩ := hx p v h
    have e : (fun g => K p h g * (c • x).1 v g) = fun g => c * (K p h g * x.1 v g) := by
      funext g
      simp [mul_left_comm]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hx1.const_mul c
    · have h3 : (io (c • x)).1 (It p v) h = c * (io x).1 (It p v) h := by
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h3, e, integral_const_mul, hx2]

section

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cuspAlong_iff_hasLifts (G : GridPre R) : CuspAlong G ↔ G.HasLifts := by
  constructor
  · intro hc
    refine { X := ?_, th := ?_, col := ?_, dn := ?_, up := ?_ }
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.X t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t i j hi hj f hf
      obtain ⟨io, hio⟩ := (hc.th t i j hi hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro t j hj f hf
      obtain ⟨io, hio⟩ := (hc.col t j hj f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.dn i hi f hf).exists_linear
      exact ⟨io, Lift.IsIo.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
    · intro i hi f hf
      obtain ⟨io, hio⟩ := (hc.up i hi f hf).exists_linear
      exact ⟨io, Lift.IsIoUp.mk (fun F φ v g => (hio F φ v g).1) (fun F φ v g => (hio F φ v g).2)⟩
  · intro hl
    refine { X := ?_, th := ?_, up := ?_, dn := ?_, col := ?_ }
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.X t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t i j hi hj f hf F hF
      obtain ⟨io, hio⟩ := hl.th t i j hi hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.up i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIoUp.integ hio ⟨F, hF⟩ p v h, Lift.IsIoUp.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro i hi f hf F hF
      obtain ⟨io, hio⟩ := hl.dn i hi f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩
    · intro t j hj f hf F hF
      obtain ⟨io, hio⟩ := hl.col t j hj f hf
      exact ⟨(io ⟨F, hF⟩).1, (io ⟨F, hF⟩).2, fun p v h =>
        ⟨Lift.IsIo.integ hio ⟨F, hF⟩ p v h, Lift.IsIo.eq hio ⟨F, hF⟩ p v h⟩⟩

end

end GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

def adj (S T : HSp D) (y : WO S T) : WO T S :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

def blkL (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V := fun a b => z (Fin.castAdd V₁.rank a) b

def blkR (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V₁ := fun a b => z (Fin.natAdd V.rank a) b

def ten (M V V₁ : HSp D) : (WO M V → ℂ) →ₗ[ℂ] (WO V₁ M → ℂ) →ₗ[ℂ] (WO M (hsum V V₁) → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ φ' z => φ (blkL M V V₁ z) * φ' (adj M V₁ (blkR M V V₁ z)))
    (fun _ _ _ => funext fun _ => add_mul _ _ _) (fun _ _ _ => funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => funext fun _ => mul_add _ _ _) (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

section Route

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (V M V₁ : Node D)

abbrev Pair : Type := (WO M.V V.V → ℂ) × (WO V₁.V M.V → ℂ)

def IsFinPair (f : Pair V M V₁) : Prop := IsFinVec ψ θ ε M V f.1 ∧ IsFinVec ψ θ (!ε) V₁ M f.2

variable {V M V₁}

def route (a : ArrS M V) (b : ArrS V₁ M) (mV : V.MeasDat) (mM : M.MeasDat) {n : ℕ} (Φ : Fin n → Pair V M V₁)
    (F : GA D V.V → ℂ) : GA D V₁.V → ℂ :=
  ∑ k, b.int mM (Φ k).2 (a.int mV (Φ k).1 F)

end Route

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)


variable (R) in
def al (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) * R.eta ^ (rkV D i j % 2)

def be (i j : ℕ) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

def routeA (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.X i (j + 1)) (G.th t (i + 1) j) (G.meas t i (j + 1)) (G.meas t (i + 1) (j + 1)) Φ F

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OppositeColumnLifts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

variable {D : D7}

section Local


variable (D) in
abbrev Oh : Subring (Datum.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def InI (I : Ideal (𝓞 D.host.E)) (z : Datum.EAf D) : Prop := ∃ h : z ∈ Oh D, (⟨z, h⟩ : Oh D) ∈ idS D.host.F I

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {a a' d₁ d₂ : ℕ}

variable (hd : a + a' = d₁ + d₂) (h : GL (Fin (d₁ + d₂)) (AE D))

end Local

section Models

variable (ψ : AddChar (AF D.host.F) ℂ)


open Classical in
def IsDatOwn (ε : Bool) (S T : Node D) (e : AE D) (f₀ : WO S.V T.V → ℂ)
    (φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ) (f : WO S.V T.V → ℂ) : Prop :=
  IsSBHalf e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True)
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) ∧
    IsThetaAt ψ (symplO (sgn ε S.V) T.V) (heisO ψ (sgn ε S.V) T.V) e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True) 1 f₀
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) f


end Models

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)





end Grid

section Basic₂

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridDat R}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

end
end

