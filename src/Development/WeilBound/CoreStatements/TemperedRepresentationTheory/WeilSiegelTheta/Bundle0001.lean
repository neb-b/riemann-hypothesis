module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.BC

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions

variable {D : D7}

def hermA (D : D7) (r : ℕ) : AddSubgroup (Mx D r r) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def ratHerm (D : D7) (r : ℕ) : AddSubgroup (hermA D r) := (ratMx D r r).comap (hermA D r).subtype

def IsCovolOneH {r : ℕ} (lam : Measure (hermA D r)) (𝓕 : Set (hermA D r)) : Prop :=
  lam.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratHerm D r) 𝓕 lam ∧ lam 𝓕 = 1

def Jt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b : hermA D r) : ℂ :=
  ∫ y, φ y * ψ (halfTr (Matrix.trace (HMul.hMul b.1 (inner V y y) : Mx D r r))) ∂μ

def W (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ b, Jt ψ V μ φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam

def gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin r) D.host.E :=
  (x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * (HSpace.gram V * x)

def IfrB (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
    φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q ∂autMeasure V ν

def Hyp (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) : Prop :=
  2 * r < V.rank ∧ IsCharAF D.host.F ψ ∧ IsInfFam θ ∧ (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) ∧
    (∃ 𝓖, IsCovolOneH lam 𝓖) ∧ ν.IsHaarMeasure ∧ φ ∈ schwartzA θ V.rank r ∧
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤

def PoissonHerm : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    Summable (fun b : HermE D r => J ψ V μ φ b) →
    HasSum (fun β : HermE D r => W ψ V μ lam φ β) (∑' b : HermE D r, J ψ V μ φ b)

def SiegelND : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = W ψ V μ lam φ β

def SiegelDeg : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det = 0 → IfrB V ν φ β = W ψ V μ lam φ β

end PositivityTheory.GramSchwartzFunctions.BC
end
end

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.EC

open GlobalTheory.StdUnn

section Field

variable {K : Type} [Field K]

def cT (σ : K →+* K) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin a) K := (x.map σ).transpose

def Jm (K : Type) [Field K] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) 0

def IsUnitary (σ : K →+* K) {N : ℕ} (J g : Matrix (Fin N) (Fin N) K) : Prop := cT σ g * J * g = J

def IsSiegelP {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) : Prop :=
  ∀ i j : Fin n, g (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0

def eId (K : Type) [Field K] (n r : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

def wr (K : Type) [Field K] (n r : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (1 - eId K n r) (eId K n r) (-eId K n r) (1 - eId K n r)

def nB {n : ℕ} (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 1 b 0 1

def mA (σ : K →+* K) {n : ℕ} (a : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 a 0 0 (cT σ a)⁻¹

def extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if h : (i : ℕ) < r ∧ (j : ℕ) < r then b ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def IsCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUnit a.det ∧ ∀ (i : Fin n) (hi : (i : ℕ) < r), a i = c ⟨i, hi⟩

def repMat (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + n)) (Fin (n + n)) K :=
  wr K n r * nB (extB b) * mA σ a

end Field

def Bruhat : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → (2 : K) ≠ 0 → ∀ n : ℕ,
  ∀ c : ∀ U : Submodule K (Fin n → K), Matrix (Fin (Module.finrank K U)) (Fin n) K,
    (∀ U, LinearIndependent K (c U) ∧ Submodule.span K (Set.range (c U)) = U) →
  ∀ a : ∀ U : Submodule K (Fin n → K), Matrix (Fin n) (Fin n) K, (∀ U, IsCompl (c U) (a U)) →
    (∀ (U : Submodule K (Fin n → K)) (b : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K), cT σ b = b →
      IsUnit (repMat σ b (a U)).det ∧ IsUnitary σ (Jm K n) (repMat σ b (a U))) ∧
    ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) K, IsUnit g.det → IsUnitary σ (Jm K n) g →
      ∃! q : (Σ U : Submodule K (Fin n → K), {b : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K // cT σ b = b}),
        IsSiegelP (g * (repMat σ q.2.1 (a q.1))⁻¹)

def RatPts : Prop :=
  ∀ (D : D7) (n : ℕ),
    (∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D)) ∧
    (∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D)) ∧
    (∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g))

def PInv : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, LeftInv (P D n ⊓ GF D n) (fun γ => (ω γ Φ).1 0)

def ThetaInv : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, ∀ γ ∈ GF D n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))

end PositivityTheory.GramSchwartzFunctions.EC
end
end

-- bundled from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
section
noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions

def PullSchLI : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r n : ℕ) (c : Matrix (Fin r) (Fin n) D.host.E), LinearIndependent D.host.E c →
    ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → pull c φ ∈ schwartzA θ m r

end PositivityTheory.GramSchwartzFunctions
end
end

