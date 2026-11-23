module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerLe {A B Z₁ Z₂ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] (q₁ : A → B → Z₁) (q₂ : A → B → Z₂) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B), ∑ i, q₁ (a i) (b i) = 0 → ∑ i, q₂ (a i) (b i) = 0

def AbsIrr {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) : Prop :=
  (∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, a g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    ∀ T : Module.End ℂ K, (∀ g, T ∘ₗ a g = a g ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def intersection_update_fsHerm_neg_one {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι) (f : Module.End ℂ (K i)) :
    Module.End ℂ (⨂[ℂ] j, K j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) i f)

theorem position_tprod {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι)
    (f : Module.End ℂ (K i)) (v : ∀ j, K j) :
    intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v i (f (v i))) := by
  unfold intersection_update_fsHerm_neg_one
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

section Cover

variable {p q r s : ℕ}

def AdjRule {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (X : Mat p q) P P' y y', ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ = ⟪B P y, B (fockAct1 p q r s (adjZ X) P') y'⟫_ℂ

def InvRule (N : GKMod r s) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (Y : Mat r s) P y, B (fockAct2 p q r s Y P) y = B P (N.act (adjZ Y) y)


variable (p q r s) in
def UnitaryImage : Prop :=
  ∀ (Y Z : Type) [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z), AdjRule B →
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧ Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (fockAct1 p q r s X P) y = A.M.act X (B' P y)

def contr {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) : A ⊗[ℂ] V →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A (innerₛₗ ℂ (ι y) ∘ₗ ι)


variable (p q) in
def FiniteSupport {T : GrpData r s} (R : DSRep T) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (B : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] A), InvRule R.HK B →
    ∀ P, ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪R.ι y, R.ι e⟫_ℂ = 0) → B P y = 0

def TensorForm : Prop :=
  ∀ (U A V H : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    (∀ t : A ⊗[ℂ] V, (∀ y, contr ι y t = 0) → t = 0) ∧
    ∀ B : U →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] A,
      (∀ P, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → B P y = 0) →
      ∃ f : U →ₗ[ℂ] A ⊗[ℂ] V, ∀ P y, contr ι y (f P) = B P y

structure IsCoverPair (N : GKMod r s) {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop where
  skew : ∀ X ∈ upq p q, ∀ P P' y y',
    ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ + ⟪B P y, B (fockAct1 p q r s X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ upq r s, ∀ P y, B (fockAct2 p q r s Y P) y + B P (N.act Y y) = 0


variable (p q) in
def CoverKer (N : GKMod r s) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₂),
    IsCoverPair N B₁ → IsCoverPair N B₂ → B₁ ≠ 0 → KerLe (fun P y => B₁ P y) fun P y => B₂ P y

end Cover

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure IsKAct (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) : Prop where
  der : ∀ X ∈ lieAt V τ, ∀ v : kFin M τ,
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (a X v : M.H τ) 0
  skew : ∀ X ∈ lieAt V τ, ∀ v w : kFin M τ, ⟪a X v, w⟫_ℂ + ⟪v, a X w⟫_ℂ = 0

def KSm : Prop := ∀ τ, kFin M τ ≤ M.sm τ

abbrev KT : Type := ⨂[ℂ] τ, kFin M τ


variable {M} in
def inclK (h : KSm M) : KT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => Submodule.inclusion (h τ)

def kOp (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ) : Module.End ℂ (kFin M τ) :=
  (M.rep τ k : M.H τ →ₗ[ℂ] M.H τ).restrict fun _ hv => rep_mem_kFin M τ hk hv

def sOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure IsLocPair (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z) :
    Prop where
  skew : ∀ X ∈ lieAt V τ, ∀ P P' y y', ⟪B (sOp M M' τ aT X P) y, B P' y'⟫_ℂ + ⟪B P y, B (sOp M M' τ aT X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ lieAt W τ, ∀ P y, B (tOp M M' τ aS Y P) y + B P (a' Y y) = 0

def LocKer (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₁) (B₂ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₂),
    IsLocPair M M' τ aS aT a' B₁ → IsLocPair M M' τ aS aT a' B₂ → B₁ ≠ 0 →
      KerLe (fun P y => B₁ P y) fun P y => B₂ P y

def IsCuspGrow (θ : InfFam D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ GlobalTheory.Grow.UnifModGrowth V θ φ

def kMean (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ) (w : M.H τ) : M.H τ :=
  ∫ k, e k • M.σ τ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK (M.ε τ))

def IsCoefFam {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} (c : Fin n → G → ℂ) : Prop :=
  (∀ i, Continuous (c i)) ∧ ∀ (k₀ : G) (i : Fin n), ∃ d : Fin n → ℂ, ∀ k, c i (k₀ * k) = ∑ j, d j * c j k

end GlobalTheory.Chain.IoLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZetaSumU

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem cartan_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ (d : Fin n → ℤ) (t : GU σ n),
      t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  intro L _ _ _ ϖ σ q n hU g
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  have hϖ : ϖ ≠ 0 := by
    intro h
    have hv := hU.2.2.2.1
    rw [h, Valuation.map_zero] at hv
    exact absurd hv WithZero.zero_ne_coe
  obtain ⟨t, ht, -⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i : Fin n => ϖ ^ d.getD i.1 0) fun i => by
      rw [map_zpow₀, hU.2.2.1, hd.rev, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))
  exact ⟨fun i => d.getD i.1 0, t, ht, k₁, h₁, k₂, h₂, e'⟩

section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {q n : ℕ}

theorem kerU_biInv {ϖ : L} (hU : IsUnramInv ϖ σ q) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU ϖ q N z φ)
    (g : GU σ n) {k₁ k₂ : GU σ n} (h₁ : k₁ ∈ KU σ n) (h₂ : k₂ ∈ KU σ n) : φ (k₁ * g * k₂) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L ϖ σ q n hU g
  rw [show k₁ * (a * t * b) * k₂ = (k₁ * a) * t * (b * k₂) by group, hφ d t ht _ (mul_mem h₁ ha) _ (mul_mem hb h₂),
    hφ d t ht a ha b hb]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem sph_eq (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ} {Φ : GD σ n → ℂ}
    (hΦ : IsSphSec σ q n χ s Φ) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU (ϖ : L) q N z φ)
    (hX : varX q n (χ ϖ) s = (z : ℂ) * ((q : ℂ) ^ N)⁻¹) (g : GU σ n) : Φ (io1 σ n g) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L (ϖ : L) σ q n hU g
  rw [_root_.GlobalTheory.UGraph.sphSec_io_diag L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb, hφ d t ht a ha b hb, hX]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem exists_unr_char (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) (z : ℂˣ) : ∃ χ : Lˣ →* ℂˣ, IsUnr χ ∧ χ ϖ = z := by
  refine ⟨{ toFun := fun u => z ^ Formalism.UG.ordL (u : L), map_one' := ?_, map_mul' := fun a b => ?_ }, fun u hu => ?_, ?_⟩
  · have : Formalism.UG.ordL (1 : L) = 0 := by simp [Formalism.UG.ordL]; rfl
    simp [this]
  · simp [Formalism.UG.P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, _root_.zpow_add]
  · have : Formalism.UG.ordL (u : L) = 0 := by
      have h0 : Valued.v (u : L) ≠ 0 := by rw [hu]; exact one_ne_zero
      have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, hu]; rfl)
      simp [Formalism.UG.ordL, h0, h1]
    simp [this]
  · have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (1 : ℤ)
    rw [zpow_one] at h
    simp [h]

theorem exists_haar (ϖ : L) (hU : IsUnramInv ϖ σ q) (n : ℕ) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] :
    ∃ μ : Measure (GU σ n), μ.IsHaarMeasure ∧ μ (KU σ n) = 1 := by
  haveI := GlobalTheory.LGrp.locallyCompact_GU_of_unram hU n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  let K₀ : TopologicalSpace.PositiveCompacts (GU σ n) :=
    ⟨⟨_, hc⟩, by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_eq' (q r : ℕ) (X y : ℂ) (α : Fin (r / 2) → ℂˣ) :
    closedForm q r X y α = eulerFac (bcParam r α) y * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X) := by
  rw [closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm y]
  rcases Nat.even_or_odd r with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem varXY_eq (q r t : ℕ) (hq : 2 ≤ q) (z : ℂ) :
    varX q r z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (r + t))⁻¹ ∧ varY q z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (t + 1))⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · rw [varX, show -(2 * ((t : ℂ) / 2) + r) = -(((r + t : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]
  · rw [varY, show -(2 * ((t : ℂ) / 2) + 1) = -(((t + 1 : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]

theorem tb_triv : ∀ (q r : ℕ), 2 ≤ q → ∀ α : Fin (r / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((r : ℤ) - 1 - 2 * (i.val : ℤ))) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α := by
  intro q r hq α hα i
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hn : ‖(α i : ℂ)‖ = (q:ℝ) ^ ((((r:ℤ) - 1 - 2 * (i.val:ℤ) : ℤ)) : ℝ) := by
    rw [hα, norm_zpow, Complex.norm_natCast, Real.rpow_intCast]
  have hi : 2 * i.val + 1 ≤ r := by have := i.2; omega
  have hi' : 2 * (i.val : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [Real.rpow_neg (by positivity), GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, hn, ← Real.rpow_neg (by positivity)]
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> push_cast <;> linarith

theorem dom_of_tb : ∀ (q r t : ℕ), 2 ≤ q → r ≤ t → ∀ (z : ℂ), ‖z‖ = 1 → ∀ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q z ((t : ℂ) / 2)) α := by
  intro q r t hq hrt z hz α hα
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq1' : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0:ℝ) < q := by linarith
  rw [(varXY_eq q r t hq z).2]
  have hy : ‖z * ((q:ℂ)^(t+1))⁻¹‖ = ((q:ℝ)^(t+1))⁻¹ := by
    rw [norm_mul, hz, one_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hB : ((q:ℝ)^2)^(((r:ℝ)-1)/2) ≤ (q:ℝ)^t := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have : (r:ℝ) ≤ t := (by exact_mod_cast hrt); linarith)
  have hBp : 0 < ((q:ℝ)^2)^(((r:ℝ)-1)/2) := by positivity
  have e : ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t = (q:ℝ)⁻¹ := by rw [pow_succ]; field_simp
  have key : ∀ a : ℝ, a ≤ (q:ℝ)^t → ((q:ℝ)^(t+1))⁻¹ * a < 1 := fun a ha =>
    calc ((q:ℝ)^(t+1))⁻¹ * a ≤ ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (q:ℝ)⁻¹ := e
      _ < 1 := inv_lt_one_of_one_lt₀ hq1'
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain, hy]
  refine ⟨by simpa using key 1 (one_le_pow₀ hq1), fun i => ⟨key _ ((hα i).2.trans hB), key _ ?_⟩⟩
  have h1 := (hα i).1
  rw [Real.rpow_neg (by positivity)] at h1
  have hαp : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  exact (inv_le_of_inv_le₀ hBp h1).trans hB


set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem hasSum_zetaSum_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hφ V _ _ ρ x α hx hα ℓ hℓ
  obtain ⟨C, hC⟩ := hℓ
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have h' := hU.2.2.2.1
    rw [h, map_zero] at h'
    exact WithZero.zero_ne_coe h'
  let ϖu : Lˣ := Units.mk0 ϖ hϖ0
  have hUu : IsUnramInv (ϖu : L) σ q := hU
  obtain ⟨χ, hχ, hχϖ⟩ := exists_unr_char ϖu hUu z
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq r hχ ((t : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := varXY_eq q r t hq2 (z : ℂ)
  have hX : varX q r (χ ϖu) ((t : ℂ) / 2) = (z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹ := by rw [hχϖ, hXe]
  have hΦφ : ∀ g, Φ (io1 σ r g) = φ g := sph_eq ϖu hUu hχ hΦ hφ hX
  letI : MeasurableSpace (GU σ r) := borel _
  haveI : BorelSpace (GU σ r) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := exists_haar ϖ hU r
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU r
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q r hU).1
  have hright : ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := fun g k hk => by
    simpa using kerU_biInv hU hφ g (one_mem _) hk
  have hdouble := _root_.GlobalTheory.InertZeta.unramDoublingInert L ϖu σ q r hUu μ hμK χ hχ _ Φ hΦ
  have hzχ : ((χ ϖu : ℂˣ) : ℂ) = z := by rw [hχϖ]
  have hdom : ∀ β : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r β →
      Domain (varY q (χ ϖu) ((t : ℂ) / 2)) β := fun β hβ => by
    rw [hzχ]; exact dom_of_tb q r t hq2 hrt z hz β hβ

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU r
  have hint1 := ((hdouble α0 _ hw0).1 (hdom α0 (tb_triv q r hq2 α0 hα0))).1
  have hintφ : Integrable φ μ := by simpa [hΦφ] using hint1

  obtain ⟨w, hw⟩ := _root_.GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal L ϖ σ q r hU α
  obtain ⟨hintw, hval, -⟩ := (hdouble α w hw).1 (hdom α hα)
  simp only [hΦφ] at hintw hval
  have hFw : ∀ g, ∀ k ∈ KU σ r, φ (g * k) * w (g * k) = φ g * w g := fun g k hk => by
    have h1 := hw.1 1 ⟨k, hk⟩ g
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [hright g k hk, h1]
  have hsw := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK _ hFw hintw).of_norm
  have hci := (_root_.GlobalTheory.InertZeta.cosetIntegral_holds _ μ (KU σ r) hKo hμK (fun g => φ g * w g) _ hFw hsw.hasSum).2
  have hS1 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * w a.out)
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α) := by
    rw [← hval, hci]; exact hsw.hasSum

  have hsφ := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK φ hright hintφ
  have hsψ : Summable (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) := by
    refine Summable.of_norm_bounded (hsφ.mul_left C) fun a => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

  have hm : ∀ g : GU σ r, dosetInd ℂ (KU σ r) g ∈ Formalism.UG.Hecke ℂ (KU σ r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  have hcond : ∀ g : GU σ r, Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
      Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 := fun g => by
    have h1 := hw.2.2 _ (hm g)
    have h2 := congrArg ℓ (hx.2.2 _ (hm g))
    rw [map_smul, smul_eq_mul] at h2
    have e1 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
        ℓ x * Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) w 1 := by
      unfold Formalism.UG.hAct
      rw [mul_finsum]
      exact finsum_congr fun c => by simp only [smul_eq_mul]; ring
    have e2 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 =
        ℓ (GlobalTheory.LFun.heckeVec ρ (KU σ r) (dosetInd ℂ (KU σ r) g) x) := by
      refine Eq.trans (finsum_congr fun c => ?_)
        (ℓ.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK (hm g) ρ x)).symm
      simp
    rw [e1, e2, h1, h2, mul_comm]
  have hswap := _root_.GlobalTheory.InertZeta.dosetSwap _ (KU σ r) hK φ (fun g => ℓ x * w g) (fun g => ℓ (ρ g x)) _
    (fun a b g => kerU_biInv hU hφ g a.2 b.2)
    (fun a b g => by simp only [hw.1 a b g]) hcond hsψ.hasSum
  have h2 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out))
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α * ℓ x) := by
    have h3 : (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out)) = fun a => φ a.out * w a.out * ℓ x :=
      funext fun a => by ring
    rw [h3]; exact hS1.mul_right (ℓ x)
  have e := hswap.unique h2
  rw [hX, hzχ, hYe, closedForm_eq'] at e
  rw [← e]
  exact hsψ.hasSum

end GlobalTheory.ZetaSumU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqSetIntegralTsumRationalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPlaces_not_isConjPlace_realDat : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.SeeConjPlaces.pg_not_isConjPl | exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl | (intros; apply GlobalTheory.SeeConjPlaces.pg_not_isConjPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.KFiniteDetermined

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_kFin_of_mem_lowT {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {v : M.sm τ} (hv : v ∈ lowT M τ) : (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ :=
  (sSup_le (a := GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) fun A hA _ hw => ⟨A, hA.1, hw, hA.2.1⟩) hv

theorem restrInj : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.RestrInj D :=
  fun D θ hθ V S M J χ T hT h0 =>
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D V S M θ hθ (GlobalTheory.LowTypeRestriction.lowT_ne_bot M) J χ T hT
      fun v => h0 _ fun τ => mem_kFin_of_mem_lowT M τ (v τ).2

end GlobalTheory.KFiniteDetermined
end

