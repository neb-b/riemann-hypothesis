module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi

variable {D : D7}

structure SBes.FrameAt {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (μ lam : D.host.E) : Prop where
  ne : μ ≠ 0
  sign : lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)
  e : B.d.e = GlobalTheory.Core.SBesEx.eM X h μ lam
  e' : B.d.e' = GlobalTheory.Core.SBesEx.e'M X h μ lam
  z : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u)

def SBes.FrameTied {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam, B.FrameAt μ lam

namespace LatMatch

def NormOneAt (v : GlobalTheory.FinPl.Pl D) (c : AE D) : Prop := c * cA D c = 1 ∧ c - 1 ∈ idAt D (· = v)

def CenAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (a : GA D S) : Prop := a ∈ grpAt S (· = v) ∧ a ∈ Subgroup.center (GA D S)

def SMoves (S : HSp D) (c : AE D) (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S L (· = v) ↔ c • (Formalism.L2.Theta.mt S g *ᵥ y) ∈ latV S M (· = v))

def LastAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S)
    (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, a ∈ idAt D (· = v) → a • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) : Lat S₀ :=
  L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))

theorem mem_coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (x : Fin S₀.rank → D.host.E) :
    x ∈ coreLat d L ↔ d.i₀ *ᵥ x ∈ L := Iff.rfl

abbrev latS (D : D7) : Lat (D.sp.Y 0) := Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0

abbrev lat0 {u : D.what₂.Word} (F : Formalism.L2.Forms.Forms0 D u) : Lat (D.sp.X 0) :=
  F.cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
    (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))

def LineAt {S : HSp D} (z : Fin S.rank → D.host.E) (μ : D.host.E) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV z ∈ latV S M (· = v) ↔ incA D μ * a ∈ intAt D (· = v)

def SplitsAt {S A L : HSp D} (o : OrthDec S A L) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S M (· = v) ↔ o.jA *ᵥ (o.pA *ᵥ y) ∈ latV S M (· = v) ∧ o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v))

def TraceAt {S A L : HSp D} (o : OrthDec S A L) (g : GA D A) (N : Lat A) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV A N (· = v) ↔ o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ y) ∈ latV S M (· = v))

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def atW (p : SplitPt D k) {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) k :=
  x.map fun a => p.pr (incA D a)

def WShape (p : SplitPt D k) {S S₀ A Ln : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln)
    (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (α α' : Fin ρ → k) (γ : k) (g : GA D A) (N : Lat A) : Prop :=
  ∀ (x x' : Fin ρ → k) (t : k) (y : Fin A.rank → k),
    (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) ∈ latV S L (· = p.v) ↔
      (∀ a, α a * x a ∈ 𝒪[k]) ∧ (∀ a, α' a * x' a ∈ 𝒪[k]) ∧ γ * t ∈ 𝒪[k] ∧ (fun r => p.sec (y r)) ∈ latV A N (· = p.v)

def GluedW {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1))
    (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n) : Prop :=
  ∀ x : n ⊕ Fin 1 → k, (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
    Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec

end Split

theorem normOneAt_one (v : GlobalTheory.FinPl.Pl D) : NormOneAt v (1 : AE D) := ⟨by simp, by simp⟩

theorem sMoves_one {S : HSp D} (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : SMoves S 1 g L M v ↔ Moves S g L M (· = v) := by
  simp only [SMoves, Moves, one_smul]

end LatMatch

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OtherPlacesConvolutionFiniteAwayOrthogonal
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

namespace GlobalTheory.QVal.InnerSupp

variable {D : D7}

theorem placeIdem_self {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hαα : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α) = evalV D.host.F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α) = ((0 : Ainf D.host.F), α)
  rw [Prod.mk_mul_mk, mul_zero, hαα]

theorem idem_sq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [heq, ← map_mul, placeIdem_self hε]

theorem support_aconv {G : Type} [AddMonoid G] (P : G → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) :
    ∀ l : List (G →₀ ℂ), (∀ c ∈ l, ∀ u ∈ c.support, P u) → ∀ u ∈ (aconv l).support, P u := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ u hu
    have h := Finsupp.support_single_subset (show u ∈ (Finsupp.single (0 : G) (1 : ℂ)).support from hu)
    rw [Finset.mem_singleton] at h
    subst h
    exact h0
  | cons e l ih =>
    intro hl u hu
    have hu' : u ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support := hu
    have h1 := Finsupp.support_sum hu'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g, hg, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨h, hh, h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    subst h5
    exact hadd g h (hl e (List.mem_cons.2 (Or.inl rfl)) g hg)
      (ih (fun c hc => hl c (List.mem_cons.2 (Or.inr hc))) h hh)

theorem side {A T : HSp D} (E₀ : AE D) (hc : cA D E₀ = E₀) (hsq : E₀ * E₀ = E₀) (c₀ : WO A T →₀ ℂ)
    (l : List (WO A T →₀ ℂ)) (h₀ : ∀ x ∈ c₀.support, IsHalf E₀ x)
    (hl : ∀ c ∈ l, ∀ u ∈ c.support, (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0) :
    IsFinComb (aconv l) ∧ (∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u) ∧
      ∀ x ∈ c₀.support, ∀ y ∈ (aconv l).support, symplO A T x y = 0 := by
  have key := support_aconv (fun u : WO A T => (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0)
    ⟨fun a b => by rw [Matrix.zero_apply, mul_zero], by ext a b; simp⟩
    (fun u u' hu hu' => ⟨fun a b => by rw [Matrix.add_apply, mul_add, hu.1 a b, hu'.1 a b, add_zero], by
      ext a b
      have e1 := congrFun (congrFun hu.2 a) b
      have e2 := congrFun (congrFun hu'.2 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.add_apply] at e1 e2 ⊢
      rw [map_add, e1, e2, add_zero]⟩) l hl
  have half : ∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u := fun u hu a b => by
    rw [sub_mul, one_mul, (key u hu).1 a b, sub_zero]
  refine ⟨fun u hu => (key u hu).2, half, fun x hx y hy => ?_⟩
  exact GlobalTheory.HeisComb.symplO_half A T E₀ (1 - E₀) x y hc (by rw [mul_sub, mul_one, hsq, sub_self]) (h₀ x hx) (half y hy)

end GlobalTheory.QVal.InnerSupp


open GlobalTheory.QVal.InnerSupp in
theorem GlobalTheory.QVal.inner_supp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  intro D ψ σ S r Q hinj
  have hv : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  obtain ⟨hc, -, horth⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q 0).k (Q 0).q
  have hsq := idem_sq (Q 0).q
  have kill : ∀ (i : Fin r) {m n : ℕ} (u : Mx D m n), IsHalf ((Q i.succ).q.e + cA D (Q i.succ).q.e) u →
      (∀ a b, ((Q 0).q.e + cA D (Q 0).q.e) * u a b = 0) ∧ u.map (infPart D) = 0 := by
    intro i m n u hu
    obtain ⟨-, hinf, -⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q i.succ).k (Q i.succ).q
    refine ⟨fun a b => ?_, (hinf (fun _ => True) trivial m n u hu).2⟩
    rw [← hu a b, ← mul_assoc, horth (Q i.succ).k (Q i.succ).q (hv i), zero_mul]
  refine ⟨side _ hc hsq (Q 0).D₁ _ (fun x hx => (Q 0).dat₁.1 x hx) ?_, side _ hc hsq (Q 0).D₂ _ (fun x hx => (Q 0).dat₂.1 x hx) ?_⟩
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₁.1 u hu)
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₂.1 u hu)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw

abbrev conjR (D : D7) : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv

def conjFI (D : D7) : FI D ≃+* FI D :=
  FractionalIdeal.ringEquivOfRingEquiv D.host.E D.host.E (NumberField.RingOfIntegers.mapRingEquiv (conjR D))

theorem conj_conj_host (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← bridge_star_holds D.R D.host, ← bridge_star_holds D.R D.host, star_star]

theorem fracEquiv_conj (D : D7) (x : D.host.E) :
    IsFractionRing.ringEquivOfRingEquiv (K := D.host.E) (L := D.host.E)
      (NumberField.RingOfIntegers.mapRingEquiv (conjR D)) x = D.host.conj x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_div₀]
  rfl

theorem mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : x ∈ conjFI D 𝔞 ↔ D.host.conj x ∈ 𝔞 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg D.host.conj (fracEquiv_conj D y)).trans (conj_conj_host D y)
    exact h.symm ▸ hy
  · intro h
    exact ⟨D.host.conj x, h, (fracEquiv_conj D _).trans (conj_conj_host D x)⟩

theorem conj_mem_conjFI {D : D7} {𝔞 : FI D} {x : D.host.E} : D.host.conj x ∈ conjFI D 𝔞 ↔ x ∈ 𝔞 := by
  rw [mem_conjFI, conj_conj_host]

theorem conjFI_AA (D : D7) : conjFI D D.host.AA = D.host.AAbar := by
  ext x
  rw [mem_conjFI]
  refine ⟨fun h => ?_, fun h => Formalism.L2.Pj.conj_mem_AA D h⟩
  simpa only [conj_conj_host] using Formalism.L2.Pj.conj_mem_AAbar D h

theorem conjFI_AA_zpow (D : D7) (n : ℤ) : conjFI D (D.host.AA ^ n) = D.host.AAbar ^ n := by
  rw [map_zpow₀, conjFI_AA]

theorem cA_tmul (D : D7) (α : AF D.host.F) (a : D.host.E) :
    cA D (α ⊗ₜ[D.host.F] a) = α ⊗ₜ[D.host.F] D.host.conj a := by
  change α ⊗ₜ[D.host.F] star a = _
  rw [bridge_star_holds D.R D.host]

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rw [cA_tmul, cA_tmul, conj_conj_host]

theorem cA_mem_idV {D : D7} {𝔞 : FI D} {v : Pl D} {s : AE D} (hs : s ∈ idV 𝔞 v) :
    cA D s ∈ idV (conjFI D 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (conjFI D 𝔞) v).comap (cA D).toAddMonoidHom := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hv, a, ha, rfl⟩
    show cA D _ ∈ idV (conjFI D 𝔞) v
    rw [cA_tmul]
    exact AddSubgroup.subset_closure ⟨α, hα, hv, D.host.conj a, conj_mem_conjFI.2 ha, rfl⟩
  exact hle hs

theorem idV_cA_iff (D : D7) (v : Pl D) (𝔞 : FI D) (s : AE D) :
    s ∈ idV 𝔞 v ↔ cA D s ∈ idV (conjFI D 𝔞) v := by
  refine ⟨cA_mem_idV, fun h => ?_⟩
  have h2 := cA_mem_idV h
  rwa [cA_cA, show conjFI D (conjFI D 𝔞) = 𝔞 from by ext x; rw [mem_conjFI, conj_mem_conjFI]] at h2

theorem idV_AA_zpow_conj : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D),
    s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  intro D v n s
  rw [idV_cA_iff D v, conjFI_AA_zpow]

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7}

def tens {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : WO S T → ℂ := fun t => Φ (t - b • t) * Ψ (b • t)

theorem tens_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) (t : WO S T) :
    tens b Φ Ψ t = Φ (t - b • t) * Ψ (b • t) := rfl

def tensL {S T : HSp D} (b : AE D) (Ψ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := tens b Φ Ψ
  map_add' Φ Φ' := by funext t; simp only [tens, Pi.add_apply, add_mul]
  map_smul' c Φ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

def tensR {S T : HSp D} (b : AE D) (Φ : WO S T → ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := tens b Φ Ψ
  map_add' Ψ Ψ' := by funext t; simp only [tens, Pi.add_apply, mul_add]
  map_smul' c Ψ := by funext t; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensL_apply {S T : HSp D} (b : AE D) (Ψ Φ : WO S T → ℂ) : tensL b Ψ Φ = tens b Φ Ψ := rfl

theorem tensR_apply {S T : HSp D} (b : AE D) (Φ Ψ : WO S T → ℂ) : tensR b Φ Ψ = tens b Φ Ψ := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def eSum (p : ι → SplitPt D k) (J : List ι) : AE D := (J.map fun i => (p i).e).sum

theorem eSum_cons (p : ι → SplitPt D k) (i : ι) (J : List ι) : eSum p (i :: J) = (p i).e + eSum p J := by
  simp [eSum]


open Classical in
def datJ (p : ι → SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}
    (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (J : List ι) (t : WO S T) : ℂ :=
  if IsHalf (eSum p J) t then (J.map fun i => Ψ i (rd (α i) (β i) t)).prod else 0

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  rw [← p.sec_one, p.pr_sec]

theorem pr_of_mul_eq_zero (p : SplitPt D k) {a : AE D} (h : p.e * a = 0) : p.pr a = 0 := by
  have := congrArg p.pr h
  rwa [map_mul, pr_e, one_mul, map_zero] at this

theorem mul_eSum (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, a * (p j).e = 0) : a * eSum p J = 0 := by
  induction J with
  | nil => simp [eSum]
  | cons j J ih =>
    rw [eSum_cons, mul_add, h j (List.mem_cons_self), ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), add_zero]

theorem eSum_mul (p : ι → SplitPt D k) (a : AE D) (J : List ι) (h : ∀ j ∈ J, (p j).e * a = 0) : eSum p J * a = 0 := by
  rw [mul_comm]; exact mul_eSum p a J fun j hj => by rw [mul_comm]; exact h j hj

theorem eSum_idem (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup) :
    eSum p J * eSum p J = eSum p J := by
  induction J with
  | nil => simp [eSum]
  | cons i J ih =>
    rw [List.nodup_cons] at hJ
    have h1 : (p i).e * eSum p J = 0 := mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    have h2 : eSum p J * (p i).e = 0 := by rw [mul_comm, h1]
    rw [eSum_cons, add_mul, mul_add, mul_add, (p i).split.1, h1, h2, ih hJ.2, add_zero, zero_add]

theorem pr_eSum (p : ι → SplitPt D k) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (J : List ι) (hJ : J.Nodup)
    (i : ι) (hi : i ∈ J) : (p i).pr (eSum p J) = 1 := by
  induction J with
  | nil => simp at hi
  | cons j J ih =>
    rw [List.nodup_cons] at hJ
    rw [eSum_cons, map_add (f := _)]
    by_cases hij : i = j
    · subst hij
      rw [pr_e, pr_of_mul_eq_zero (p i) (mul_eSum p _ J fun j hj => horth i j fun h => hJ.1 (h ▸ hj)), add_zero]
    · rw [pr_of_mul_eq_zero (p i) (horth i j hij), zero_add, ih hJ.2 ((List.mem_cons.1 hi).resolve_left hij)]

end GlobalTheory.FinPl.PutIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RallisInnerProductConvergentOfWeilSiegelFormula
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Proof.Corev

theorem convergent_both_orientations :
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D := by
  intro hR hW hE D ψ θ A B χA χB sA sB t cA o K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  cases o with
  | false => exact _root_.GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht hK hm hν hf₁ hf₂
  | true =>
    obtain ⟨_, _, _, hθ, _, _, hA, hB, _⟩ := id hS
    exact _root_.GlobalTheory.Core.Rk.IP.innerProduct_convergent_conj hR hW hE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hρ ht
      (_root_.GlobalTheory.KernelFlip.kernelPair_flip D ψ θ A B χA χB sA sB K₁ K₂ c hθ hA hB hK) hm hν hf₁ hf₂

end GlobalTheory.Proof.Corev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

def RdAt {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

end GlobalTheory.MovedDat

end
end

