module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0206
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.TrueGeo GlobalTheory.TrueCx
open scoped ContDiff

def cutoff (y : ℝ) : ℝ := Real.smoothTransition (3 - y) ^ 2

theorem cutoff_mem (y : ℝ) : cutoff y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem cutoff_of_le {y : ℝ} (h : y ≤ 2) : cutoff y = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le (by linarith), one_pow]

def cutWt (κ R r : ℝ) : ℝ := cutoff (Real.log r / Real.log R) / (1 + (r / R) ^ κ)

theorem cutWt_mem (κ : ℝ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) : cutWt κ R r ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Real.rpow_nonneg (div_nonneg hr hR) κ
  exact ⟨div_nonneg (cutoff_mem _).1 (by linarith), (div_le_one (by linarith)).2 ((cutoff_mem _).2.trans (by linarith))⟩

theorem cutWt_of_le (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) : cutWt κ R r = 1 / (1 + (r / R) ^ κ) := by
  have h1 := Real.log_le_log hr h
  rw [Real.log_pow] at h1
  rw [cutWt, cutoff_of_le ((div_le_iff₀ (Real.log_pos (by linarith))).2 (by exact_mod_cast h1))]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ)

def OddPrimesWithRootsOfUnity.eigMet : EigMet Z σ := .ofForm (x.met σ) (x.met_smooth σ).1

theorem OddPrimesWithRootsOfUnity.exp_le_r (y : CxPts (genStr Z) σ) : Real.exp 1 ≤ x.r σ y :=
  le_sub_self_iff _ |>.2 (Real.log_nonpos (sq_nonneg _) (pow_le_one₀
    (Finset.prod_nonneg fun i _ => ((x.nrm_div σ i).1 y).1)
    (Finset.prod_le_one₀ (fun i _ => ((x.nrm_div σ i).1 y).1) fun i _ => ((x.nrm_div σ i).1 y).2)))

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem xiR_pos (D : D7) : 0 < xiR D :=
  norm_embedding_xi_zero D D.host.φ₀ ▸ norm_pos_iff.2 ((map_ne_zero _).2 (cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))


variable (s) in
theorem FinalTheorems.im_neg_xi (σ : κ.c.F →+* ℂ) (k : (s.U σ).Comp) (τ : ((s.U σ).X k).Ψ) :
    (τ.1 (-((s.U σ).X k).ξ0)).im = xiR D := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · have h1 := A.im_neg_xi_neg τ.1 ((((s.unf σ h).1.2.1 k).2 _).1 τ.2)
    have h2 := s.xiAbs σ k τ.1
    rw [← s.xi_eq σ k] at h1
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.2 (GlobalTheory.FrameNormLie.re_xi _ _)] at h2
    rw [← h2, abs_of_pos (by simpa using h1)]
  · exact ((s.unif.isEmpty_comp h).false k).elim

namespace ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ)

def hodge : EigMet s.T.Z σ :=
  .hodge s.U (2 * Real.pi * xiR D) (mul_pos Real.two_pi_pos (xiR_pos D)) (x.eigMet σ)

variable {σ} {y : CxPts (genStr s.T.Z) σ}

theorem _root_.GlobalTheory.ShFam.FinalTheorems.exists_isHodgeFrame_iff : (∃ f, IsHodgeFrame s.U y f) ↔ ¬ LiesIn y (genBd s.T.Z) :=
  ⟨fun ⟨_, h⟩ => h.not_liesIn, exists_isHodgeFrame fun σ h => (s.unf σ h).1⟩

theorem hodge_gram {f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} (hf : IsHodgeFrame s.U y f)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ).gram y g τ = ((2 * Real.pi * xiR D : ℝ) : ℂ) • ((f.co g τ)ᴴ * f.co g τ) :=
  hf.gram_eq (fun σ h => (s.unf σ h).1) (xiR_pos D) s.im_neg_xi g τ

def IsMuExp (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ), ¬ LiesIn y (genBd s.T.Z) →
    ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ),
      x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ (star v ⬝ᵥ ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ).gram y g τ *ᵥ v).re ∧
        (star v ⬝ᵥ ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ).gram y g τ *ᵥ v).re ≤ x.r σ y ^ C * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re

def muExp : ℝ := Classical.epsilon x.IsMuExp

def kap : ℝ := 2 * x.muExp + 3


open Classical in
variable (σ) in
def wt (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : ℝ :=
  if LiesIn y (genBd s.T.Z) then 0 else cutWt x.kap (max R 2) (x.r σ y)

theorem wt_mem (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : x.wt σ R y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold wt
  split_ifs
  exacts [⟨le_rfl, zero_le_one⟩, cutWt_mem _ (le_max_of_le_right zero_le_two) ((Real.exp_pos 1).le.trans (x.exp_le_r σ y))]


variable (σ) in
def eigMetAt : Option ℝ → EigMet s.T.Z σ
  | none => (_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ
  | some R => .interp (x.wt σ R) (x.wt_mem R) (x.eigMet σ) ((_root_.GlobalTheory.ShFam.ToroidalCompactificationData.hodge x) σ)

end ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (Φ : s.Flag)

def metsOf : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL) := fun k R σ n => (Φ.C k).met (x.eigMetAt (embOf κ.e σ) R) n

def refMet : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n) :=
  fun k σ n => (Φ.C k).met (x.eigMet (embOf κ.e σ)) n

def rFlag : ∀ k σ, Pts (Φ.C k).Y σ → ℝ := fun k σ p => x.r (embOf κ.e σ) ((Φ.C k).down p)

variable (k : s.Comp) (R : Option ℝ) (σ : D.what₂.LL →+* ℂ) (n n' : Letter S.Dw → ℤ)

variable {x Φ k σ n} {p : Pts (Φ.C k).Y σ}

theorem pn_metsOf {g : (Φ.C k).FrameAt p} {f : (Φ.C k).Y.Fn} {a : ℂ} (h : IsCoord (Φ.C k) p.1 g n f a) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k R σ n) ((cxSt D.what₂.LL).cx _ σ f) p =
      ‖a‖ ^ 2 * ∏ z : Letter S.Dw, grSq ((x.eigMetAt _ R).gram _ g z.1) z.2 ^ n z := FlagCpt.pn_met _ _ h

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

end GlobalTheory.ShFam
end
end

