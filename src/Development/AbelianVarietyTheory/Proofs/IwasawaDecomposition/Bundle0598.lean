module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompMapAndFrDense
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDim
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernDegree

def gradedCoeff (σ : Type) : Subring (Polynomial (MvPolynomial σ ℂ)) where
  carrier := {p | ∀ k, (p.coeff k).IsHomogeneous k}
  mul_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun x hx => ?_
    have := (hp x.1).mul (hq x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hx] at this
  one_mem' := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simpa using isHomogeneous_one σ ℂ
    · rw [Polynomial.coeff_one, if_neg (by omega)]; exact isHomogeneous_zero _ _ _
  add_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_add]; exact (hp k).add (hq k)
  zero_mem' := by
    intro k
    rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  neg_mem' := by
    intro p hp k
    rw [Polynomial.coeff_neg]; exact (hp k).neg

theorem charpolyRev_coeff_isHomogeneous {σ r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r (MvPolynomial σ ℂ)) (hM : ∀ i j, (M i j).IsHomogeneous 1) (k : ℕ) :
    ((Matrix.charpolyRev M).coeff k).IsHomogeneous k := by
  have hent : ∀ i j, (1 - (Polynomial.X : Polynomial (MvPolynomial σ ℂ)) • M.map Polynomial.C) i j ∈ gradedCoeff σ := by
    intro i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Subring.sub_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · intro l
      rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h; exact hM i j
      · exact isHomogeneous_zero _ _ _
  have hdet : Matrix.charpolyRev M ∈ gradedCoeff σ := by
    rw [Matrix.charpolyRev, Matrix.det_apply']
    refine Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _) ?_
    exact Subring.prod_mem _ fun i _ => hent _ _
  exact hdet k

theorem chernPoly_isHomogeneous {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    (chernPoly G v k).IsHomogeneous k := by
  refine charpolyRev_coeff_isHomogeneous _ (fun i j => ?_) k
  rw [Matrix.neg_apply, curvPoly, Matrix.of_apply]
  exact (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    isHomogeneous_C_mul_X _ _).neg

theorem aeval_isWeightedHomogeneous {σ τ : Type} {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ ℝ} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) :
    IsWeightedHomogeneous w' (aeval g φ) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => g i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (algebraMap ℝ ℂ (AddMonoidAlgebra.coeff φ d))).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_apply]
  exact h3

theorem topCoeff_eq_zero {n d : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous d) (hd : d ≠ n) :
    topCoeff P = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hP.coeff_eq_zero, mul_zero]
  intro h
  apply hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, Finsupp.degree_eq_weight_one, map_sum]
  simp [Finsupp.weight_single]

end GlobalTheory.GoodMetric.ChernDegree


open GlobalTheory.GoodMetric.ChernDegree in
theorem GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous (n : ℕ) (ι : Type) (m : ι → ℕ)
    (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ)
    (hQ : MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d) (hd : d ≠ n) :
    chernTop Q G v = 0 := by
  have h : (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) Q).IsHomogeneous d :=
    aeval_isWeightedHomogeneous hQ _ fun x => chernPoly_isHomogeneous _ _ _
  rw [chernTop, topCoeff_eq_zero h hd, Complex.zero_re, mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityUnitAndAboveRank
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.GoodMetric

open Polynomial in
theorem chernPoly_zero' {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : chernPoly G v 0 = 1 := by
  rw [chernPoly, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

open Polynomial in
theorem chernPoly_above {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) (hk : Fintype.card r < k) : chernPoly G v k = 0 := by
  rw [chernPoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [← Matrix.reverse_charpoly]
  calc _ ≤ (Matrix.charpoly (-curvPoly G v)).natDegree := Polynomial.reverse_natDegree_le _
    _ = Fintype.card r := Matrix.charpoly_natDegree_eq_dim _
    _ < k := hk

theorem chernTop_unit : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  intro n ι m G v τ Q
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [chernTop, map_mul, map_sub, map_one, MvPolynomial.aeval_X, chernPoly_zero', sub_self, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]
  · have h := chernPoly_above (fun u => G u τ) v k (by simpa using hk)
    simp only [chernTop, map_mul, MvPolynomial.aeval_X, h, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open GlobalTheory.Mem.Db

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)


set_option maxHeartbeats 8000000 in
def nchTTr {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) :
    NchT w (setDivZ Z N h) Wt { nch with } :=
  { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }


set_option maxHeartbeats 8000000 in
def kerTr {Gt : GatTies (w.D Z)} {cmp : LatCmp (w.D Z)} {Gy : G.LatInst (w.D Z)} (k : KerFam (w.D Z) Gt cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) { Gt with } { cmp with } (w.tw (setDivZ Z N h)) { Gy with } :=
  fun u v g => { k u v g with }


set_option maxHeartbeats 8000000 in
def columnLocalDataTransportDivision (c : ColumnDataSplitPrimes K w Z)
    (hR : let t := DivTr.colTTr w Z N h c.toColT
          IsRecG K.s (w.D (setDivZ Z N h)) t.Gt t.cmp t.g.herm t.g.forms) :
    ColumnDataSplitPrimes K w (setDivZ Z N h) :=
  { DivTr.colTTr w Z N h c.toColT with isRec := hR, om := c.om }

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationArithmeticGroupInvariant
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnfInv

theorem one_mem_bor {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a b hab => ?_⟩
  · change ¬ (1 : Matrix (Fin r) (Fin r) ℂ).det = 0
    simp
  · simp [Matrix.one_apply, (ne_of_lt hab).symm]

theorem rmul_one {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    ReciprocityTheory.ChartRestriction.G.FD.rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = x τ
  rw [show ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = 1 from rfl,
    Matrix.mul_one]
  rfl

theorem psi_moebI_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ (flat (moebI γ (unflat v))) = ψ v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ γ hγ v hv
  obtain ⟨-, hk, -, h4, -⟩ := hU
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hk k).1]; omega
  haveI : IsOpenImmersion j := hL.1
  have hinj : Function.Injective (GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (cancel_mono j).1 this
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨x, hx, hxv⟩ := FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right Dw.p Dw.q)
    (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
  have hx' : ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x ∈ (U.X k).dom := GlobalTheory.Reg.GenericFrameDensity.lact_mem_dom _ hγ₀ hx
  have hdom : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x) =
      moebI (toUpq (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) γ₀) (unflat v) := by
    rw [domPt_lact (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 γ₀ hx]
    exact congrArg _ hxv
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨_, hx'⟩
  simp only at h1 h2
  rw [hxv] at h1
  rw [hdom] at h2
  apply hinj
  have h1' : GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj (ψ v) = cxPt T.Z (U.un k ⟨x, hx⟩) := h1
  rw [h2, h1']
  apply GlobalTheory.ShFam.cxPt_congr
  have hx'' : (⟨k, (⟨ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x, hx'⟩ : (U.X k).dom).1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) =
      ⟨k, ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ (⟨x, hx⟩ : (U.X k).dom).1)
        (fun _ => (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) ℂ))⟩ := by
    rw [rmul_one]
  obtain ⟨t, ht⟩ := (h4 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ₀, hγ₀, _, one_mem_bor _ _, hx''⟩
  exact ht.1

end GlobalTheory.UnfInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtCha
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifHolo

theorem unif_continuousOn_analyticAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) ∧ ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ w ∈ ch.e.source → AnalyticAt ℂ (fun w' => ch.e (ψ w')) w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  classical
  haveI : IsOpenImmersion j := hL.1
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) hp0 (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((GlobalTheory.TrueCx.TorHolo.differentiable_stdMat (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have key : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p),
      cxOf e σ hj (ψ v) = cxPt T.Z (U.un k (x (L v))) := by
    intro v hv
    have h1 := hψ (x (L v))
    have h2 : flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (x (L v)).1) = v := by
      show flat (domPt _ _ _ (stdFrame _ _ _ hp0 (unflat (L.symm (L v)))).1) = v
      rw [L.symm_apply_apply, domPt_stdFrame _ _ _ hp0 hv]
      rfl
    rw [h2] at h1
    exact h1
  have hcont : ContinuousOn (fun b => cxPt T.Z (U.un k (x b))) B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun W => ⟨?_, fun g => ?_⟩
    · have := (hY W 0).1.preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin _ → ℂ) ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ W} := ⟨v.2, hv⟩
      have hca := (((hY W g).2).differentiableAt (((hY W g).1).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hκ := isOpenEmbedding_cxOf e σ hj
  have hLB : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L v ∈ B := fun v hv => by
    show L.symm (L v) ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
    rwa [L.symm_apply_apply]
  have hψc : ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := by
    rw [hκ.isInducing.continuousOn_iff]
    exact (hcont.comp L.continuous.continuousOn hLB).congr fun v hv => key v hv
  refine ⟨hψc, fun w hw ch hch => ?_⟩
  have hS : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ch.e.source) :=
    hψc.isOpen_inter_preimage ho ch.e.open_source
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ?_ (hS.mem_nhds ⟨hw, hch⟩)
  refine differentiableOn_euclidean.2 fun a => ?_
  have hmaps : Set.MapsTo L (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ∩ ψ ⁻¹' ch.e.source)
      {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ ch.U)} := fun v hv => by
    refine ⟨hLB v hv.1, ?_⟩
    rw [← key v hv.1]
    exact le_preimage_cxOf e σ hj ch.U (ch.source_subset hv.2)
  refine ((hY (j ''ᵁ ch.U) ((j.appIso ch.U).inv.hom (ch.x a))).2.comp L.differentiableOn hmaps).congr
    fun v hv => ?_
  show ch.e (ψ v) a = valAt' (cxPt T.Z (U.un k (x (L v)))).1 (j ''ᵁ ch.U) ((j.appIso ch.U).inv.hom (ch.x a))
  rw [ch.apply_eq _ hv.2 a, ev_eq_valAt'_cxOf e σ hj _ _ (ch.source_subset hv.2), key v hv.1]

end GlobalTheory.UnifHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationFibreArithmeticGroupRelat
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifFibre

theorem fibre_gamma : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ v hv w hw hvw
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat v) hv
  obtain ⟨x', hx', hxw⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat w) hw
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨x', hx'⟩
  simp only at h1 h2
  rw [hxv, hflat] at h1
  rw [hxw, hflat] at h2
  have h3 : cxPt T.Z (U.un k ⟨x, hx⟩) = cxPt T.Z (U.un k ⟨x', hx'⟩) := by
    rw [← h1, ← h2, hvw]
  have h4 : (U.un k ⟨x, hx⟩).x = (U.un k ⟨x', hx'⟩).x := by
    have h5 := congrArg Subtype.val h3
    simp only [cxPt] at h5
    haveI := T.Z.jQ_open
    have h6 := (cancel_mono T.Z.jQ).1 h5
    have h7 := congrArg (· ≫ CategoryTheory.Limits.pullback.fst _ _) h6
    simp only [GlobalTheory.AllWt.ptF] at h7
    rwa [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst] at h7
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hG k ⟨x, hx⟩ _ h4
  obtain ⟨γ, hγ, b', hb', heq⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ ⟨x', hx'⟩).1 ⟨t, ht⟩
  have hx'eq : x' = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ (ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) b' :=
    eq_of_heq (Sigma.mk.inj_iff.1 heq).2
  refine ⟨GlobalTheory.TrueCx.toUpq (U.X k) hjr (Equiv.refl (U.X k).Ψ) γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩, ?_⟩
  rw [← hxv, ← hxw, hx'eq, GlobalTheory.TrueCx.domPt_rmul _ _ _ hb', GlobalTheory.TrueCx.domPt_lact _ _ _ hp γ hm]
  rw [hp] at hb0
  rw [GlobalTheory.PointOfFrames.domPt_rmul_block _ _ _ _ b hb hb0]

end GlobalTheory.UnifFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreSlotConstructionMonoFewerCoresBothPasses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

theorem row_mono_id {Bd : GlobalTheory.Fc.BdT} {Q Q₁ : V4.Slot} {Lk Lk₁ : GlobalTheory.Fc.LkT Bd} {H : ∀ 𝒜 : FamClass, GlobalTheory.Fc.RawSel Bd 𝒜 → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hL : ∀ K β c b, Lk₁ K β c b → Lk K β c b)
    (h : GlobalTheory.Fc.Row Q Lk H) : GlobalTheory.Fc.Row Q₁ Lk₁ H :=
  GlobalTheory.Fc.Row.map (fun _ _ _ b => b) hQ (fun K β c b _ t => hL K β c b t) h

theorem largeBaseProperty_anti {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ R : V4.Slot} (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c)
    (h : GlobalTheory.Fc.LargeBaseCondition KP Q R) : GlobalTheory.Fc.LargeBaseCondition KP Q₁ R :=
  GlobalTheory.Fc.eventuallyAllScaleContexts_mono_of_imp (fun _ H => H.imp fun _ _ _ _ t k C W V S N G c q => t k C W V S N G c (hQ _ _ _ _ _ q)) h

theorem eventually_coreProperty_mono_fewerCores {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q₁ Q' Q'₁ : V4.Slot} {r r₁ : V4.Slot → Prop}
    (hQ : ∀ K X f T c, Q₁ K X f T c → Q K X f T c) (hQ' : ∀ K X f T c, Q'₁ K X f T c → Q' K X f T c)
    (hr : ∀ S S₁ : V4.Slot, (∀ K X f T c, S₁ K X f T c → S K X f T c) → r S → r₁ S₁)
    (h : GlobalTheory.Fc.Lg1 KP Q Q' r) : GlobalTheory.Fc.Lg1 KP Q₁ Q'₁ r₁ := by
  obtain ⟨R, hR, h⟩ := h
  exact ⟨R, largeBaseProperty_anti hQ hR, hr _ _ (fun _ _ _ _ _ t => ⟨hQ' _ _ _ _ _ t.1, t.2⟩) h⟩

end GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedFormsStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_siegel_basis_balanced_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  first | exact @GlobalTheory.RedTh.exists_adapted_siegel_basis | exact GlobalTheory.RedTh.exists_adapted_siegel_basis | (intros; apply GlobalTheory.RedTh.exists_adapted_siegel_basis <;> assumption)
end

