module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Formalism.SharpRestriction.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceStepZeroChartsGoodStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoice_stepZero_charts_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ Kc : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1) ∧ (∀ β, (Kc β).lev.Lb = F.to0.cls0.lev.Lb ∧ (Kc β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (Kc β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (Kc β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (Kc β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((Kc ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.charts_zero_good | exact GlobalTheory.TwU.AtTrue.charts_zero_good | (intros; apply GlobalTheory.TwU.AtTrue.charts_zero_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
section
noncomputable section

namespace GlobalTheory.AtG

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem row_atG_of_jetSplitAmb : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) →
    Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  intro hJ Bd Q Lk hE
  refine ⟨_, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  obtain ⟨xs, hxs⟩ := _root_.GlobalTheory.AtG.KernelSizes.sizeAt_of_params eps he (by linarith)
  refine ⟨⟨0, fun _ => 0, fun _ => 2, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  have hg : (2 : ℝ) ≤ Fm.cX.err.g := hL.2.2.1 Fm.cX.err.g (by simp [FamP.cMid])
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  refine ⟨1, ⟨xs, fun x hx hx0 i => ?_⟩, Formalism.MainNotions.J.family_type_prime_loss Fm zero_le_one (by linarith)⟩
  refine _root_.GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement hJ (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (Fm.X x i) (t x hx i).2 ?_
  exact hxs (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) (Fm.L_eps x i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.AtG

end
end

