module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjRationalPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginDatumValueHalfIntegerPowPlaceAA
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Flat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem flatTensor_moved_box (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod *
      ∏ j, ∏ v, ((nabs k (ϖ ^ boxExp G a a' j v) : ℝ) : ℂ) := by
  set P := ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod
  have key : flatIntegrand hs ψ (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
      (box G ϖ a a').indicator fun _ => P := by
    funext e
    rw [flatIntegrand, moved_false, GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator G hs ϖ a a' g hg e]
    by_cases he : e ∈ box G ϖ a a'
    · have h1 := GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box G ϖ a a' e he
      rw [Set.indicator_of_mem he, Set.indicator_of_mem he, hψ _ (by rwa [Valuation.map_neg])]
      simp only [Pi.one_apply, mul_one, Circle.coe_one, P]
    · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]
      simp
  rw [flatTensor, key, integral_indicator_const _ (measurableSet_box G ϖ a a'), Measure.real, vol_box G ν hν ϖ a a',
    Complex.real_smul, mul_comm]
  push_cast
  rfl

end Flat
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_box_apow (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    apow ϖ (-(expo G a a' : ℂ) / 2) := by
  classical
  have hn : ∀ x : kˣ, ((nabs k x : ℝ) : ℂ) = apow x 1 := fun x => by simp [apow]
  rw [flatTensor_moved_box G hs ψ ν hν ϖ a a' hψ g hg]
  simp_rw [gdet_eq ϖ a a' g hg hg', ← _root_.zpow_neg, apow_zpow, ← apow_add, hn, apow_zpow, prod_apow_finset,
    prod_apow_list, ← apow_add]
  congr 1
  have hl : ∀ l : List Edge, (l.map fun b => ((-vtxDet G a a' b.src : ℤ) : ℂ) * ((G.rank b.tgt : ℂ) / 2) +
      ((-vtxDet G a a' b.tgt : ℤ) : ℂ) * (-(G.rank b.src : ℂ) / 2)).sum =
      -(((l.map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum : ℤ) : ℂ) / 2 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  rw [hl, expo]
  push_cast
  simp only [mul_one]
  ring

end Expo
end GlobalTheory.OriginBox
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k]

theorem colDiag_eq_one (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) {j : ℕ} (hj : G.m - 1 ≤ j) :
    colDiag G ϖ a a' j = 1 := by
  refine Units.ext ?_
  rw [colDiag, diagGL_val, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  have h := topRank_add hs j
  have hx := x.2
  rw [vtxExp, if_neg (by omega), zpow_zero, Units.val_one]

end Generic

variable {D : D7}

theorem aaElt_eq (w : Pl D.host.E) (j : ℕ) :
    aaElt w j = colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  refine Units.ext ?_
  rw [aaElt, colDiag, diagGL_val, diagGL_val]
  congr 1
  funext x
  have h := topRank_add (G := bareGrid w) one_le_sLen j
  have hx := x.2
  simp only [vtxExp]
  split_ifs with h1
  · simp only [genAt, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add, Units.val_zpow_eq_zpow_val]
    congr 1
    have : x.val - topRank (bareGrid w) j < D.R.m - 1 - j := by
      change topRank (bareGrid w) j + D.R.m = (bareGrid w).rank ((bareGrid w).m, j) + j + 1 at h
      change (x : ℕ) < (bareGrid w).rank ((bareGrid w).m, j) at hx
      omega
    change _ = _ * (((D.R.m - 1 - j : ℕ) : ℤ) - _) - _
    push_cast [Nat.sub_sub]
    rw [show D.R.m - (1 + j + (x.val - topRank (bareGrid w) j)) = D.R.m - (1 + j) - (x.val - topRank (bareGrid w) j) by omega,
      Nat.cast_sub (by omega)]
    ring
  · simp

theorem aaElt_elt_col (w : Pl D.host.E) (j : ℕ) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) ((bareGrid w).m, j) =
    colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  unfold Reps.elt
  rw [onColumn_apply]
  cases j with
  | zero => exact aaElt_eq w 0
  | succ i =>
    simp only [Reps.through]
    split_ifs with h
    · exact aaElt_eq w (i + 1)
    · exact (colDiag_eq_one _ one_le_sLen _ _ _ (by omega)).symm

theorem aaElt_elt_off (w : Pl D.host.E) (i j : ℕ) (hi : i ≠ (bareGrid w).m) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (i, j) = 1 := by
  simp [Reps.elt, onColumn, hi]

theorem rank_le_bigN (w : Pl D.host.E) (i j : ℕ) (hi : i ≤ (bareGrid w).m) (hj : j ≤ (bareGrid w).m) :
    (bareGrid w).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  change i ≤ D.R.m at hi
  change j ≤ D.R.m at hj
  nlinarith

theorem aaTerm_datum_origin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), (∀ a : Kw w, valuation (Kw w) a ≤ valuation (Kw w) ((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ) : Kw w) → psiAt W w a = 1) → ∃ n : ℤ, (aaTerm W w).datum 0 0 = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧ |n| ≤ 8 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  intro D T L sc G W w hψ
  have hψ' : ∀ y : Kw w, valuation (Kw w) y ≤ valuation (Kw w) (((unifAt w) ^ (FractionalIdeal.count D.host.E w D.host.AA +
      FractionalIdeal.count D.host.E w D.host.AAbar) : (Kw w)ˣ) : Kw w) → psiAt W w y = 1 := fun y hy =>
    hψ y (by rwa [genAt, genAt, ← _root_.zpow_add])
  have key := flatTensor_moved_box_apow (bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (isUnitVol_unitVol w) (unifAt w)
    _ _ hψ' _ (aaElt_elt_col w) (aaElt_elt_off w)
  refine ⟨expo (bareGrid w) (FractionalIdeal.count D.host.E w D.host.AA) (FractionalIdeal.count D.host.E w D.host.AAbar),
    ?_, _root_.GlobalTheory.OriginBox.abs_expo_le (bareGrid w) one_le_sLen _ _ (bigN D) (rank_le_bigN w)⟩
  change flatTensor _ _ _ _ 0 0 = _
  rw [aaVac, genAt] at *
  rw [key, IsUnif.apow_eq (isUnif_unifAt w)]
  congr 1
  ring

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem isConn_of_retract {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Nontrivial O] {G H : PDivGroup p O}
    (f : H ⟶ G) (r : G ⟶ H) (h : f ≫ r = 𝟙 H) (hG : GlobalTheory.PDivLat.IsConn G) : GlobalTheory.PDivLat.IsConn H := by
  intro n
  have hs : Function.Surjective (f.app n) := fun a => ⟨r.app n a, by
    have := congrArg (fun g => Hom.app g n) h
    exact DFunLike.congr_fun this a⟩
  haveI : Nontrivial (H.A n) :=
    (Bialgebra.counitAlgHom O (H.A n) : H.A n →+* O).domain_nontrivial
  haveI := hG n
  exact IsLocalRing.of_surjective' (f.app n : G.A n →+* H.A n) hs

theorem hasDatum_of_conn_dual_conn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hyp G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨G₁, G₂, hs, hc₁, hk₂⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G
  obtain ⟨H₁, H₂, hs', hcH, hkH⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G₁.dual
  obtain ⟨i₁, -, q₁, -, e₁, -⟩ := id hs'
  have hD : GlobalTheory.PDivLat.IsConn H₁.dual :=
    isConn_of_retract (dualHom _ _ q₁ ≫ G₁.bidual.inv) (G₁.bidual.hom ≫ dualHom _ _ i₁)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, ← dualHom_comp, e₁, dualHom_id]) hc₁
  have dD := GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε _ _ _ hs' (hyp H₁ hcH hD)
    (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε H₂ hkH)
  have d₁ := GlobalTheory.PDivLat.hasDatum_of_iso p C v O hv ε hε _ _ ⟨G₁.bidual.symm⟩
    (GlobalTheory.DualDatum.hasDatum_dual p C v O hv ε hε _ dD)
  exact GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε G G₁ G₂ hs d₁ (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε G₂ hk₂)

end GlobalTheory.PDivLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruence
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevGeo.Reps

theorem core (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ)
    (hK : IsLevelK V M Kf) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hm : ∀ k, ModelW V hr (X k)) :
    ∃ (G : Matrix (Fin r) (Fin r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
      (g : Comp → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
      (Λk : Comp → Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (u : Comp → (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
      GlobalTheory.UCls.SelfDualLat G Λ ∧
      (∀ k, (X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧
        (Λk k : Set (Fin r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin r → D.host.E)) ∧
        (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin r → D.host.E)) = ⊤ ∧
        (∀ τ ∈ (X k).Ψ, gram τ G (u k τ) = G.map τ) ∧
        (∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) ∧
          ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
        ∀ γ' : GL (Fin r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k,
            (γ' : Matrix (Fin r) (Fin r) D.host.E).mulVec x - x = M • y) →
          ∃ γ ∈ (X k).Γ, ∀ τ ∈ (X k).Ψ, u k τ * (γ : Matrix (Fin r) (Fin r) D.host.E).map τ =
            (γ' : Matrix (Fin r) (Fin r) D.host.E).map τ * u k τ) ∧
      ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin r → D.host.E)) M (g k) (g k') → k = k' := by
  subst hr
  classical
  obtain ⟨x0, hx0, hact⟩ := hD.2.2.1
  choose gA hgA using fun c => (hx0 c).2
  have hG : ∀ k, (X k).Gm = -(V.gram)ᵀ := fun k => by
    have := (hm k).1
    simpa [Matrix.reindex_apply] using this
  have hL := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  choose Λk hΛk using fun k => _root_.GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (finHom V (gA k))
    hL.2.2.1 hL.2.2.2.1
  refine ⟨-(V.gram)ᵀ, GlobalTheory.Member.latC V, fun k => (finHom V (gA k)).1, Λk,
    fun k τ => if h : τ ∈ (X k).Ψ then archM V (th k ⟨τ, h⟩) (gA k) else 1, _root_.GlobalTheory.Member.selfDualLat_neg_gram_transpose D V, fun k => ?_, ?_⟩
  · refine ⟨hG k, _root_.GlobalTheory.FinUA.isUA_finHom D V (gA k), (hΛk k).1, (hΛk k).2.1, (hΛk k).2.2.1, ?_, ?_, ?_⟩
    · intro τ hτ
      simp only [dif_pos hτ]
      exact _root_.GlobalTheory.ArchUnit.gram_archM D V τ _ (hth k ⟨τ, hτ⟩) (gA k)
    · intro γ hγ
      obtain ⟨γ', h1, h2⟩ := _root_.GlobalTheory.MsRepsFwd.conj_rat_congr D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 γ hγ
      refine ⟨γ', h1, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
    · intro γ' hγ'
      obtain ⟨γ, hγ, h2⟩ := _root_.GlobalTheory.RepConv.conj_mem_of_cong D V Comp X dict Kf th M x0 hK hth hD (fun c => (hx0 c).1) hact hG k (gA k)
        (hgA k) (Λk k) (hΛk k).1 (hΛk k).2.2.2 γ' hγ'
      refine ⟨γ, hγ, fun τ hτ => ?_⟩
      simp only [dif_pos hτ]
      exact h2 τ hτ
  · exact _root_.GlobalTheory.RepsInj.reps_inj D V Comp X dict Kf th M gA hK hth hD (fun k => by rw [hgA k])

end GlobalTheory.LevGeo.Reps

theorem GlobalTheory.LevGeo.Reps.components_double_cosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (g : (U σ).Comp → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (Λk : (U σ).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (u : (U σ).Comp → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ k, ((U σ).X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧ (Λk k : Set (Fin D.R.r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin D.R.r → D.host.E)) ∧ (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin D.R.r → D.host.E)) = ⊤ ∧ (∀ τ ∈ ((U σ).X k).Ψ, gram τ G (u k τ) = G.map τ) ∧ (∀ γ ∈ ((U σ).X k).Γ, ∃ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) ∧ ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) → ∃ γ ∈ ((U σ).X k).Γ, ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin D.R.r → D.host.E)) l.M (g k) (g k') → k = k' := by
  intro D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨Kf, th, hr, hK, hth, hD, -⟩ := hL.dictU σ hσ
  obtain ⟨hr', hm⟩ := hL.modelW σ hσ
  exact GlobalTheory.LevGeo.Reps.core D (D.sp.W j) D.R.r hr (U σ).Comp (U σ).X (dict σ) Kf th l.M hK hth hD hm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVector
section
open NumberField

namespace GlobalTheory

theorem latRank_one_eq_ideal_smul {K : Type} [Field K] [NumberField K] {m : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) :
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  intro hr hfg
  unfold ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hr
  have hvW : (w : Fin m → K) ≠ 0 := by
    intro h; exact hw0 (Subtype.ext h)
  have hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K) := by
    intro e he
    obtain ⟨c, hc⟩ := hw ⟨e, Submodule.subset_span he⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    exact this.symm
  let f : K →ₗ[𝓞 K] (Fin m → K) :=
    { toFun := fun β => β • (w : Fin m → K)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun r b => by
        simp only [RingHom.id_apply]
        exact smul_assoc r b _ }
  have hf : ∀ β, f β = β • (w : Fin m → K) := fun _ => rfl
  have finj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have : (a - b) • (w : Fin m → K) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvW
  refine ⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f finj
    have : (ell.comap f).map f = ell := by
      apply le_antisymm (Submodule.map_comap_le _ _)
      intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    rw [this]; exact hfg
  · intro hbot
    apply hw0
    have hell : ell = ⊥ := by
      rw [eq_bot_iff]; intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      have : β ∈ ell.comap f := he
      rw [hbot, Submodule.mem_bot] at this
      simp [this]
    have hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥ := by simp [hell]
    have h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0 := by
      rw [hW]; intro x hx; exact (Submodule.mem_bot K).mp hx
    exact Subtype.ext (h0 _ w.2)
  · intro e
    constructor
    · intro he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact hβ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RestPure

theorem evFin_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) :
    evFin F v (z i) = 0 := by

  have hu : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  have h := congrFun (hz _ hu) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 := congrArg (evFin F v) h
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem rest_evI_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  intro F _ _ κ _ φ hφ hcof f
  refine ⟨fun x z hz => ?_, ?_⟩
  ·
    have hc : ∀ v i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
      rw [Pi.add_apply, map_add (f := _), evFin_eq_zero z hz v i, add_zero]
    simp only [hc]
  ·
    have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        SB (κ → FiniteAdeleRing (𝓞 F) F) :=
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩
    show _ ∈ Submodule.span ℂ _
    exact Submodule.subset_span ⟨f, _, hg, rfl⟩

end GlobalTheory.RestPure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtSmallPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 →
      ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ _ _ v ε hε hv hns
  obtain ⟨e, he⟩ := G.pl.w_split v hv
  have hb := Formalism.IndefR.Fin.below_of_idemAt he
  have hbv : Formalism.IndefR.Fin.belowPl (G.pl.w v) = v := by
    refine HeightOneSpectrum.ext ?_
    have a := congrArg HeightOneSpectrum.asIdeal (G.pl.under_w hv)
    rw [← a]
    rfl
  rw [hbv] at hb
  refine hns.2 ⟨e, he.1, ?_⟩
  rw [hb, Formalism.IndefR.Fin.placeIdem_eq hε]
  rfl

end GlobalTheory.SplitAtSmallPlaces
end

