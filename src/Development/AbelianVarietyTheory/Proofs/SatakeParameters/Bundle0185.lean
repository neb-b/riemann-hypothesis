module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertTypeEigenvaluesIffLabelEigensystemsRows
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AutomorphicArithmetic.OrbitLabellings.LatticePairsOddDegreeIsometric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsEqOfSameEigensystemThetaAdjoint
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartnerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ t, ∃ pl cX c0, RowDict R t pl cX c0 := by
  first | exact @GlobalTheory.RowDictR.rowDict_exists | exact GlobalTheory.RowDictR.rowDict_exists | (intros; apply GlobalTheory.RowDictR.rowDict_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassage
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrPass

theorem sep_extend {α κ K : Type} [Field K] [CharZero K] (S : Finset α) (C : α → Prop) (f : α → κ → K) (k0 : κ) :
    ∃ g : α → κ → K, (∀ a, C a → g a = f a) ∧
      ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (C a ∧ C a') → g a k0 ≠ g a' k0 := by
  classical
  set Ex : Finset K := (S.filter C).image (fun a => f a k0)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hinf : ((Ex : Set K)ᶜ).Infinite := Ex.finite_toSet.infinite_compl
  haveI := hinf.to_subtype
  let e : ℕ ↪ ((Ex : Set K)ᶜ : Set K) := Infinite.natEmbedding _
  set U := S.filter (fun a => ¬ C a)
  let idx : α → ℕ := fun a => if h : a ∈ U then ((U.equivFin ⟨a, h⟩ : Fin U.card) : ℕ) else 0
  refine ⟨fun a => if C a then f a else fun _ => (e (idx a) : K), fun a ha => by simp [ha], ?_⟩
  intro a ha a' ha' hne hC
  have hidx : ∀ b ∈ S, ¬ C b → ∀ b' ∈ S, ¬ C b' → idx b = idx b' → b = b' := by
    intro b hb hCb b' hb' hCb' h
    have hbU : b ∈ U := Finset.mem_filter.2 ⟨hb, hCb⟩
    have hbU' : b' ∈ U := Finset.mem_filter.2 ⟨hb', hCb'⟩
    simp only [idx, dif_pos hbU, dif_pos hbU'] at h
    have := U.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  have hnot : ∀ n, (e n : K) ∉ Ex := fun n => (e n).2
  by_cases h1 : C a
  · have h2 : ¬ C a' := fun h2 => hC ⟨h1, h2⟩
    simp only [if_pos h1, if_neg h2]
    intro h
    have hm : f a k0 ∈ Ex := Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩, rfl⟩
    rw [h] at hm
    exact hnot _ hm
  · by_cases h2 : C a'
    · simp only [if_neg h1, if_pos h2]
      intro h
      have hm : f a' k0 ∈ Ex := Finset.mem_image.2 ⟨a', Finset.mem_filter.2 ⟨ha', h2⟩, rfl⟩
      rw [← h] at hm
      exact hnot _ hm
    · simp only [if_neg h1, if_neg h2]
      intro h
      exact hne (hidx a ha h1 a' ha' h2 (e.injective (Subtype.ext h)))

end GlobalTheory.TrPass

namespace GlobalTheory.TrPass

theorem exists_inert_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJ hAbs hPB hPP
  classical
  have hlab : ∀ (j : Fin D.R.m) P d, IsLab (Yc D 0) P d ↔ IsLab (Wc D j) P d := by
    intro j P d
    rw [_root_.GlobalTheory.LabChar.labels_char, _root_.GlobalTheory.LabChar.labels_char]
    have h1 : (Yc D 0).rank = D.R.r := by
      rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
    have h2 : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
    rw [h1, h2]
  let Wit : ∀ j : Fin D.R.m, A3.fam3.base3.Ix → (Pl D.host.E → List ℤ → ℂ) →
      ((A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) → Prop :=
    fun j p c s => R.Carries p c ∧ ∃ x : (A3.A.fam.L j A3.A.μ0).S.Forms,
      x ∈ BlockGood.goodR (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0
  have key : ∀ j p c s p' c' s', Wit j p c s → Wit j p' c' s' → ∀ Q : A3.okI A3.A.μ0,
      ((∀ y, p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)) ↔ ∀ y, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) := by
    intro j p c s p' c' s' hw hw' Q
    obtain ⟨hc, x, -, hx, hxW, hx0⟩ := hw
    obtain ⟨hc', x', -, hx', hxW', hx0'⟩ := hw'
    rw [_root_.GlobalTheory.InertRowsEig.inert_types_iff_labels hHowe R F hLI hCW hEx hSch hJ hPB hPP p p' c c' hc hc' Q,
      _root_.GlobalTheory.Hk3.lift_inert_iff hHowe R F hLI hCW hEx hSch hJ hAbs j c c' s s' x x' hx hxW hx0 hx' hxW' hx0' Q]
    exact forall_congr' fun d => imp_congr_left (hlab j _ d)
  let Cons : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → Prop := fun j a => ∃ p c s, Wit j p c s ∧ p.1.2 = a
  let f : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL := fun j a k =>
    if h : Cons j a then
      (if hk : k.1 ∈ A3.okI A3.A.μ0 then h.choose_spec.choose_spec.choose (Sum.inr (⟨k.1, hk⟩, k.2)) else 0)
    else 0
  have hf : ∀ j a (h : Cons j a) (Q : A3.okI A3.A.μ0) y,
      f j a (Q.1, y) = h.choose_spec.choose_spec.choose (Sum.inr (Q, y)) := by
    intro j a h Q y
    simp only [f, dif_pos h, dif_pos Q.2]
  have hspec : ∀ j a (h : Cons j a),
      Wit j h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose ∧ h.choose.1.2 = a :=
    fun j a h => h.choose_spec.choose_spec.choose_spec
  let S : Finset (I0 × List ℕ → D.what₂.LL) := ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd
  have hg : ∀ j, ∃ g : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL, (∀ a, Cons j a → g a = f j a) ∧
      ∀ _q : A3.okI A3.A.μ0, ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (Cons j a ∧ Cons j a') →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, g a (k.1.1, k.2) ≠ g a' (k.1.1, k.2) := by
    intro j
    by_cases hne : Nonempty (A3.okI A3.A.μ0)
    · obtain ⟨q⟩ := hne
      obtain ⟨g, hg1, hg2⟩ := sep_extend S (Cons j) (f j) (q.1, ([] : List ℕ))
      exact ⟨g, hg1, fun _ a ha a' ha' hne hC => ⟨(q, []), hg2 a ha a' ha' hne hC⟩⟩
    · exact ⟨f j, fun _ _ => rfl, fun q => (hne ⟨q⟩).elim⟩
  choose g hg1 hg2 using hg
  refine ⟨g, ?_, ?_⟩
  · intro j p c hc s hx k
    have hC : Cons j p.1.2 := ⟨p, c, s, ⟨hc, hx⟩, rfl⟩
    rw [hg1 j _ hC]
    change s (Sum.inr k) = f j p.1.2 (k.1.1, k.2)
    rw [hf j _ hC k.1 k.2]
    obtain ⟨hw, ha⟩ := hspec j _ hC
    exact (((key j _ _ _ p c s hw ⟨hc, hx⟩ k.1).1 (fun y => by rw [ha])) k.2).symm
  · intro j p hp p' hp' hk
    obtain ⟨k0, hk0⟩ := hk
    by_cases hC : Cons j p.2 ∧ Cons j p'.2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hw, ha⟩ := hspec j _ hC.1
      obtain ⟨hw', ha'⟩ := hspec j _ hC.2
      have := (key j _ _ _ _ _ _ hw hw' k0.1).2 (fun y => by
        have h1 := hcon (k0.1, y)
        rw [hg1 j _ hC.1, hg1 j _ hC.2, hf j _ hC.1, hf j _ hC.2] at h1
        exact h1) k0.2
      rw [ha, ha'] at this
      exact hk0 this
    · have hne : p.2 ≠ p'.2 := fun h => hk0 (by rw [h])
      exact hg2 j k0.1 p.2 (Finset.mem_image_of_mem _ hp) p'.2 (Finset.mem_image_of_mem _ hp') hne hC

end GlobalTheory.TrPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.Ggeo

theorem frobeniusConjugation_conditions_adaptedKernelDatum_alt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3 ep be sg
  have main : ∀ u μ (w : D.what₂.places.Pl), LevFree Y u μ w → IsResidueClassZero D (D.what₂.places.resChar w) → ∀ i < D.R.m, ∀ c c',
      ∀ Q : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w] → Prop,
      (HostAt t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) → 5 ≤ D.what₂.places.resChar w →
        ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
          (P : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
          (P' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
          admitted D (D.R.N i) (D.R.N (i + 1)) L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
          ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → Q (stdSer D (t.ent.lam w) (fun _ => 1) P P' G)) →
      Q (t.ent.Th u μ w i c c') := by
    intro u μ w hLF' hC i hi c c' Q hQ
    have hprime : (D.what₂.places.resChar w).Prime := Fact.out
    have h5 : 5 ≤ D.what₂.places.resChar w := (DIV.Inh.orbit_admissible_of_split_bound D h3).2 _ hprime hC
    have hAdPl : Formalism.L2.Ker.AdPl D w := Or.inl hC
    obtain ⟨Pm, hB, -, hConj, hTh⟩ := hAd w hAdPl u μ hLF'
    obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLF' i hi c c'
    have hHA := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) h5 (Or.inl hC)
    have hS : StdBases D (t.ent.lam w) ((t.O u μ).lat i c).1 (Pm i c) :=
      _root_.GlobalTheory.KerStd.stdBases_of_basR D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat i c).2.1 (fun τ => hB i hi.le c τ)
        (fun τ τ' h => hConj i hi.le c τ τ' h)
    have hS' : StdBases D (t.ent.lam w) ((t.O u μ).lat (i + 1) c').1 (Pm (i + 1) c') :=
      _root_.GlobalTheory.KerStd.stdBases_of_basR D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat (i + 1) c').2.1 (fun τ => hB (i + 1) hi c' τ)
        (fun τ τ' h => hConj (i + 1) hi c' τ τ' h)
    have key := hQ hHA h5 _ _ _ _ hAdm hS hS' _ hComb
    rw [hTh i hi c c', _root_.GlobalTheory.atLin_adCoef_eq_stdSer]
    exact key
  refine ⟨fun u μ w hLF hC hP0 i hi _ c c' => ?_, fun u μ w hLF hC i hi _ c c' => ?_⟩
  · exact main u μ w hLF hC i hi c c' (OrbitPlaces.ThetaExpansionRealPlaces D (D.what₂.places.resChar w)) fun hHA h5 =>
      _root_.GlobalTheory.KerStd.thetaExpansionRealPlaces_stdSer_of_adm D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC hP0 _ _
  · have hodd : Odd (nP D (D.what₂.places.resChar w)) := by
      have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun h => by
        have h1 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := hC.1
        have h2 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
        rw [h1] at h2; cases h2
      unfold nP
      rw [if_neg hs]
      exact hC.2.1
    exact main u μ w hLF hC.1 i hi c c' (OrbitPlaces.EvenConditionsAllReal D (D.what₂.places.resChar w)) fun hHA h5 =>
      UpperTheory.lattice_pairs_odd_degree_isometric D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC.1 hodd _ _

end GlobalTheory.Ggeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharacters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem forall_val_of_heq_hom {E : Type} [Field E] {a b b' : ℕ} (hb : b = b') (P : ℂ → Prop)
    {f : HomE E a b → ℂ} {g : HomE E a b' → ℂ} (h : HEq f g) (hg : ∀ x, P (g x)) : ∀ x, P (f x) := by
  subst hb
  rw [eq_of_heq h]
  exact hg

theorem kernel_datum_of_hecke_character_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ
  obtain ⟨hFG, hsd⟩ := _root_.GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t
  refine ⟨hFG, fun u μ i hi c c' hpin => ⟨hsd u μ i c, hsd u μ (i + 1) c', ?_⟩⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, row, -, hyb, hE, hC1, -, hC2, -, hp⟩ := t.rd_chain u μ
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · intro x
    rw [hE i hlt c c' x]
    exact GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) i hlt _ _ _ _ x
  · subst heq
    intro x
    rw [hC1 c c' x]
    exact GlobalTheory.T.precedingStepDatum_integral_away_from_levels D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) _ _ _ _ x
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    obtain ⟨d, hd⟩ := (hp c').1 hpin
    refine forall_val_of_heq_hom (congrArg D.R.N (by omega : t.m2 + 1 + 1 = D.R.m))
      (IntOff (t.O u μ).S) (hC2 c c' d hd) fun x => ?_
    exact GlobalTheory.T.lastStep_data_integralAwayFrom_levels D L hT Gi Gl K Y cX ex t u μ _ _ d x (hyb c)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplitStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTheta_relation_of_indicator_relation_split : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  first | exact @GlobalTheory.KerRel.kerTh_relation_of_indicator | exact GlobalTheory.KerRel.kerTh_relation_of_indicator | (intros; apply GlobalTheory.KerRel.kerTh_relation_of_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftSplitHeckePolysEqTransferResidualPolysStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i c (p : Pl0 → D.what₂.LL[X]) (sX : A.ok A.μ0 × ℕ → D.what₂.LL) (sV : A.ok A.μ0 × ℕ → D.what₂.LL), (A.fam.R A.μ0).HasRes p sX → ∀ hX hV, IsOpsX R A.μ0 hX → IsOpsV R i A.μ0 hV → ∀ w ∈ EEc R SF c, LinearMap.adjoint (R.Th A.μ0) w ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ D.sp.X'.rank → hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A.μ0) w) = D.what₂.embLL (sX (P, k)) • LinearMap.adjoint (R.Th A.μ0) w) → ∀ y, R.thG i A.μ0 y ∈ Wcc R SF i c → R.thG i A.μ0 y ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ (Vc D i).rank → hV (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) y = D.what₂.embLL (sV (P, k)) • y) → (A.fam.L i A.μ0).HasRes (A.fam.tr i p) sV := by
  first | exact @GlobalTheory.Hk3.Link.hasRes_lift | exact GlobalTheory.Hk3.Link.hasRes_lift | (intros; apply GlobalTheory.Hk3.Link.hasRes_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSystemsLowerBoundsSecondRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.SiteSys

variable {D : D7}

theorem orbMap_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) (s : ZMod (nP D p)) :
    OrbitPlaces.orbMap D p (posPl D p r e) s = OrbitPlaces.orbMap D p r (s + (e : ZMod (nP D p))) := by
  unfold OrbitPlaces.orbMap
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p r s.val, posPl_mod, posPl_add, add_comm]

theorem topsOrb_posPl (p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.topsOrb D p (posPl D p r e) = OrbitPlaces.topsOrb D p r := by
  unfold OrbitPlaces.topsOrb
  refine Finset.card_equiv (Equiv.addRight (e : ZMod (nP D p))) fun s => ?_
  simp [orbMap_posPl]

theorem errF_posPl {L : SizeData₂ D} (K : Consts) (ce : ErrC) (j p : ℕ) (r : OrbitPlaces.Pl D) (e : ℕ) :
    OrbitPlaces.errF L K ce j p (posPl D p r e) = OrbitPlaces.errF L K ce j p r := by
  have h : ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p (posPl D p r e) s) =
      ∑ s : ZMod (nP D p), wPl D j (OrbitPlaces.orbMap D p r s) := by
    simp only [orbMap_posPl]
    exact Equiv.sum_comp (Equiv.addRight (e : ZMod (nP D p))) (fun s => wPl D j (OrbitPlaces.orbMap D p r s))
  unfold OrbitPlaces.errF
  rw [h, topsOrb_posPl]

theorem posPl_true_one {p : ℕ} (hs : ¬ IsSg D p) (t : HH D) : posPl D p (true, t) 1 = (true, t + hP D p) := by
  simp [posPl, partner, hs]

theorem notSg {T p : ℕ} (hg : GIdx D.host T p) : ¬ IsSg D p := by
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  unfold IsSg at h
  rw [h1] at h
  exact absurd h (by decide)

theorem sysTw_sites : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (Dx : DivX D) (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (E : OrbitPlaces.Ent D) (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Y.Fl u w hg), Chain Lv), LatTied hT X Y → FillsAll hT Y → L.FDef → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → (∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ → SiteAdm D u w hg (Y.Fl u w hg) (LC μ u w hg).1 (LC μ u w hg).2) → SysTw D L X K Dx (reW Y LC) lev Xe ce 1 := by
  intro D L hT X Y K Dx lev Xe ce E LC hty hfa hF hadm hSh hCL hS hE μ hμ hT' hty' u w hg hQ
  obtain ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, h0, hj⟩ := hS μ hμ u w hg hQ
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.SecondOrbits.places_off_first_orbits D u w hg L hT X Y hty
  refine ⟨i, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA,
    fun v j => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, r v) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, r v) else 0,
    ?_, ?_⟩
  · intro v hv j hjm
    obtain ⟨-, -, -, a2c, -, -, -, -, -, -, -, -, a11⟩ := hA
    by_cases hp : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hp]
      exact _root_.GlobalTheory.TwU.LowF.lowAt_F D u w hg L hT X Y K ce E hty hfa hadm hSh hCL hp _ _ std vp unif eO eO_spec dG dG_spec om Y5 a2c v (r v)
        (hr1 v hv).1 (hr1 v hv).2.2 j hjm
    · simp only [if_neg hp]
      exact a11 v j (lt_of_lt_of_eq hjm (hty u w hg).1.symm)
  · refine (_root_.GlobalTheory.TwU.LowTerm.lowS_le D u w hg L X K ce Xe dG hF h0 hj).trans (sub_le_sub_right (le_of_eq ?_) _)
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (hr2 (fun t => if ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n then
      FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) ?_).symm
    intro t
    have h1 := posPl_true_one (notSg hg) t
    have h2 := FOrb_step D j (D.what₂.places.resChar w) (true, t) 1
    have h3 := errF_posPl (L := L) K ce j (D.what₂.places.resChar w) (true, t) 1
    rw [h1] at h2 h3
    simp only [h2, h3]

end GlobalTheory.TwU.SiteSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := _root_.GlobalTheory.KerStd.BeData.exists_of_curveData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := _root_.GlobalTheory.KerStd.hyp_of_stdBases D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact _root_.GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsEqOfSameEigensystemThetaAdjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parts_eq_of_same_eigensystem_thetaAdjoint : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ c c', ∀ w ∈ R.Wc' j c, ∀ w' ∈ R.Wc' j c', LinearMap.adjoint (R.thG j A3.A.μ0) w ≠ 0 → LinearMap.adjoint (R.thG j A3.A.μ0) w' ≠ 0 → labW j pl cW c = labW j pl cW c' → R.Wc' j c = R.Wc' j c' := by
  first | exact @GlobalTheory.Hk3.SepLift.parts_eq_of_labW | exact GlobalTheory.Hk3.SepLift.parts_eq_of_labW | (intros; apply GlobalTheory.Hk3.SepLift.parts_eq_of_labW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiEntryStab
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
open Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.MatLaw

noncomputable section

namespace GlobalTheory.FiLaw

theorem xiEntry_stab : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → Ch.Ok → cst.sharp = true → R.m ≤ cst.A → (∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) → ∀ (u : Pr.Word) (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (a : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)), a • p' = p' → ∀ x, XiEntry Ch sel mu cst L i al be p p' (a.1.1.toLinearMap ∘ₗ x) * ∏ P : rowSG Pr sel mu, muAt Ch sel mu cst i P ((LinearEquiv.det a.1.1 : X.Eˣ) : X.E) = (((L.levG (i + 1) be).chr a.2.1 * (L.levQ (i + 1) be).chr a.2.2 : X.Kˣ) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hg hT hL _ _ _ _ u i hi al be p p' a ha x
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u ⟨hT u, hg⟩).2.2
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd (1 : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd a p'
  have key := xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  have e1 : x ∘ₗ ((1 : FrmG (L.levG i al) (L.levQ i al)).1.1.symm.toLinearMap) = x := LinearMap.ext fun v => rfl
  rw [one_smul, ha, e1, ec, ec'] at key
  simp only [Prod.snd_one, Prod.fst_one, map_one, mul_one, inv_one] at key
  rw [← key]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have h1 : ((κ P)⁻¹).1 = 1 := by
    have h := hκ P
    rw [one_smul] at h
    simpa using h
  have h2 : LinearEquiv.det (κ' P).1 = LinearEquiv.det a.1.1 := by
    have h := congrArg LinearEquiv.det (hκ' P)
    rw [ha, map_mul, map_mul, Subgroup.coe_inv, map_inv] at h
    rw [mul_left_comm] at h
    have h' := mul_left_cancel (h.symm.trans (mul_one _).symm)
    exact (mul_inv_eq_one.1 h').symm
  rw [Pi.inv_apply, Pi.inv_apply, h1, map_one, Units.val_one, rhoT_inv, ← muAt_det, h2]
  unfold rhoS
  rw [GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one, one_mul]

end GlobalTheory.FiLaw
end
end

