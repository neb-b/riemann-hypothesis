module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestWitness

theorem exists_rest : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  intro F _ _ κ _ v
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  refine ⟨r, ?_, fun φ hφ => ⟨hr, ?_⟩⟩
  · have e := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
      exact map_zero _
    have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [φs, Pi.zero_apply, map_zero]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
    exact hf
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w

end GlobalTheory.RestWitness
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

theorem nsmul_mem_of_mem_halfCoset {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {r x : Mx D m n}
    (hr : K • r ∈ Λ) (h : x ∈ halfCoset e Λ K r) : K • x ∈ Λ := by
  obtain ⟨u, hu, -, rfl⟩ := h
  rw [nsmul_add]
  exact add_mem hr (nsmul_mem (nsmul_mem hu K) K)

theorem eq_of_mem_halfCoset_reps {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {R : Finset (Mx D m n)}
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') {r r₀ x : Mx D m n} (hr : r ∈ R) (hr₀ : r₀ ∈ R)
    (hm : x ∈ halfCoset e Λ K r) (hm₀ : x ∈ halfCoset e Λ K r₀) : r = r₀ := by
  refine hR3 r hr r₀ hr₀ ?_
  rw [← halfCoset_eq hm, halfCoset_eq hm₀]
  exact mem_halfCoset_self _ _ _ _

theorem exists_cosetExpansion_of_depthOK : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  classical
  intro D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep
  by_cases hτ : τ = 0
  · subst hτ
    exact ⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩
  obtain ⟨d₀, hd₀⟩ := Finsupp.support_nonempty_iff.2 hτ
  have hP0 := hexp.1 d₀ hd₀
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  let dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) →
      (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t :=
    fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))
  set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'
  have hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ' := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := hP0.1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := hP0.2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    change Finsupp.sum τ' g = _
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) =
        (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) := fun ρ hρ j =>
      congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1
        ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)
    have hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ' hρ' i =>
      congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1
        ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)
    simp only [g, dat]
    have hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2,
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)) *
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ hρ ρ' hρ' => by
      rw [Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]
    rw [Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']
    show _ = flatProd S t Φ β x y
    by_cases hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)
    · have h1 := fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)
      have h2 := fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)
      choose ρ0 hρ0 hxρ0 using h1
      choose ρ0' hρ0' hyρ0' using h2
      have hmem : ρ0 ∈ Fintype.piFinset R1 := Fintype.mem_piFinset.2 hρ0
      have hmem' : ρ0' ∈ Fintype.piFinset R2 := Fintype.mem_piFinset.2 hρ0'
      have hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 →
          ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ) := by
        intro ρ hρ hne
        obtain ⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)
        exact eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)
      have hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' →
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ) := by
        intro ρ' hρ' hne
        obtain ⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)
        exact eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)
      rw [Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]
      case s1 =>
        intro ρ hρ hne
        exact Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _
      case s2 =>
        intro ρ' hρ' hne
        exact mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)
      refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_))
        (Finset.prod_eq_one fun i _ => ?_)).trans ?_
      · exact Set.indicator_of_mem (hxρ0 j) _
      · exact Set.indicator_of_mem (hyρ0' i) _
      rw [mul_one, mul_one]
      choose u hu hu' hxu using hxρ0
      choose v hv hv' hyv using hyρ0'
      have hx' : x = ρ0 + K • u := funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j
      have hy' : y = ρ0' + K • v := funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i
      rw [hx', hy']
      exact (hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1)
        (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm
    · have hzero : flatProd S t Φ β x y = 0 := by
        by_contra h
        exact hin (hdep.1 x y hx hy h)
      rw [hzero]
      refine Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_
      rw [Fintype.mem_piFinset] at hρ hρ'
      rcases not_and_or.1 hin with h | h
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem
          (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem
          (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))
  · obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2

end GlobalTheory.DepthUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  intro E _ _ _ m S b 𝒲 hb ⟨C, hC, hbC⟩ ⟨Ub, hUbo, hUb⟩ hWe hWt hWU H
  classical
  have hsel : ∀ q : GA E (m + 1), ∃ W ∈ 𝒲, (q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1 →
      ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) →
        W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) := by
    intro q
    by_cases hq : q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1
    · obtain ⟨W, hW, h⟩ := H q hq.1 hq.2
      exact ⟨W, hW, fun _ => h⟩
    · exact ⟨0, 𝒲.zero_mem, fun h => absurd h hq⟩
  choose Wq hWq hWqb using hsel
  choose Uq hUqo hUq using fun q => hWU _ (hWq q)
  obtain ⟨K, R, j, hKo, hKc, hR, hcov, huniq⟩ :=
    GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic E m S C hC (fun q => Ub ⊓ Uq q) (fun q => hUbo.inter (hUqo q))
  choose n hh c hhS hcutEq using GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces E m S K hKo hKc
  refine ⟨∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i)), ?_, ?_⟩
  · exact 𝒲.sum_mem fun x _ => 𝒲.sum_mem fun i _ => 𝒲.smul_mem _ (hWt _ (hWq _) _ (hhS x i))
  · intro p hp
    have e1 : (∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i))) p =
        ∑ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      refine hcutEq x (Wq (j x)) (hWe _ (hWq _)) (fun u hu g => hUq _ u ((hR x hx).2.2.1 hu).2 g) p hp
    have e2 : ∀ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p =
        (GlobalTheory.JSW.MirPatch.cell K x).indicator (fun _ => b p) p := by
      intro x hx
      by_cases hpx : p ∈ GlobalTheory.JSW.MirPatch.cell K x
      · rw [Set.indicator_of_mem hpx, Set.indicator_of_mem hpx]
        obtain ⟨hj1, hj2, -, hj4⟩ := hR x hx
        exact GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice E m S b (Wq (j x)) (Ub ⊓ Uq (j x)) (j x) hj1 hj2 hb (hWe _ (hWq _))
          (fun u hu g => hUb u hu.1 g) (fun u hu g => hUq _ u hu.2 g) (hWqb _ ⟨hj1, hj2⟩) p hp (hj4 hpx)
      · rw [Set.indicator_of_notMem hpx, Set.indicator_of_notMem hpx]
    rw [e1, Finset.sum_congr rfl e2]
    by_cases hbp : b p = 0
    · rw [hbp]; simp
    · obtain ⟨x0, hx0, hpx0⟩ := hcov p hp (hbC p hp hbp)
      rw [Finset.sum_eq_single x0 (fun x hx hne => Set.indicator_of_notMem
        (fun hpx => hne (huniq x hx x0 hx0 p hp hpx hpx0)) _) (fun h => absurd hx0 h),
        Set.indicator_of_mem hpx0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvZeroInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finPart (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem pure_eq_tens (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = tens (evI F) (⇑f) (finPart φ) := rfl

theorem snd_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h := congrArg Prod.snd (congrFun (hz _ h0) i)
  change (1 : Af F) * (z i).2 = 0 at h
  rwa [one_mul] at h

theorem finPart_add (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  unfold finPart
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  have h : evFin F v (z i) = 0 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
    rw [snd_eq_zero_of_at z hz i, map_zero]
  rw [Pi.add_apply, map_add (f := _), h, add_zero]

theorem exists_finPart_ne_zero (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ x₀ : κ → Af F, ∀ x : κ → AF F, (∀ i, (x i).2 = x₀ i) → finPart φ x ≠ 0 := by
  classical
  have hfin := Filter.eventually_cofinite.1 hstd
  set S := hfin.toFinset with hS
  have hy : ∀ v, ∃ y, φ v y ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact h0 v (funext h)
  choose y hy using hy
  refine ⟨fun i => ∑ v ∈ S, singleFin v (y v i), fun x hx => ?_⟩
  have hev : ∀ w, (fun i => evFin F w (x i)) = if w ∈ S then y w else 0 := by
    intro w
    funext i
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (x i).2 = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx i, map_sum]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hw h),
        evalV_singleFin_self, if_pos hw]
    · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (fun h => hw (by rw [h]; exact hv)) _), if_neg hw]
      rfl
  have hne : ∀ w, φ w (fun i => evFin F w (x i)) ≠ 0 := by
    intro w
    by_cases hw : w ∈ S
    · rw [hev w, if_pos hw]; exact hy w
    · rw [hev w, if_neg hw]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (by rw [hS, Set.Finite.mem_toFinset]; exact h)
      rw [hw', Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from
        fun i => zero_mem _)]
      exact one_ne_zero
  unfold finPart
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun w _ => hne w
  · exact one_ne_zero

theorem eq_of_pure_eq (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (g g' : SInf F κ) (h : pure g φ = pure g' φ) : g = g' := by
  obtain ⟨x₀, hx₀⟩ := exists_finPart_ne_zero φ h0 hstd
  refine DFunLike.ext g g' fun y => ?_
  let x : κ → AF F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)
  have hI : (fun i => evI F (x i)) = y :=
    funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
  have e := congrFun h x
  change g (fun i => evI F (x i)) * finPart φ x = g' (fun i => evI F (x i)) * finPart φ x at e
  rw [hI] at e
  exact mul_right_cancel₀ (hx₀ x fun i => rfl) e

end GlobalTheory.EvZeroInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumOfHeisenbergLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlaceVacuum_of_heisenbergLattice : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Continuous ψ → GlobalTheory.LatVac.psiAt ψ v ≠ 1 →
    ∀ Γ : AddSubgroup W, (∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ Γ, GlobalTheory.LatVac.liftV v a • γ ∈ Γ) →
    IsOpen ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    IsCompact ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ c : W → ℂ, c 0 = 1 → (∀ γ ∈ Γ, ∀ γ' ∈ Γ, c (γ + γ') = c γ * c γ' * ψ (⅟(2 : AF F) * B γ γ')) →
    (∀ γ ∈ Γ, c (GlobalTheory.LatVac.liftV v 2 • γ) = 1) →
    ∃ φ : (κ → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧
      ∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ (c γ • φ) := by
  first | exact @GlobalTheory.HeisLatVac.exists_vac_of_lattice | exact GlobalTheory.HeisLatVac.exists_vac_of_lattice | (intros; apply GlobalTheory.HeisLatVac.exists_vac_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphism
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertRho

theorem exists_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∃ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, -⟩ := hC
  have hstd := hTr.base.std
  let ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)) := fun x =>
    { toFun := fun m => ⟨schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) m,
        GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v _ _ m.2⟩
      map_add' := fun m m' => by
        ext y
        simp only [schr, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c m => by
        ext y
        simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  exact ⟨ρ, fun x m => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v (κ x) (hAt x) m⟩

end GlobalTheory.InertRho

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShiftsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J),
    ∃ k : UA σ J, At (evFin F v) (mat k - 1) ∧ ∃ a b : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) a ∧ At (evFin F v) b ∧
      a * (1 - mat k) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      (1 - mat k) * a = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      b * (1 - mat (g⁻¹ * k)) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      (1 - mat (g⁻¹ * k)) * b = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  first | exact @GlobalTheory.InertScalarUnit.exists_scalar_inv_at | exact GlobalTheory.InertScalarUnit.exists_scalar_inv_at | (intros; apply GlobalTheory.InertScalarUnit.exists_scalar_inv_at <;> assumption)
end

