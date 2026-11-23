module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0240
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo

theorem sum_incA_inv_mul {D : D7} (W : HSp D) (p i : Fin W.rank) :
    ∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i) = if p = i then 1 else 0 := by
  have h1 : (∑ k, incA D (W.gram⁻¹ p k) * incA D (W.gram k i)) = incA D ((W.gram⁻¹ * W.gram) p i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum (incA D)]
    exact Finset.sum_congr rfl fun k _ => ((incA D).map_mul _ _).symm
  rw [h1, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _


set_option maxHeartbeats 1000000 in
theorem exists_pair_entry {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)}
    {e : AE D} (he : SplitAt D v e) (W : HSp D) {r : ℕ} (p : Fin W.rank) (q : Fin r) (c : Fv D.host.F v) :
    ∃ a : Mx D W.rank r, IsHalf e a ∧ ∀ t : Mx D W.rank r,
      halfPair W a t = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
  let a : Mx D W.rank r := Matrix.of fun k j => if j = q then
    incA D (star (W.gram⁻¹ p k)) * incA D (star D.host.xi0⁻¹) * fj D (singleV D.host.F v c) * e else 0
  have hca : ∀ k, cA D (a k q) = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * incA D (W.gram⁻¹ p k) := by
    intro k
    show cA D (if q = q then _ else 0) = _
    rw [if_pos rfl, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.cA_incA, star_star, star_star,
      cA_fj]
    ring
  refine ⟨a, fun k j => ?_, fun t => ?_⟩
  · show e * a k j = a k j
    simp only [a, Matrix.of_apply]
    split_ifs
    · rw [mul_left_comm, he.1]
    · rw [mul_zero]
  have hG := sum_incA_inv_mul W p
  unfold halfPair
  calc ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j
      = ∑ i, incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * (if p = i then 1 else 0) * t i q :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_eq_single q (fun j _ hj => Finset.sum_eq_zero fun k _ => by
            rw [show a k j = 0 from if_neg hj, map_zero, zero_mul, zero_mul]) (fun h => absurd (Finset.mem_univ q) h)]
          rw [← hG i, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [hca]; ring
    _ = incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e * t p q := by
      rw [Finset.sum_eq_single p (fun i _ hi => by rw [if_neg (Ne.symm hi), mul_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ p) h), if_pos rfl, mul_one]

end GlobalTheory.HalfSeparate

namespace GlobalTheory.HalfSeparate

open GlobalTheory.IdemModTwo


set_option maxHeartbeats 1000000 in
theorem exists_open_separated : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  intro D ψ hψ W r e hε U hU
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  have he' := he.conj
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let sg : Fv D.host.F v →+ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := AddMonoidHom.ofMapSub (singleV D.host.F v) (singleV_sub D v)
  let ι : Fv D.host.F v →+ AF D.host.F := AddMonoidHom.mk' (fun y => pairA D.host.F 0 (sg y)) fun a b => by
    rw [map_add (f := _)]; exact Prod.ext (add_zero _).symm rfl
  have hι : Continuous ι := Continuous.prodMk continuous_const (GlobalTheory.SplitAnnihilator.continuous_singleV D.host.F v)
  have hψc : Continuous fun x => ψ (ι x) := hψ.1.1.comp hι

  obtain ⟨ε0, hε0, hψε⟩ : ∃ ε > 0, ∀ x : Fv D.host.F v, ‖x‖ < ε → ψ (ι x) = 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hψc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun x hx => GlobalTheory.ThetaStalk.eq_one_of_pow_near fun n => ?_⟩
    have := h (x := n • x) (by
      rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
    rwa [map_zero, AddChar.map_zero_eq_one, dist_eq_norm, map_nsmul, AddChar.map_nsmul_eq_pow] at this
  obtain ⟨y1, hy1⟩ : ∃ y, ψ (ι y) ≠ 1 := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v

  let G := Fin W.rank × Fin r → Fv D.host.F v
  let J : G →+ Mx D W.rank r := AddMonoidHom.mk' (fun y => Matrix.of fun i k => fj D (sg (y (i, k))) * cA D e)
    fun a b => by
      ext i k
      simp only [G, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add (f := _), add_mul]
  have hJ : Continuous J := continuous_matrix fun i k =>
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))).comp
      (hι.comp (continuous_apply (i, k)))).mul continuous_const
  have hJh : ∀ y, J y ∈ halfMx (cA D e) W.rank r := fun y i k => by
    show cA D e * (_ * cA D e) = _ * cA D e
    rw [mul_left_comm, he'.1]
  let J' : G →+ halfMx (cA D e) W.rank r := J.codRestrict (halfMx (cA D e) W.rank r) hJh
  have hJ' : Continuous J' := hJ.subtype_mk _
  have hJs : Function.Surjective J' := fun u => by
    choose y hy using fun p : Fin W.rank × Fin r => he'.exists_scalar ((u : Mx D W.rank r) p.1 p.2)
    exact ⟨y, Subtype.ext (Matrix.ext fun i k => (hy (i, k)).symm.trans (u.2 i k))⟩
  have : T2Space (halfMx (cA D e) W.rank r) := t2Space_halfAdelicMatrixAddSubgroup (cA D e) W.rank r
  have : LocallyCompactSpace (halfMx (cA D e) W.rank r) := lcHalf (cA D e) W.rank r
  have : R1Space (halfMx (cA D e) W.rank r) := T2Space.r1Space
  have : BaireSpace (halfMx (cA D e) W.rank r) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J' := AddMonoidHom.isOpenMap_of_sigmaCompact J' hJs hJ'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hJ') 0 (by
    show J' 0 ∈ U
    rw [map_zero]; exact U.zero_mem)

  have hR : 0 ≤ ‖y1‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  let LG : AddSubgroup G :=
    { carrier := {y | ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1}
      add_mem' := fun {a b} ha hb p c hc => by
        rw [Pi.add_apply, mul_add, map_add (f := _), AddChar.map_add_eq_mul, ha p c hc, hb p c hc, one_mul]
      zero_mem' := fun p c _ => by rw [Pi.zero_apply, mul_zero, map_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {a} ha p c hc => by
        have h := ψ.map_add_eq_mul (ι (c * (-a) p)) (ι (c * a p))
        rw [← map_add (f := _), Pi.neg_apply, mul_neg, neg_add_cancel, map_zero, AddChar.map_zero_eq_one, ha p c hc,
          mul_one] at h
        rw [Pi.neg_apply, mul_neg]
        exact h.symm }
  have hLGopen : IsOpen (LG : Set G) := by
    refine AddSubgroup.isOpen_of_mem_nhds LG (g := 0) (Metric.mem_nhds_iff.2 ⟨ε0 / (‖y1‖ / ρ + 1), by positivity,
      fun y hy p c hc => hψε _ ?_⟩)
    have hy' : ‖y‖ < ε0 / (‖y1‖ / ρ + 1) := mem_ball_zero_iff.1 hy
    rw [lt_div_iff₀ (by positivity)] at hy'
    calc ‖c * y p‖ = ‖c‖ * ‖y p‖ := norm_mul _ _
      _ ≤ ‖y1‖ / ρ * ‖y‖ := mul_le_mul hc (norm_le_pi_norm y p) (norm_nonneg _) hR
      _ ≤ ‖y‖ * (‖y1‖ / ρ + 1) := by nlinarith [norm_nonneg y]
      _ < ε0 := hy'
  have hLGsmall : ∀ y ∈ LG, ‖y‖ < ρ := fun y hy => (pi_norm_lt_iff hρ).2 fun p => by
    by_contra hn
    push_neg at hn
    have hp : 0 < ‖y p‖ := hρ.trans_le hn
    have h := hy p (y1 / y p) (by rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hρ hn)
    rw [div_mul_cancel₀ _ (norm_pos_iff.1 hp)] at h
    exact hy1 h
  refine ⟨LG.map J', by rw [AddSubgroup.coe_map]; exact hopen _ hLGopen, ?_, fun x hx => ?_⟩
  · rw [AddSubgroup.map_le_iff_le_comap]
    intro y hy
    exact hball (mem_ball_zero_iff.2 (hLGsmall y hy))
  obtain ⟨y, rfl⟩ := hJs x
  have hy : ¬ ∀ p, ∀ c : Fv D.host.F v, ‖c‖ ≤ ‖y1‖ / ρ → ψ (ι (c * y p)) = 1 :=
    fun h => hx (AddSubgroup.mem_map_of_mem _ h)
  push_neg at hy
  obtain ⟨p, c, hc, hne⟩ := hy
  obtain ⟨a, ha, hpair⟩ := exists_pair_entry he W p.1 p.2 c
  have key : ∀ y', ψ (halfSympl W a (J y')) = ψ (ι (c * y' p)) := fun y' => by
    congr 1
    have h1 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have h2 : incA D D.host.xi0 * halfPair W a (J y') =
        fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e) := by
      rw [hpair]
      show incA D D.host.xi0 * (incA D D.host.xi0⁻¹ * fj D (singleV D.host.F v c) * cA D e *
        (fj D (singleV D.host.F v (y' p)) * cA D e)) = _
      linear_combination (fj D (singleV D.host.F v c) * cA D e * (fj D (singleV D.host.F v (y' p)) * cA D e)) * h1
    rw [halfSympl, h2]
    exact GlobalTheory.SplitAnnihilator.trace_split he' c (y' p)
  refine ⟨⟨a, ha⟩, fun l hl => ?_, (key y).trans_ne hne⟩
  obtain ⟨y', hy', rfl⟩ := AddSubgroup.mem_map.1 hl
  exact (key y').trans (hy' p c hc)

end GlobalTheory.HalfSeparate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWRepOfNegSp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRowArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JoinArrows

theorem weil_arrow_transport {D : D7} {ψ : AddChar (AF ↥D.host.F) ℂ} {S T S' T' : HSp D}
    (hS : S = S') (hT : T = T') {χS χT χS' χT' : (AE D)ˣ →* Circle} (h1 : χS = χS') (h2 : χT = χT')
    (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS' χT' ω') :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ false S T χS χT ω ∧ HEq ω ω' := by
  cases hS
  cases hT
  cases h1
  cases h2
  refine ⟨ω', ?_, HEq.rfl⟩
  rw [GlobalTheory.Grid.isWeil_false]
  exact h

theorem exists_weil_rowArrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ω ∧ HEq ω (W.om (.mu t (i + 1) j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hSp _ hAg _ t i j hi hj

  have hw := W.om_is (.mu t (i + 1) j) ⟨hi, hj⟩
  rw [hW.ψ] at hw

  have e1 : (G.nV i j).V = G'.V (.grid (i + 1) j) := (hAg.vert (i + 1) j hi (by omega)).sp
  have e2 : (G.nV i (j + 1)).V = G'.V (.grid (i + 1) (j + 1)) := (hAg.vert (i + 1) (j + 1) hi hj).sp

  have r1 : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← e1]; exact (hSp.vert i j hi (by omega)).rank
  have r2 : (G'.V (.grid (i + 1) (j + 1))).rank = rkV D (i + 1) (j + 1) := by
    rw [← e2]; exact (hSp.vert i (j + 1) hi hj).rank

  have c1 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j) = G'.chrS (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) j)).rank
    rw [r1]
    rfl
  have c2 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1)) = G'.chrT (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) (j + 1))).rank
    rw [r2]
    rfl
  exact weil_arrow_transport e1 e2 c1 c2 (W.om (.mu t (i + 1) j)) hw

end GlobalTheory.JoinArrows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWrepOfEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin


open GlobalTheory.Grid GlobalTheory.ChiGrid in
theorem exists_wrep_of_eq {D : D7} {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χ χ' : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χ χ' om) :
    ∃ ω : WRep S T, IsWeil ψ true S T χ χ' ω ∧ HEq (ω.toSgn true) om := by
  subst hS hT
  let ω : WRep S T := om.comp ((ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _))
  have e : ω.toSgn true = om := MonoidHom.ext fun x => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  unfold IsWeil
  rw [e]
  exact h

theorem core_arrows_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V, GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω ∧ HEq (ω.toSgn true) (W.om (.core i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ i hi
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := Nat.sub_le _ _
  have hom := W.om_is (.core i) (show (i + 1) ≤ D.R.m by omega)
  rw [(G'.chr_core (by omega : i + 1 ≤ D.R.m)).1, (G'.chr_core (by omega : i + 1 ≤ D.R.m)).2, hW.ψ,
    ← hSp.chi _ h1 h2] at hom
  exact exists_wrep_of_eq (hSp.core (i + 1) (by omega)).sp (hSp.core i (by omega)).sp _ _ _ _ hom

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanAnnih

theorem finPart_mem_compact : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  intro D V W a b P Q hP hQ ψ hψ U hU
  obtain ⟨d, c, e, hce⟩ := _root_.GlobalTheory.TwistCoords.finPart_eq_sum_trace D
  have hm : ∀ p : Fin a × Fin b × Fin d, ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) =
        r * Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
    fun p => _root_.GlobalTheory.EntryTest.entry D V W a b P Q hP hQ p.1 p.2.1 (c p.2.2)
  choose m hm using hm
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  let φ : (Fin a × Fin b × Fin d) → Af D.host.F → WO V W :=
    fun p t => (pairA D.host.F 0 t) • (m p).map (incA D)
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => (m p).map (incA D)) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hφ0]; exact U.zero_mem))
  obtain ⟨K₀, hK₀, hmem⟩ := _root_.GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ _ hO
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : ContinuousSMul (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  let g : (Fin a × Fin b × Fin d → Af D.host.F) → Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun z => Matrix.of fun i j => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin a × Fin b × Fin d → Af D.host.F => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
    refine continuous_finsetSum _ fun l _ => ?_
    have : (fun z : Fin a × Fin b × Fin d → Af D.host.F => z (i, j, l) ⊗ₜ[D.host.F] e l) =
        fun z => z (i, j, l) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin a × Fin b × Fin d => Af D.host.F) (i, j, l))
      (continuous_const (y := ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy =>
    ⟨fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1)),
      fun p _ => hmem _ fun t ht => ?_, ?_⟩⟩
  · have hu : φ p t ∈ U := Set.mem_iInter.1 ht p
    have hinf : (φ p t).map (infPart D) = 0 := by
      ext k l
      simp only [φ, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
      change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] m p k l)) = 0
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (m p k l) = 0
      exact TensorProduct.zero_tmul _ _
    have h1 := hy _ hu hinf
    simp only [φ] at h1
    rw [hm] at h1
    convert h1 using 2
    exact Prod.ext (zero_mul _).symm rfl
  · ext i j
    simp only [g, Matrix.of_apply, Matrix.map_apply]
    rw [hce]

end GlobalTheory.IsoMeanAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem sqrt_intCast_eq_sqrt_toNat (x : ℤ) : Real.sqrt (x : ℝ) = Real.sqrt ((x.toNat : ℕ) : ℝ) := by
  rcases le_or_gt 0 x with h | h
  · rw [show ((x.toNat : ℕ) : ℝ) = (x : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
  · rw [Real.sqrt_eq_zero'.2 (by exact_mod_cast h.le), Int.toNat_eq_zero.2 h.le]; simp

theorem gap_eq_chiGap : ∀ D : D7, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 := by
  intro D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hv : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v = (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v := fun _ => rfl
  have hk : ∀ τ : D.what₂.Tau, (GlobalTheory.Grid.gridOf D 0 0 τ).v 2 - (GlobalTheory.Grid.gridOf D 0 0 τ).v D.R.k =
      (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k := fun τ => by rw [hv]
  have hN : (GlobalTheory.Grid.bigN D : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := rfl
  have hN' : GlobalTheory.Grid.bigN D = GlobalTheory.ChiGrid.bigN D := rfl
  have hs : GlobalTheory.Grid.sLen D = GlobalTheory.ChiGrid.sLen D := rfl
  have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = (D.R.r : ℝ) + 1 := by simp [GlobalTheory.ChiGrid.nRk]
  set f : D.what₂.Tau → ℤ := fun τ => (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k with hf
  have hc : GlobalTheory.ChiGrid.cloudLen D = Finset.univ.sup fun τ => (f τ).toNat := rfl
  have key : ∀ γ : ℕ, GlobalTheory.Grid.GapCond D γ ↔ GlobalTheory.ChiGrid.GapBound D 1 γ := by
    intro γ
    unfold GlobalTheory.Grid.GapCond GlobalTheory.ChiGrid.GapBound
    simp only [one_mul, hk, hn, hN, hN', hs, hc]
    refine and_congr ?_ Iff.rfl
    have hB : (0 : ℝ) ≤ ((D.R.r : ℝ) + 1) ^ 3 := by positivity
    constructor
    · intro h
      obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun τ => (f τ).toNat
      have := h τ
      rw [sqrt_intCast_eq_sqrt_toNat] at this
      rw [hτ]; exact this
    · intro h τ
      rw [sqrt_intCast_eq_sqrt_toNat]
      refine le_trans ?_ h
      have h1 : (f τ).toNat ≤ Finset.univ.sup fun τ => (f τ).toNat := Finset.le_sup (f := fun τ => (f τ).toNat) (Finset.mem_univ τ)
      have h2 : Real.sqrt (((f τ).toNat : ℕ) : ℝ) ≤ Real.sqrt (((Finset.univ.sup fun τ => (f τ).toNat : ℕ)) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast h1)
      nlinarith
  have e : {γ | GlobalTheory.Grid.GapCond D γ} = {g | GlobalTheory.ChiGrid.GapBound D 1 g} := Set.ext fun γ => key γ
  have h1 := GlobalTheory.Grid.isLeast_gap D
  rw [e] at h1
  exact h1.unique (GlobalTheory.ChiGrid.isLeast_gap D 1)

end GlobalTheory.GridJoin
end

