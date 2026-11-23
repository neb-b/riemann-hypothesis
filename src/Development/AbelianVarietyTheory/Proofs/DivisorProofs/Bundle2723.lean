module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSchemeOrdPullbackResidueDegreeCodimOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforward
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PushDiv

theorem hasDim_lt {X : Scheme.{0}} {x y : X} {d d' : ℕ} (hxy : y ⤳ x) (hne : x ≠ y)
    (hx : HasDim x d) (hy : HasDim y d') : d < d' := by
  have hsub : closure ({x} : Set X) ⊆ closure {y} := specializes_iff_closure_subset.1 hxy
  have hne' : closure ({x} : Set X) ≠ closure {y} := fun e =>
    hne (inseparable_iff_closure_eq.2 e).eq
  have h := topologicalKrullDim_add_one_le_of_ssubset X _ _ isClosed_closure
    isIrreducible_singleton.closure isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub hne')
  rw [show topologicalKrullDim (closure ({x} : Set X)) = d from hx,
    show topologicalKrullDim (closure ({y} : Set X)) = d' from hy] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d' : WithBot ℕ∞) := by exact_mod_cast h
  have h'' : d + 1 ≤ d' := by exact_mod_cast h'
  omega

theorem mult_genericPoint {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] (D : CartierDiv Z) :
    D.mult (genericPoint Z) = 0 := by
  rw [(D.isEqn_genericPoint 1).mult_eq]
  exact (unitAt_one _).ord_eq_zero

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)

theorem mult_pull_eq (w : Y) (i : B.ι) (hi : g w ∈ B.U i) :
    (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w =
      Scheme.ord (TrueGeo.SmallSec.fnMap g hη' (r i : X.functionField)) w :=
  by
  have hm : w ∈ (B.pull g).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have h := (presents_divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).isEqn
    (fun _ => i) w hm
  rw [h.mult_eq]
  rfl

theorem mult_eq_chart (z : X) (i : B.ι) (hi : z ∈ B.U i) :
    (divOfRatSec hB hr).mult z = Scheme.ord (r i : X.functionField) z :=
  ((presents_divOfRatSec hB hr).isEqn i z hi).mult_eq

theorem map_ne_genericPoint (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0) :
    g w ≠ genericPoint X := by
  intro e
  obtain ⟨i, hi⟩ := exists_chart hB (g w)
  apply hw
  rw [mult_pull_eq g hη' hB hr w i hi]
  exact (FrameGlue.Pull.unitAt_fnMap g hη' (e ▸ unitAt_genericPoint (r i).ne_zero)).ord_eq_zero

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem degree_ne_zero_and_coheight (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0)
    (hd : g.residueDegree w ≠ 0) :
    g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight (g w) = 1 := by
  have hw1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hw
  have hgw := map_ne_genericPoint g hη' hB hr w hw
  have hwY : w ≠ genericPoint Y := fun e => hw (e ▸ mult_genericPoint _)
  have AY := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hq
  have AX := _root_.GlobalTheory.MixHt.hasDim_basic k X p hp
  obtain ⟨mY, hmY⟩ := AY.1
  obtain ⟨mX, hmX⟩ := AX.1
  obtain ⟨dY, -, hdY⟩ := hmY (genericPoint Y)
  obtain ⟨dw, -, hdw⟩ := hmY w
  have hlt : dw < dY := hasDim_lt (genericPoint_specializes w) hwY hdw hdY
  obtain ⟨e, rfl⟩ : ∃ e, dY = e + 1 := ⟨dY - 1, by omega⟩
  have hYdim : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (AY.2.2.2.2.2 Y (e + 1)).1 hdY
  have hwe : HasDim w e := ((_root_.GlobalTheory.MixHt.dimOne k Y q hq e hYdim).1 w).1 hw1
  obtain ⟨dgw, -, hdgw⟩ := hmX (g w)
  obtain ⟨dX, -, hdX⟩ := hmX (genericPoint X)
  have h1 := _root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w e dgw hwe hdgw
  have hdX' : HasDim (g (genericPoint Y)) dX := by rw [hη]; exact hdX
  have h2 := _root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) (e + 1) dX hdY hdX'
  have h3 : dgw < dX := hasDim_lt (genericPoint_specializes (g w)) hgw hdgw hdX
  have he : e = dgw := h1.2.1 hd
  have hXe : dX = e + 1 := by omega
  refine ⟨h2.2.2 hXe.symm, ?_⟩
  have hXdim : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (AX.2.2.2.2.2 X (e + 1)).1 (hXe ▸ hdX)
  exact ((_root_.GlobalTheory.MixHt.dimOne k X p hp e hXdim).1 (g w)).2 (he ▸ hdgw)

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}


open Classical in
theorem fiber_sum (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) [CompactSpace Y] (z : X) :
    ∑ w ∈ (CartierDiv.finite_support_mult
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr))).toFinset with g w = z,
      (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
        (g.residueDegree w : ℤ) =
    (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
  by_cases h : g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight z = 1
  · obtain ⟨i, hi⟩ := exists_chart hB z
    have H := _root_.GlobalTheory.OrdPull.sum_ord_pull k X Y p q hp hq g hg hη h.1 z h.2 (r i : X.functionField) (r i).ne_zero
    have H2 : ∑ᶠ w ∈ g ⁻¹' {z},
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
          (g.residueDegree w : ℤ) =
        (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
      rw [mult_eq_chart hB hr z i hi, ← H]
      refine finsum_mem_congr rfl fun w hw => ?_
      have hw' : g w = z := hw
      rw [mult_pull_eq g hη' hB hr w i (by rw [hw']; exact hi)]
    rw [← H2]
    refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter,
      Set.Finite.mem_toFinset, Function.mem_support, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨left_ne_zero_of_mul h2, h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · have hR : (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z = 0 := by
      by_cases hδ : g.residueDegree (genericPoint Y) = 0
      · rw [hδ, Nat.cast_zero, zero_mul]
      · have hz : Order.coheight z ≠ 1 := fun hz => h ⟨hδ, hz⟩
        rw [show (divOfRatSec hB hr).mult z = 0 from
          by_contra fun h0 => hz (CartierDiv.coheight_eq_one_of_mult_ne_zero h0), mul_zero]
    rw [hR]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hwz : g w = z := (Finset.mem_filter.1 hw).2
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 : g.residueDegree w ≠ 0 := fun h0 => hne (by rw [h0, Nat.cast_zero, mul_zero])
    obtain ⟨hδ, hc⟩ := degree_ne_zero_and_coheight g hη' hB hr hp hq hg hη w h1 h2
    exact h ⟨hδ, hwz ▸ hc⟩

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

theorem finsum_mult_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη B hB r hr φ
  classical
  haveI := hq.isNoetherian
  haveI := hp.isNoetherian
  set D' := divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g
    (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) with hD'
  set D := divOfRatSec hB hr with hD
  set S := D'.finite_support_mult.toFinset with hS
  set T := S.image g ∪ D.finite_support_mult.toFinset with hT
  have hL : ∑ᶠ w, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) =
      ∑ w ∈ S, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hw (by simp only [h0, Int.cast_zero, zero_mul])
  have hR : ∑ᶠ z, (D.mult z : ℝ) * φ z = ∑ z ∈ T, (D.mult z : ℝ) * φ z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr fun h0 => hz (by simp only [h0, Int.cast_zero, zero_mul])
  rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := g)
    (fun w hw => Finset.mem_union_left _ (Finset.mem_image_of_mem g hw)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hF := fiber_sum g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hB hr hp hq hg hη z
  calc ∑ w ∈ S with g w = z, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w))
      = ((∑ w ∈ S with g w = z, D'.mult w * (g.residueDegree w : ℤ) : ℤ) : ℝ) * φ z := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [(Finset.mem_filter.1 hw).2]
        push_cast
        ring
    _ = (g.residueDegree (genericPoint Y) : ℝ) * ((D.mult z : ℝ) * φ z) := by
        rw [hF]
        push_cast
        ring

end GlobalTheory.PushDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundOfAnchor
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw

namespace GlobalTheory.FlatSplit

section Congr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

theorem lieFacZ_congr (x : ℝ) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : lieFacZ Dw x G = lieFacZ Dw x G' := by
  unfold lieFacZ
  congr 4
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun h (some ⟨τ, i⟩))

theorem lat_congr {C C' : Submodule c.F (Rul Xo c)} (hC : C = C') {N N' : (c.F →+* ℂ) → Rul Xo c → ℝ} (hN : N = N') :
    ((HasGram (fun σ (f : C) => N σ f) ∧ (supLat C).FG ∧ Submodule.span c.F (supLat C : Set C) = ⊤) ↔
      (HasGram (fun σ (f : C') => N' σ f) ∧ (supLat C').FG ∧ Submodule.span c.F (supLat C' : Set C') = ⊤)) ∧
    Formalism.HN.rkK (supLat C) = Formalism.HN.rkK (supLat C') ∧
    slope_sq (fun σ (f : C) => N σ f) (supLat C) = slope_sq (fun σ (f : C') => N' σ f) (supLat C') := by
  subst hC hN
  exact ⟨Iff.rfl, rfl, rfl⟩

theorem congr_exZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') :
    (GoodW U x V dict G ↔ GoodW U x V dict G') ∧ rankW U G = rankW U G' ∧
      slopeW_sq U x V dict G = slopeW_sq U x V dict G' := by
  have hC : cuspW Xo c U G = cuspW Xo c U G' := by
    ext f
    rw [mem_cuspW, mem_cuspW, h]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]
  have hP : petW U x V dict G = petW U x V dict G' := by
    funext σ f
    unfold petW petAt
    rw [lieFacZ_congr x h, modelWt_congr (U (goodOf c σ)) (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h]
  exact lat_congr hC hP

end Congr

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)

theorem exZ_shift_neg (m kc : ℕ) (c0 : ℤ) :
    exZ Dw (shiftG Dw a (2 * m) (-c0)) =
      exZ Dw (wtOf Dw (uMinus Dw a (2 * m) kc c0 + parWt Dw (anchor Dw a (2 * m) kc)) ((0 : ℤ) + (m : ℤ))) := by
  rw [Model.exZ_shiftG, zero_add, exOf]
  congr 2
  simp only [uMinus, uWt, neg_smul]
  abel

end Weights

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem twice_twist_ge {ι : Type} [Fintype ι] (w c1v : ι → ℝ) (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L) (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E) (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b) (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ Finset.univ, (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_le {PP A M : ℝ} (hH : HostNum D L PP A M) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have h1 := hH.disc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
  rw [rootDiscr_def]
  push_cast
  rw [Real.log_rpow hd, hH.deg]
  push_cast
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

end GlobalTheory.FlatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatSupp

open GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_pow {ϖ : kˣ} (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n n' : ℕ} (h : n ≤ n') :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ n')⁻¹ : kˣ) : k) := by
  rw [val_inv_pow, val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  exact inv_anti₀ (pow_pos (zero_lt_iff.2 h0) _) (pow_le_pow_of_le_one zero_le' h1 h)

theorem exists_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) :
    ∃ n : ℕ, valuation k a ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hv : valuation k a ≠ 0 := by simpa using ha
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (hϖ ▸ uniformizer_lt_one : valuation k (ϖ : k) < 1) (Units.mk0 _ hv)⁻¹
  refine ⟨n, ?_⟩
  rw [val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
  have := le_of_lt hn
  rwa [le_inv_comm₀ (pow_pos (zero_lt_iff.2 h0) _) (zero_lt_iff.2 hv)] at this

theorem exists_bound_conj {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : GL m k) (B : GL n k) :
    ∃ N : ℕ, ∀ Z : Matrix m n k, (∀ r s, ((A⁻¹ : GL m k).val * Z * B.val) r s ∈ 𝒪[k]) →
      ∀ r s, valuation k (Z r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  choose nA hnA using fun p : m × m => exists_le hϖ (A.val p.1 p.2)
  choose nB hnB using fun p : n × n => exists_le hϖ ((B⁻¹ : GL n k).val p.1 p.2)
  set N0 := Finset.univ.sup nA ⊔ Finset.univ.sup nB
  have hc : valuation k (((ϖ ^ (N0 + N0))⁻¹ : kˣ) : k) =
      valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) * valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) := by
    rw [val_inv_pow, val_inv_pow, pow_add, mul_inv]
  set c := valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k)
  have hA : ∀ r a, valuation k (A.val r a) ≤ c := fun r a =>
    (hnA (r, a)).trans (val_inv_pow_mono hϖ (le_sup_left.trans' (Finset.le_sup (f := nA) (Finset.mem_univ (r, a)))))
  have hB : ∀ b s, valuation k ((B⁻¹ : GL n k).val b s) ≤ c := fun b s =>
    (hnB (b, s)).trans (val_inv_pow_mono hϖ (le_sup_right.trans' (Finset.le_sup (f := nB) (Finset.mem_univ (b, s)))))
  refine ⟨N0 + N0, fun Z hZ r s => ?_⟩
  have hZ' : Z = A.val * ((A⁻¹ : GL m k).val * Z * B.val) * (B⁻¹ : GL n k).val := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  rw [hZ', hc]
  set W := (A⁻¹ : GL m k).val * Z * B.val
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun b _ => ?_
  rw [map_mul]
  refine mul_le_mul' (Valuation.map_sum_le _ fun a _ => ?_) (hB b s)
  rw [map_mul]
  simpa using mul_le_mul' (hA r a) (show valuation k (W a b) ≤ 1 from hZ a b)


open Matrix in
theorem flatTensor_support : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  classical
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hT
  choose N hN using fun b : Edge => exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  refine ⟨(oppositePath G.m).toFinset.sup N, fun x y hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, flatIntegrand hs ψ (moved G keep g T) x y v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    unfold flatTensor
    simp [h]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hv
    simp [flatIntegrand, moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤
      valuation k (((ϖ ^ (oppositePath G.m).toFinset.sup N)⁻¹ : kˣ) : k) := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s)
      (val_inv_pow_mono hϖ (Finset.le_sup (f := N) (List.mem_toFinset.2 hb)))
    have hm : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm r s
  refine ⟨fun j hj r s hr => ?_, fun i hi r s => ?_⟩
  · have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    by_cases hj' : j < G.m - 1
    · have h := key _ hmem (frame (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) (Sum.inl s))
        (frame (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j) (by have := topRank_add hs (j + 1); omega) (Sum.inl r))
      rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
      simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, basePt, Free, Kept] using h
    · have hjm : j + 1 = G.m := by omega
      have hrk := topRank_add hs (j + 1)
      have hrk' := topRank_add hs j
      have hr' : r.val < G.rank (G.m, j + 1) := by
        have := hr hjm
        have h2 : (topLast G (j + 1)).val = topRank G (j + 1) - 1 := rfl
        rw [Ne, Fin.ext_iff, h2] at this
        have := r.2
        omega
      have h := key _ hmem (show Fin (G.rank (G.m, j)) from ⟨s.val, by have := s.2; omega⟩)
        (show Fin (G.rank (G.m, j + 1)) from ⟨r.val, hr'⟩)
      rw [fill_theta, transpose_apply, downMap, dite_eq_right hj', dite_eq_left hjm] at h
      simpa using h
  · have hmem : Edge.ex i G.m ∈ oppositePath G.m := by simp [oppositePath]; omega
    have h := key _ hmem s r
    rwa [fill_ex, transpose_apply] at h

end GlobalTheory.FunObj.FlatSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  first | (exact @GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (exact GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (intros; apply GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf <;> assumption)
end

