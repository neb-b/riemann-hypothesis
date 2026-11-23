module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorColsBEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow
section
open Matrix
open GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.GenFam

variable {G : Type} [Field G] {S : Type} {r : S → ℕ}

theorem adjoin_low (F : Type) [Field F] [Algebra F G] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (h1 : ∀ s a, u s a a = 1) (h0 : ∀ s a b, a < b → u s a b = 0) :
    IntermediateField.adjoin F (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin F
        (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, a, b⟩, rfl⟩
    show u s a b ∈ IntermediateField.adjoin F _
    rcases lt_trichotomy a b with h | h | h
    · rw [h0 s a b h]; exact zero_mem _
    · rw [h, h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (a, b), h⟩, rfl⟩
  · rintro _ ⟨⟨s, ⟨a, b⟩, h⟩, rfl⟩
    exact ⟨⟨s, a, b⟩, rfl⟩

variable {Ω : Type} [Field Ω] [Algebra Ω G]

theorem of_gen [Finite S] {u v : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G} (hu : IsGenFam Ω G u)
    (h1 : ∀ s a, v s a a = 1) (h0 : ∀ s a b, a < b → v s a b = 0)
    (h : ∀ s a b, u s a b ∈
      IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2)) :
    IsGenFam Ω G v := by
  have htop : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2) = ⊤ := by
    rw [eq_top_iff, ← hu.2.2.2]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    exact h _ _ _
  refine ⟨h1, h0, ?_, htop⟩
  rw [adjoin_low Ω v h1 h0] at htop
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range
      fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) G := by
    refine IntermediateField.isAlgebraic_adjoin_iff_top.1 ⟨fun x => ?_⟩
    exact isAlgebraic_algebraMap (⟨x, by rw [htop]; trivial⟩ : IntermediateField.adjoin Ω _)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω _ hu.2.2.1.cardinalMk_le_trdeg).1

theorem inv_mem {n : ℕ} (F : IntermediateField Ω G) (M : Matrix (Fin n) (Fin n) G) (hd : IsUnit M.det)
    (h : ∀ a b, M a b ∈ F) (a b : Fin n) : M⁻¹ a b ∈ F := by
  let M' : Matrix (Fin n) (Fin n) F := fun a b => ⟨M a b, h a b⟩
  have e : M = M'.map (algebraMap F G) := rfl
  have hd' : IsUnit M'.det := by
    rw [isUnit_iff_ne_zero] at hd ⊢
    intro h0
    apply hd
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have : M⁻¹ = (M'⁻¹).map (algebraMap F G) := by
    apply Matrix.inv_eq_right_inv
    rw [e, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd', Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact (M'⁻¹ a b).2

end PositivityTheory.Xgp.GenFam
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsFlagFrame
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map f) = f (detFac j i T) := by
  unfold detFac
  rw [CPts.minorIJ_map, CPts.minorIJ_map]
  split_ifs <;> simp

theorem muI_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    muI N j i (T.map f) = f (muI N j i T) := by
  unfold muI
  rw [CPts.minorIJ_map]
  split_ifs <;> simp

theorem zpow_sum' {σ : Type} (S : Finset σ) {x : L} (hx : x ≠ 0) (n : σ → ℤ) : x ^ (∑ p ∈ S, n p) = ∏ p ∈ S, x ^ n p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem chartMono_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartMono z c e ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

theorem chartMono_eDeg {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (τ : Ψ) (a : Fin N) (k₀ : K) :
    chartMono z c (eDeg M τ a k₀) * (z ⟨k₀, c k₀⟩ ^ 2 * ∏ i, chartMono z c (M.dy (τ, i)) ^ xiCoef τ a (τ, i)) = 1 := by
  rw [← prod_xi_pair τ a fun p => chartMono z c (M.dy p)]
  have e1 : ∏ p, chartMono z c (M.dy p) ^ xiCoef τ a p = ∏ k, z ⟨k, c k⟩ ^ ∑ p, xiCoef τ a p * M.dy p k := by
    simp only [chartMono, ← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_sum' _ (hc k)]
    exact Finset.prod_congr rfl fun p _ => by rw [← _root_.zpow_mul, mul_comm]
  have e2 : z ⟨k₀, c k₀⟩ ^ 2 = ∏ k, z ⟨k, c k⟩ ^ (if k = k₀ then (2 : ℤ) else 0) := by
    rw [Finset.prod_eq_single k₀ (fun k _ h => by rw [ite_eq_right h, zpow_zero]) (by simp), ite_eq_left rfl, zpow_ofNat]
  rw [e1, e2, chartMono, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k), eDeg]
  rw [show -(∑ p, xiCoef τ a p * M.dy p k) - (if k = k₀ then 2 else 0) + ((if k = k₀ then 2 else 0) +
    ∑ p, xiCoef τ a p * M.dy p k) = 0 by ring, zpow_zero]

theorem chartMono_dy (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (p : Ψ × Fin N) :
    chartMono z c (M.dy p) = (∏ k : NonPluckerBlocks M.blk, (z ⟨k.1, c k.1⟩ ^ M.b p k)⁻¹) *
      (M.blk p).elim 1 fun k => z ⟨k, c k⟩ := by
  rw [chartMono, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => ∀ p', M.blk p' ≠ some k)]
  congr 1
  · rw [Finset.prod_subtype (p := fun k => ∀ p', M.blk p' ≠ some k) _ (by simp)]
    refine Finset.prod_congr (by congr) fun k _ => ?_
    rw [FlagModel.dy, dite_eq_left k.2, _root_.zpow_neg]
  · cases hp : M.blk p with
    | none =>
      refine Finset.prod_eq_one fun k hk => ?_
      rw [FlagModel.dy, dite_eq_right (Finset.mem_filter.1 hk).2, hp, ite_eq_right (by simp), zpow_zero]
    | some k₁ =>
      have hk₁ : ¬ ∀ p', M.blk p' ≠ some k₁ := fun h => h p hp
      rw [Finset.prod_eq_single k₁ (fun k hk h => by
        rw [FlagModel.dy, dite_eq_right (Finset.mem_filter.1 hk).2, hp, ite_eq_right (by simpa using h.symm), zpow_zero])
        (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ k₁, hk₁⟩)).elim), FlagModel.dy, dite_eq_right hk₁, ite_eq_left hp,
        zpow_one]
      rfl

theorem blk_some {i : Fin N} (τ : Ψ) (hi : IsProperStep N j i) : ∃ k, M.blk (τ, i) = some k :=
  Option.ne_none_iff_exists'.1 fun h => (M.blk_none _).1 h hi

theorem isPt_base {z : (Σ k, ι k) → L} (hz : IsPt y z) : IsPt M.x (basePart M.blk z) :=
  hz.comp (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base)

theorem hasVal_base {z : (Σ k, ι k) → L} {s : M.Ω} {v : L} (h : HasVal M.x (basePart M.blk z) s v) :
    HasVal y z (algebraMap M.Ω Φ s) v :=
  HasVal.pull (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base) h

theorem chart_ne {z : (Σ k, ι k) → L} {F : FrameData ι Ψ N M.Ω M.blk}
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (k : NonPluckerBlocks M.blk) : z ⟨k.1, F.c k⟩ ≠ 0 := fun h =>
  hG.1 k ((mem_iff_of_homog (isMultiHomog_X _)).2 (by rw [aeval_X]; exact h))

theorem exists_flag_frame (τ : Ψ) {z : (Σ k, ι k) → L} (hz : IsPt y z) {F : FrameData ι Ψ N M.Ω M.blk}
    (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) :
    ∃ (b : Matrix (Fin N) (Fin N) Φ) (H H' : Matrix (Fin N) (Fin N) (regO y z)), IsBlockDiag j b ∧
      b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ IsBlockDiag j H ∧ H' * H = 1 ∧
      (F.T τ).map (algebraMap M.Ω Φ) * H.map (regO y z).subtype = M.g τ * b := by
  have := isLocalRing_regO hz
  let am := algebraMap M.Ω Φ
  let h := (F.T τ)⁻¹.map am * M.g τ
  have hTh : (F.T τ).map am * h = M.g τ := CPts.map_mul_inv_map am (hF.1 τ).2 _
  have hhb : IsBlockDiag j h := (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hhd : h.det ≠ 0 := fun e => (M.isUnit_det_g τ).ne_zero (by rw [← hTh, det_mul, e, mul_zero])
  have hu : ∀ q I, am (F.u q I) ∈ regO y z := fun q I =>
    (exists_hasVal_of_regAt (hG.2.1 q I).1).imp fun _ => hasVal_base M
  have hu' : ∀ I q, am (F.u' I q) ∈ regO y z := fun I q =>
    (exists_hasVal_of_regAt (hG.2.1 q I).2).imp fun _ => hasVal_base M
  obtain ⟨b, hb, hbt, hbd, hO, hO'⟩ := exists_local_frame (regO y z) M.j_le h hhb hhd fun i hi => by
    obtain ⟨k, hk⟩ := blk_some M τ hi
    obtain ⟨c, hc⟩ := hz.1 k
    have hyc := hz.coord_ne hc
    have hdet : am (detFac j i (F.T τ)) ≠ 0 :=
      (map_ne_zero am).2 (CPts.detFac_ne_zero M.j_le i (hF.1 τ).1 (hF.1 τ).2)
    have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') ≠ 0 := (map_ne_zero am).2
      (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (isPt_base M hz).le hG k'))
    let η := am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') / (am (detFac j i (F.T τ)) * y ⟨k, c⟩)
    have rel : ∀ m, η * ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j i) = y ⟨k, m⟩ / y ⟨k, c⟩ := fun m => by
      have := CPts.frame_gen M hF (RingHom.id Φ) hk m hhb isBlockDiag_one blockTriangular_one
        (by rw [mul_one]; exact hTh)
      simp only [RingHom.id_apply, Matrix.one_apply_eq, Finset.prod_const_one, mul_one] at this
      simp only [η]
      rw [div_mul_eq_mul_div, ← this]
      exact mul_div_mul_left _ _ hdet
    have hO : ∀ I, η * minorIJ h I (stepCols N j i) ∈ regO y z := fun I => by
      by_cases hI : IsStepRows N j i I
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [← dual_sum i (fun m I => am (F.u ⟨k, m⟩ I)) (fun I m => am (F.u' I ⟨k, m⟩)) (fun I I' h1 h2 => by
            have := congrArg am (hF.2.2.1 (τ, i) k hk I I' h1 h2)
            rw [map_sum] at this
            simp only [map_mul] at this
            rw [this]
            split_ifs <;> simp) (fun I => minorIJ h I (stepCols N j i))
            (fun I hI => minor_stepCols_eq_zero M.j_le h I hhb hI) I hI, Finset.mul_sum]
        refine sum_mem fun m _ => ?_
        rw [mul_left_comm, rel]
        exact mul_mem (hu' _ _) ⟨_, hasVal_ratio hz m c hc⟩
      · rw [minor_stepCols_eq_zero M.j_le h I hhb hI, mul_zero]; exact zero_mem _
    refine ⟨η, div_ne_zero hE (mul_ne_zero hdet hyc), hO, ?_⟩
    have h1 : ∑ I, (⟨_, hu ⟨k, c⟩ I⟩ : regO y z) * ⟨_, hO I⟩ = 1 := Subtype.ext (by
      have := rel c
      rw [div_self hyc, Finset.mul_sum] at this
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_one]
      rw [← this]
      exact Finset.sum_congr rfl fun I _ => by ring)
    have h2 := congrArg (valO hz) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h2
    obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2.trans_ne one_ne_zero)
    rw [map_mul] at hI
    have h3 := hasVal_valO hz ⟨_, hO I⟩
    exact ⟨I, h3.ne_zero hz (right_ne_zero_of_mul hI), _, h3.inv hz (right_ne_zero_of_mul hI)⟩
  have hd : (h * b).det ≠ 0 := by
    rw [det_mul, det_of_isUpperTriangular hbt]
    exact mul_ne_zero hhd (Finset.prod_ne_zero_iff.2 fun a _ => hbd a)
  let H : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO a c⟩
  let H' : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO' a c⟩
  have e1 : H.map (regO y z).subtype = h * b := by ext; rfl
  have e2 : H'.map (regO y z).subtype = (h * b)⁻¹ := by ext; rfl
  refine ⟨b, H, H', hb, hbt, hbd, fun a c e => Subtype.ext ((hhb.mul hb) a c e), ?_, ?_⟩
  · refine Matrix.map_injective (f := (regO y z).subtype) Subtype.val_injective ?_
    show (H' * H).map _ = (1 : Matrix (Fin N) (Fin N) (regO y z)).map _
    rw [Matrix.map_mul, e1, e2, Matrix.nonsing_inv_mul _ hd.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [e1, ← Matrix.mul_assoc, hTh]

end PositivityTheory.Xgp.W
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsCharts
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem stalkClosedPointTo_specMap_comp_eq {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) :
    ∃ e : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω),
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ ξ) =
        (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hi : IsLocalHom i := ⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have key := (SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv
    ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨h1, h2⟩ := key
  change (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1
  change Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2
  have hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [Spec.map_comp, Category.assoc, hξ]
  revert h1 h2
  generalize Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg
  subst hg
  intro h1 h2
  exact ⟨h1, h2⟩

private theorem stalkClosedPointTo_stalkSpecializes_comp {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) (g : Spec (CommRingCat.of G) ⟶ X)
    (hg : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (y : X) (hy : g (IsLocalRing.closedPoint G) ⤳ y)
    (h : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (s : X.presheaf.stalk y) :
    (Scheme.stalkClosedPointTo g).hom ((X.presheaf.stalkSpecializes hy).hom s) =
      i ((Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes h).hom s)) := by
  subst hg
  obtain ⟨e, he⟩ := stalkClosedPointTo_specMap_comp_eq ξ i
  rw [he]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]
  congr 2
  have hh := TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy
  exact congrArg (fun k => CommRingCat.Hom.hom k s) hh

theorem PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  intro X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h
  set q : Cpt ξ := ⟨f p'.1, h⟩ with hq
  have K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s) := by
    intro s
    have e1 := stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s
    rw [Scheme.stalkClosedPointTo_comp] at e1
    exact (congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1
  have F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨_, K s⟩
  have F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q := by
    intro a ha hinv
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hinv
    by_cases h0 : genMap ξ q s = 0
    · rw [h0, _root_.inv_zero]
      exact zero_mem _
    have hu : IsUnit ((f.stalkMap p'.1).hom s) := by
      have hm : (f.stalkMap p'.1).hom s * t = 1 := by
        apply hG'.inj p'
        rw [map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]
      exact isUnit_iff_exists_inv.mpr ⟨t, hm⟩
    obtain ⟨v, hv⟩ := (isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu
    refine RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩
    rw [← hv, map_units_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩
    show i (x c') / i (x c₁) ∈ regAt ξ' p'
    rw [← map_div₀]
    exact F1 _ (h2 c')
  · rintro ⟨h1, h2⟩
    have h1' : x c₁ ≠ 0 := fun h0 => h1 (by simp [h0])
    obtain ⟨c, hc⟩ := hT.cover q
    obtain ⟨hc0, hc⟩ := hc
    refine ⟨h1', fun c' => ?_⟩
    have hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p' := by
      rw [map_div₀, inv_div]
      exact h2 c
    have hw := F2 _ (hc c₁) hinv
    have e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hc c') hw
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsField
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' x x' A A' h i j d hov hcov
  obtain ⟨hd, hf, -⟩ := hov
  have hgen : genPt A'.ξ₀ = genPt A.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt A'.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso A'.gen₀ A.gen₀ hgen
  have e1 : spMap A'.fn ≫ A'.ξ₀ = A'.ξ ≫ A'.f := A'.fn_over.symm
  have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
  have e3 : A'.ξ ≫ h = spMap i ≫ A.ξ := hd
  have e5 : spMap (A.fn.comp ψ.toRingHom) ≫ A'.ξ₀ = A.ξ ≫ A.f := by
    rw [FlagPull.spMap_comp, Category.assoc, hψ, e2]
  refine ⟨A.fn.comp ψ.toRingHom, ?_, e5.symm, ?_⟩
  · haveI := FlagPull.mono_of_isCptGen A'.gen₀
    have e4 : spMap (i.comp (A.fn.comp ψ.toRingHom)) = spMap A'.fn := by
      refine (cancel_mono A'.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, Category.assoc, e5, e1, hf, ← Category.assoc, ← e3, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  · letI := A.fn.toAlgebra
    letI := (A.fn.comp ψ.toRingHom).toAlgebra
    exact (Algebra.finrank_eq_of_equiv_equiv ψ (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)).trans hcov.2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsPullmap
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem flagStep_comp {G M N : Type} [Field G] [AddCommGroup M] [Module G M] [AddCommGroup N] [Module G N]
    (T : M →ₗ[G] N) {r : ℕ} (b : Fin r → M) (i : ℕ) :
    flagStep G (fun k => T (b k)) i = (flagStep G b i).map T := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

end PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_pullmap : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) := by
  intro X X' Ω G _ _ _ ξ ξ' f E E₁ _ _ _ _ ι π L r c u hπ hfl p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := hfl p hp
  let T := π.baseChange G
  let T' := ι.baseChange G
  have hπι : ∀ e, π (ι e) = e := fun e => LinearMap.congr_fun hπ e
  have hT : ∀ e, T (TensorProduct.mk Ω G E₁ 1 (ι e)) = TensorProduct.mk Ω G E 1 e := fun e => by
    simp [T, hπι]
  have hT' : ∀ e, T' (TensorProduct.mk Ω G E 1 e) = TensorProduct.mk Ω G E₁ 1 (ι e) := fun e => by
    simp [T']
  have hbk : ∀ k, T' (T (b k)) = b k := by
    intro k
    have h1 : b k ∈ flagStep G b r := Submodule.subset_span ⟨k, k.2, rfl⟩
    rw [hb] at h1
    have h2 : flagStep G (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) r ≤
        LinearMap.eqLocus (T' ∘ₗ T) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, -, rfl⟩
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, hT, hT']
      rfl
    exact h2 h1
  refine ⟨U, hU, fun k => T (b k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [c_fm_exists_flags_pullmap.flagStep_comp, hb, ← c_fm_exists_flags_pullmap.flagStep_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hT]
  · obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨LinearIndependent.of_comp T' ?_, ?_⟩
    · have : (T' ∘ fun k => T (b k)) = b := funext hbk
      rwa [this]
    · have h3 := congrArg (Submodule.map (T.restrictScalars (regAt ξ' q))) hsp
      have h4 := h3.trans ((Submodule.map_span _ _).trans (congrArg _ (Set.range_comp _ _).symm))
      refine Eq.trans ?_ h4
      refine Eq.trans ?_ (Submodule.map_span _ _).symm
      refine congrArg (Submodule.span (regAt ξ' q)) ?_
      ext y
      constructor
      · rintro ⟨h, e, he, rfl⟩
        exact ⟨_, ⟨h, ι e, ⟨e, he, rfl⟩, rfl⟩, hT e⟩
      · rintro ⟨_, ⟨h, _, ⟨e, he, rfl⟩, rfl⟩, rfl⟩
        exact ⟨h, e, he, hT e⟩
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsTie
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K₀ _ J₀ _ x₀ 𝔐 bW bO n φ X' ξ' h
  let e : FlagIx ((k : K₀) → J₀ k) n (rk (CMType H) D.p D.q) ≃
      ((k : K₀ ⊕ StepIx (CMType H) D.p D.q) → idx J₀ n k) :=
    (Equiv.sumPiEquivProdPi (idx J₀ n)).symm
  have h2 := coordTie_comp_equiv h e
  convert h2 using 1
  funext cJ
  obtain ⟨c0, c1⟩ := cJ
  change _ = seg (yv (aOf 𝔐 bW bO φ) x₀) (e (c0, c1))
  simp only [seg, flagCoord, Fintype.prod_sum_type, map_prod]
  congr 1
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XContract
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  intro K _ ι _ n
  refine ⟨fun V hK hV => ?_, fun P hP => ⟨?_, ?_⟩⟩
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  · haveI : P.IsPrime := hP.2.1.1
    apply ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq
    intro m hm
    have h2 : m ∈ Ideal.comap (C : ℤ →+* MRing ι) P := hm
    rw [hP.2.2.1] at h2
    simpa using h2
end

