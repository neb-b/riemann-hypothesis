module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfGivenFnDown
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.FlipStart.ColSB

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem stepFn_congr_red' (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) (w : Pl D.host.E)
    {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
  · exact GlobalTheory.FlipTop.stepFn_congr_red G hL t hj hw ha hb N N' h
  · have hP : w ∉ L.Pg := fun h => hw (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw (Finset.mem_union_right _ h)
    have hI : ∀ M : Matrix (Fin b) (Fin a) (OA D),
        GlobalTheory.StepData.IntM ((M.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
      intro M i l
      have h1 := (mem_OA_iff _).1 (M (ixOf G t w hb i) (ixOf G t w ha l)).2 w
      show cptO w (M (ixOf G t w hb i) (ixOf G t w ha l)) ∈ _
      rw [cptO_apply]
      exact (vEq w).le_one_iff_le_one.2 h1
    unfold stepFn
    simp only [if_neg hP, if_neg hQ, Set.indicator_apply, Set.mem_setOf_eq, if_pos (hI N), if_pos (hI N'), Pi.one_apply]


open Classical in
def colFn {G : GridData L sc} (B : Frames G) (t : T) (e : AE D) (j : ℕ) (ha : (G.V (.grid 0 j)).rank = D.R.r + j * D.R.t)
    (hb : (G.V (.grid 0 (j + 1))).rank = D.R.r + (j + 1) * D.R.t)
    (x : Mx D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : ℂ :=
  if IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) then
    ∏ w ∈ locPl G t, stepFn L t w j
      (((fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha))
  else 0


set_option maxHeartbeats 1000000 in
theorem isSBHalf_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (j : ℕ) (hj : j < D.R.m) :
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ locPl G t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (locPl G t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ locPl G t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold colFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold colFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red' G hL t hj w _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold colFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this


open Classical in
theorem givenFn_down_eq_colFn (G : GridData L sc) (B : Frames G) {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (Φ : G.Datum) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) = colFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj) := by
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  obtain ⟨-, c1, c0⟩ := cpt_idemSum he
  funext x
  set N := fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb)
      (ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((ixOf G t w hb).symm i) ((ixOf G t w ha).symm l), fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  unfold GlobalTheory.FlipStart.givenFn colFn
  rw [Finset.prod_congr rfl fun w _ => hR w]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  have hex : e • x = x := Matrix.ext fun p q => by rw [Matrix.smul_apply, smul_eq_mul]; exact hx p q
  have hNe : N = toEAf D e • N := by
    rw [hN, ← fr_smul]
    congr 1
    conv_lhs => rw [← hex]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hint : IsIntM N ↔ ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      exact (vEq w).le_one_iff_le_one.2 ((mem_OA_iff _).1 (h i l) w)
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      by_cases hw : w ∈ locPl G t
      · exact (vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [hNe, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c0 w hw, zero_mul]
        simp
  rw [if_pos hx]
  by_cases H : ∀ w ∈ locPl G t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos ⟨hx, hint.2 H⟩]
  · rw [if_neg fun h => H (hint.1 h.2)]
    push_neg at H
    obtain ⟨w, hw, hn⟩ := H
    refine Finset.prod_eq_zero hw ?_
    by_contra h0
    exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))

theorem isSBHalf_givenFn_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) (j : ℕ), j < D.R.m → ∀ (Φ : G.Datum) (e : AE D), IsIdemSum e (locPl G t) →
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j)) := by
  intro D T L sc G B μ₀ hL t j hj Φ e he
  rw [givenFn_down_eq_colFn G B hL t j hj Φ he]
  exact isSBHalf_colFn G B hL t he j hj

end GlobalTheory.FlipStart.ColSB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedInvariantIntegralDoubleCosetCellSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.CellInt

theorem cellBot_iff {G : Type} [Group G] {R K : Subgroup G} {b x : G} :
    (∃ r ∈ R, ∃ a ∈ (⊥ : Subgroup G), ∃ k ∈ K, x = r * a * b * k) ↔ ∃ r ∈ R, ∃ k ∈ K, x = r * b * k := by
  constructor
  · rintro ⟨r, hr, a, ha, k, hk, rfl⟩
    rw [Subgroup.mem_bot] at ha
    subst ha
    exact ⟨r, hr, k, hk, by simp⟩
  · rintro ⟨r, hr, k, hk, rfl⟩
    exact ⟨r, hr, 1, Subgroup.one_mem _, k, hk, by simp⟩

theorem cellWt_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (R K : Subgroup G) (ρ : Measure R) (μ : Measure G) (b : G) :
    cellWt ρ μ K b = (((μ (K : Set G)).toReal / (ρ (cellSet R K b b)).toReal : ℝ) : ℂ) := by
  simp only [cellWt, cellSet, measureReal_def, mul_assoc]

theorem niter_cellSum_at (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (R K : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (hl : l.Nodup)
    (hyp : ∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧
      (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) :
    ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ) (h : ∀ i, H i),
      (∀ β ∈ S, ∀ i, i ∉ l → b β i = h i) →
      (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q →
      (∀ g, (∀ i, i ∉ l → g i = h i) → q g ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) g) →
      NIter ρ μ q l h (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  induction l with
  | nil =>
    intro X S b q h hb hd _ hs
    simp only [NIter, List.map_nil, List.prod_nil, one_mul]
    have hbh : ∀ β ∈ S, b β = h := fun β hβ => funext fun i => hb β hβ i (by simp)
    have hsub : ∀ β ∈ S, ∀ β' ∈ S, β = β' := fun β hβ β' hβ' => hd β hβ β' hβ' (fun i hi => by simp at hi)
    by_cases hq : q h = 0
    · rw [hq]
      exact Finset.sum_eq_zero fun β hβ => by rw [hbh β hβ, hq]
    · obtain ⟨β, hβ, -⟩ := hs h (fun _ _ => rfl) hq
      rw [Finset.sum_eq_single β (fun β' hβ' hne => absurd (hsub β' hβ' β hβ) hne) (fun h' => absurd hβ h'), hbh β hβ]
  | cons i l' ih =>
    intro X S b q h hb hd hq hs
    classical
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨hcl, hkc, hko, hρ, hρi, hμ, hμr⟩ := hyp i (by simp)
    have hyp' : ∀ j ∈ l', _ := fun j hj => hyp j (List.mem_cons_of_mem _ hj)
    have hq' : BiInv R K l' q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
    have hne : ∀ j ∈ l', j ≠ i := fun j hj hji => hi (hji ▸ hj)
    set Wt' : X → ℂ := fun β => (l'.map fun j => cellWt (ρ j) (μ j) (K j) (b β j)).prod with hWt'
    have qinv : ∀ β g, g ∈ dcos (R i) (K i) (b β i) → q (Function.update (b β) i g) = q (b β) := by
      rintro β g ⟨r, hr, k, hk, rfl⟩
      have h1 := (hq i (by simp) (b β)).1 r hr
      have h2 := (hq i (by simp) (Function.update (b β) i (r * b β i))).2 k hk
      simp only [Function.update_self, Function.update_idem] at h2
      rw [h2, h1]
    refine ⟨fun g => ∑ β ∈ S, Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then 1 else 0), ?_, ?_⟩
    · haveI := hρ; haveI := hρi; haveI := hμ
      have hS := quotient_integral_finset_sum S (fun β g => Wt' β * q (b β) * (if g ∈ dcos (R i) (K i) (b β i) then (1 : ℂ) else 0))
        (fun β => Wt' β * q (b β) * (((μ i (K i : Set (H i))).toReal / (ρ i (cellSet (R i) (K i) (b β i) (b β i))).toReal : ℝ) : ℂ))
        (fun β _ => by
          have := (isQuotientIntegral_indicator_doubleCoset (R i) (K i) hcl hkc hko (ρ i) (μ i) (b β i)).smul (Wt' β * q (b β))
          convert this using 1)
      convert hS using 1
      apply Finset.sum_congr rfl
      intro β _
      rw [List.map_cons, List.prod_cons, cellWt_eq (R i)]
      ring
    · intro g
      have key := ih hl' hyp' X (S.filter fun β => g ∈ dcos (R i) (K i) (b β i)) (fun β => Function.update (b β) i g) q
        (Function.update h i g) ?base ?dist hq' ?supp
      · convert key using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro β _
        split_ifs with hg
        · have e : (l'.map fun j => cellWt (ρ j) (μ j) (K j) (Function.update (b β) i g j)).prod = Wt' β := by
            rw [hWt']
            congr 1
            apply List.map_congr_left
            intro j hj
            rw [Function.update_of_ne (hne j hj)]
          rw [e, qinv β g hg, mul_one]
        · simp
      case base =>
        intro β hβ j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact hb β (Finset.mem_filter.1 hβ).1 j (by simp [hji, hj])
      case dist =>
        intro β hβ β' hβ' hc
        obtain ⟨hβS, hgβ⟩ := Finset.mem_filter.1 hβ
        obtain ⟨hβS', hgβ'⟩ := Finset.mem_filter.1 hβ'
        refine hd β hβS β' hβS' ?_
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [cellBot_iff]
          have e1 := dcos_eq_of_mem hgβ
          have e2 := dcos_eq_of_mem hgβ'
          have hm : b β' j ∈ dcos (R j) (K j) (b β' j) := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
          rw [← e2, e1] at hm
          exact hm
        · obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j hj'
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj')] using e
      case supp =>
        intro g' hg' hq0
        have hgi : g' i = g := by simpa using hg' i hi
        obtain ⟨β, hβ, hc⟩ := hs g' (fun j hj => by
          have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
          have := hg' j (fun hj' => hj (List.mem_cons_of_mem _ hj'))
          rwa [Function.update_of_ne hji] at this) hq0
        refine ⟨β, Finset.mem_filter.2 ⟨hβ, ?_⟩, ?_⟩
        · have := hc i (by simp)
          rw [cellBot_iff, hgi] at this
          exact this
        · intro j hj
          obtain ⟨r, hr, a, ha, k, hk, e⟩ := hc j (List.mem_cons_of_mem _ hj)
          refine ⟨r, hr, a, ha, k, hk, ?_⟩
          simpa [Function.update_of_ne (hne j hj)] using e

theorem niter_cellSum : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)), (∀ i ∈ l, IsClosed (R i : Set (H i)) ∧ IsCompact (K i : Set (H i)) ∧ IsOpen (K i : Set (H i)) ∧ (ρ i).IsHaarMeasure ∧ (ρ i).IsInvInvariant ∧ (μ i).IsHaarMeasure ∧ (μ i).IsMulRightInvariant) → ∀ (X : Type) (S : Finset X) (b : X → ∀ i, H i) (q : (∀ i, H i) → ℂ), (∀ β ∈ S, ∀ i, i ∉ l → b β i = 1) → (∀ β ∈ S, ∀ β' ∈ S, InCells (fun _ => ⊥) R K l (b β) (b β') → β = β') → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ β ∈ S, InCells (fun _ => ⊥) R K l (b β) h) → NIter ρ μ q l 1 (∑ β ∈ S, (l.map fun i => cellWt (ρ i) (μ i) (K i) (b β i)).prod * q (b β)) := by
  intro ι _ H _ _ _ _ _ _ _ _ R K l hl ρ μ hyp X S b q hb hd hq hs
  exact niter_cellSum_at ι H R K ρ μ l hl hyp X S b q 1 (fun β hβ i hi => by simpa using hb β hβ i hi) hd hq
    (fun g hg => hs g (fun i hi => by simpa using hg i hi))

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.PcFBVac

variable {D : D7}

theorem mxAt_mul_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (b : Mx D k l) {a : Mx D l m} (c : Mx D m n)
    (ha : MxAt P a) : MxAt P (b * a * c) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (ha s r))

theorem pcFB_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨-, H2, -⟩ := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF
  have sdT : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (H2 σ h').1
  have monoB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((H2 σ h').2.1 v).1
  have monoJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((H2 (σ + 1) h).2.1 v).2
  have sdC := GlobalTheory.CosetRow.selfDual_chi hL G (2 * σ + 2) (by omega)
  have sdS : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (node_isV G hL (X := .core (2 * (σ + 1) + 1)) (show 2 * (σ + 1) + 1 ≤ D.R.m by omega)).sd
  have sdV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * (σ + 1) + 1) 0) (show 2 * (σ + 1) + 1 ≤ D.R.m ∧ 0 ≤ D.R.m by omega)).sd
  refine _root_.GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ (G.Λ (.core (2 * (σ + 1) + 1))) (lat0 F σ h') sdS sdT _ ?_
  intro u hu
  have hw := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdC.1 sdC.2 (fun _ => True) _).1 hu.1
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdS sdT]
  have hu' : u = (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0 := by
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hu']
    exact mxAt_mul_mul _ _ hw.1
  · have hj : (F.dJ (σ + 1) h).j0 *ᵥ y ∈ latV (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) fun _ => True :=
      GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace (F.dJ (σ + 1) h) sdV.1 (fun v _ => monoJ v) hy
    have h2 := hw.2 _ hj
    have e : ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) = (F.dB σ h').j0 *ᵥ (u *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    change ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) ∈ _ at h2
    rw [e] at h2
    have h3 := GlobalTheory.FinPl.ColSplitA.mulVec_mem_latA (F.dB σ h').p0
      (fun z hz => GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits _ sdT.1 (fun v _ => monoB v) hz) h2
    rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.AscFin.PcFBVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Transfer

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D n k) :
    MxAt (fun _ => True) (x ⬝ M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D k m) :
    MxAt (fun _ => True) (M ⬝ x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem finLat_comap {m n m' n' : ℕ} {Γ : AddSubgroup (Mx D m' n')} (hΓ : FinLat Γ) (f : Mx D m n →+ Mx D m' n')
    (g : Mx D m' n' → Mx D m n) (hf : Continuous f) (hg : Continuous g) (hgf : ∀ a, g (f a) = a)
    (hfM : ∀ a, MxAt (fun _ => True) a → MxAt (fun _ => True) (f a))
    (hgM : ∀ b, MxAt (fun _ => True) b → MxAt (fun _ => True) (g b)) : FinLat (Γ.comap f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [← hgf a]
    exact hgM _ (hΓ.fin _ ha)
  · haveI : T2Space (Mx D m' n') := (GlobalTheory.MixModel.lattice_Mx D m' n').2.2.2.1
    have hc : IsClosed ((Γ.comap f : AddSubgroup _) : Set (Mx D m n)) := hΓ.cpt.isClosed.preimage hf
    refine (hΓ.cpt.image hg).of_isClosed_subset hc ?_
    intro a ha
    exact ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUΓ⟩ := hΓ.opn
    exact ⟨f ⁻¹' U, hU.preimage hf, by simpa using h0, fun a ha hA => hUΓ _ ha (hfM a hA)⟩

end Transfer

theorem pcFB_fin : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧
      ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  intro D hOff T L μ0 hL sc G W M hM F hF σ h h'
  have hlat := (_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hOff T L μ0 hL sc G W M hM F hF).1 (2 * σ + 2) (by omega)
  have hRow : FinLat (latRow G (2 * σ + 2)) := hlat.1
  have hBig : FinLat (latBig G (2 * σ + 2)) := hlat.2.2.1
  set dV := F.dJ (σ + 1) h
  set dW := F.dB σ h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finLat_comap hRow (dV.extX _) (fun w => w ⬝ dV.jX) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
      (fun a => by simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one])
      (fun a ha => mxAt_mul_right ha _) (fun b hb => mxAt_mul_right hb _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incX _)) (fun w => dW.pX ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pX, HypDec.pX_jX, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incY _)) (fun w => dW.pY ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pY, HypDec.pY_jY, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · intro u hu
    have h1 := hRow.fin _ hu
    have h2 : dW.p0 ⬝ (((dV.ext0 _).comp (dW.inc0 _)) u ⬝ dV.j0) = u := by
      simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.p0, Matrix.one_mul]
    rw [← h2]
    exact mxAt_mul_left (mxAt_mul_right h1 _) _

end GlobalTheory.AscFin
end

