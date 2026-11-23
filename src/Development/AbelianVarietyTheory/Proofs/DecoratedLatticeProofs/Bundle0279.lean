module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParameters
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

section SlopeTestRemainingChoices
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

theorem rowsND_one_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  intro CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hcC hCC D large₂ u T Z C' Cl Cg cb Cu cT C0 hC2 hH hC3 hHH hVol hAmp hSm
    hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := hc1.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hL1 := d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have hC'0 : 0 ≤ C' := (abs_nonneg C2).trans hC2
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have e3 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    calc |C2| * (D.R.m : ℝ) ^ 2 ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
          mul_le_mul hC2 (e1.trans e2) (by positivity) hC'0
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + |C2| * (D.R.m : ℝ) ^ 2 / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hVol
      hDEC := hAmp.2.2
      ha := hSm.1
      hb := hSm.2.1
      hp := hAmp.1
      hpp := hAmp.2.1
      h6 := hSm.2.2.1
      hδ := zero_le_one
      hThA := word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos Z hH.1 (hSm.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : C2 * (D.R.m : ℝ) ^ 2 / 2 ≤ |C2| * (D.R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end SlopeTestRemainingChoices

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalEmbeddingSplitPlaceBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
namespace GlobalTheory.FinPl

theorem emb_map_eq_one {D : D7} {S A L : HSp D} (o : OrthDec S A L) {R : Type} [CommRing R] (f : AE D →+* R)
    {a : GA D A} (ha : (Formalism.L2.Theta.mt A a).map f = 1) : (Formalism.L2.Theta.mt S (o.emb (a, 1))).map f = 1 := by
  rw [OrthDec.mt_emb]
  have h1 : Formalism.L2.Theta.mt L (1 : GA D L) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1]
  have hs := congrArg (fun M : Mx D S.rank S.rank => M.map f) o.sum_eq_one
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f)] at hs ⊢
  rw [ha, Matrix.mul_one, Matrix.mul_one, hs]

theorem emb_mem_grpAt {D : D7} {S A L : HSp D} (o : OrthDec S A L) (P : Pl D → Prop) {a : GA D A}
    (ha : a ∈ grpAt A P) : o.emb (a, 1) ∈ grpAt S P := by
  simp only [grpAt, congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
  have ha' : (Formalism.L2.Theta.mt A a).map (Ideal.Quotient.mk (idAt D P)) = 1 := by
    have := congrArg Units.val ha
    simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using this
  have key := emb_map_eq_one o (Ideal.Quotient.mk (idAt D P)) ha'
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using key

end GlobalTheory.FinPl


open GlobalTheory.FinPl in
theorem GlobalTheory.FinPl.emb_gl_sumFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  intro D k _ _ _ _ p n _ _ σ B β β₀ hsum g
  obtain ⟨hgrp, -⟩ := _root_.GlobalTheory.FrameAt.frame_facts D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨hgrpA, -⟩ := _root_.GlobalTheory.FrameAt.frame_facts D k p B.A n β
  have hmem : B.o.emb (β.gl g, 1) ∈ grpAt B.V₀ (· = p.v) := emb_mem_grpAt B.o _ ((hgrpA _).2 ⟨g, rfl⟩)
  obtain ⟨h, hh⟩ := (hgrp _).1 hmem
  rw [hh]
  congr 1
  set M := (Formalism.L2.Theta.mt B.V₀ (B.o.emb (β.gl g, 1))).map p.pr with hMdef
  have hM : M = β₀.b * h.val * β₀.b' := by rw [hMdef, hh, β₀.gl_mat]

  have hY : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB B.o B.ζ) i)) =
      B.o.jB.map p.pr * replicateCol (Fin 1) fun j => p.pr (ratV B.ζ j) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat, map_sum, map_mul]
  have hA : M * B.o.jA.map p.pr = B.o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : M * B.o.jB.map p.pr = B.o.jB.map p.pr := by
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jB, h1, Matrix.mul_one]
  have hemb : ((embX 1 g : GL (n ⊕ Fin 1) k) : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
  have key : M * β₀.b = β₀.b * (embX 1 g).val := by
    rw [hsum, hemb, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hY]
    congr 1
    · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one,
        Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hB, Matrix.mul_zero, zero_add, Matrix.mul_one]
  apply Units.ext
  calc h.val = β₀.b' * (β₀.b * h.val * β₀.b') * β₀.b := by
        simp only [Matrix.mul_assoc, β₀.b'b, Matrix.mul_one]
        rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
    _ = β₀.b' * (M * β₀.b) := by rw [← hM, Matrix.mul_assoc]
    _ = β₀.b' * (β₀.b * (embX 1 g).val) := by rw [key]
    _ = (embX 1 g).val := by rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClasses
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem pairAbs_big_le_sum_classes : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  intro τ Rw I H H₁ _ _ _ _ _ X k B hA hk hS
  have hG : 0 ≤ X.Gam1 := hA.2.2.le
  have hv : Summable (fun t => ‖X.vec t‖) := hA.2.1
  have hcov : X.big X.nzSet ⊆
      (⋃ s ∈ Finset.Icc 2 k, Formalism.L2.SG.LoopsCut.bigS X s) ∪ (∅ : Set (τ × τ)) := by
    intro p hp
    left
    exact Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨hp.2, hk p hp⟩, ⟨hp.1, rfl⟩⟩
  have hc := Formalism.L2.SG.LoopsCut.ampSum_cover X hv (Finset.Icc 2 k) (Formalism.L2.SG.LoopsCut.bigS X) ∅
    (X.big X.nzSet) hcov
  have h0 : Formalism.L2.SG.RowsOther.ampSum X (∅ : Set (τ × τ)) = 0 := by
    unfold Formalism.L2.SG.RowsOther.ampSum; simp
  rw [h0, add_zero] at hc
  calc X.pairAbs (X.big X.nzSet)
      ≤ X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (X.big X.nzSet) :=
        Formalism.L2.SG.RowsOther.pairAbs_le_ampSum X hG _ (Formalism.L2.SG.LoopsCut.amp_summable X hv _)
    _ ≤ X.Gam1 * ∑ s ∈ Finset.Icc 2 k, Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ s ∈ Finset.Icc 2 k, B s :=
        Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorsBijectiveAtPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllBij

section Comb

variable {G : Type} [Group G]

def act (c : G →₀ ℂ) (F : G → ℂ) : G → ℂ := c.sum fun g x => x • rTrans g F

theorem act_apply (c : G →₀ ℂ) (F : G → ℂ) (y : G) : act c F y = c.sum fun g x => x * F (y * g) := by
  simp [act, Finsupp.sum, Finset.sum_apply, rTrans]

def cmul (c d : G →₀ ℂ) : G →₀ ℂ := c.sum fun g x => d.sum fun h y => Finsupp.single (g * h) (x * y)

theorem act_cmul (c d : G →₀ ℂ) (F : G → ℂ) : act (cmul c d) F = act c (act d F) := by
  funext y
  rw [act_apply, act_apply, cmul, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul]), act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp [mul_assoc]

theorem act_single_one (F : G → ℂ) : act (Finsupp.single 1 1) F = F := by
  funext y; rw [act_apply, Finsupp.sum_single_index (by simp)]; simp

theorem act_mapDomain {H : Type} (f : H → G) (c : H →₀ ℂ) (F : G → ℂ) :
    act (Finsupp.mapDomain f c) F = c.sum fun h x => x • rTrans (f h) F := by
  rw [act, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]

theorem cmul_mem {S : Subgroup G} {c d : G →₀ ℂ} (hc : ∀ g, c g ≠ 0 → g ∈ S) (hd : ∀ g, d g ≠ 0 → g ∈ S) :
    ∀ g, cmul c d g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨a, ha, hga⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum (Finsupp.mem_support_iff.2 hg))
  obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hga)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hgb)]
  exact S.mul_mem (hc a (Finsupp.mem_support_iff.1 ha)) (hd b (Finsupp.mem_support_iff.1 hb))

theorem mapDomain_mem {H : Type} {S : Subgroup G} (f : H → G) (hf : ∀ h, f h ∈ S) (c : H →₀ ℂ) :
    ∀ g, Finsupp.mapDomain f c g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hg))
  exact hf h

def actL (c : G →₀ ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := act c
  map_add' F F' := by funext y; simp [act_apply, mul_add, Finsupp.sum_add]
  map_smul' r F := by funext y; simp [act_apply, Finsupp.mul_sum, mul_left_comm]

end Comb

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem isContAut_act {V : HSp D} (c : GA D V →₀ ℂ) {F : GA D V → ℂ} (hF : IsContAut V F) : IsContAut V (act c F) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [act_apply, act_apply]
    exact Finsupp.sum_congr fun h _ => by rw [mul_assoc, hF.1 γ hγ]
  · have : act c F = fun y => c.sum fun g x => x * F (y * g) := funext (act_apply c F)
    rw [this]
    exact continuous_finsetSum _ fun h _ => continuous_const.mul (hF.2.comp (continuous_id.mul continuous_const))

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem rep_eq (β : Frame p S n) (g : GL n k) (F : GA D S → ℂ) : β.rep g F = rTrans (β.gl g) F := rfl

theorem sum_rep_eq (β : Frame p S n) (c : GL n k →₀ ℂ) (F : GA D S → ℂ) :
    (c.sum fun g a => a • β.rep g F) = act (Finsupp.mapDomain β.gl c) F := by
  rw [act_mapDomain]; rfl

theorem ramAt_act (β : Frame p S n) (P : Pair k n) (c : GA D S →₀ ℂ)
    (hc : ∀ x, c x ≠ 0 → ∀ g, x * β.gl g = β.gl g * x) {φ₀ : GA D S → ℂ} (hφ : RamAt β P φ₀) :
    RamAt β P (act c φ₀) := by
  obtain ⟨φ, ⟨heq, hram, hcont⟩, rfl⟩ := hφ
  refine ⟨fun Q => actL c (φ Q), ⟨?_, ?_, fun Q => isContAut_act c (hcont Q)⟩, rfl⟩
  · intro g Q
    show act c (φ (g • Q)) = β.rep g (act c (φ Q))
    rw [heq g Q]
    funext y
    rw [rep_eq, rep_eq, act_apply]
    show _ = act c (φ Q) (y * β.gl g)
    rw [act_apply]
    refine Finsupp.sum_congr fun x hx => ?_
    simp only [rTrans]
    rw [mul_assoc, hc x (Finsupp.mem_support_iff.1 hx) g, mul_assoc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun Q => ?_
    have h0 := (mem_Mram φ).1 hram Q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h0, map_zero]

end Frames

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : ∀ x : GL (Fin V.rank) (AE D), Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) x =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) x) := by
    intro x; ext i j; simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = v) ≤ idOff D (· = w) := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = w := u.2
  exact ha.2 ⟨u.1, fun e => h (e.symm.trans hu)⟩

theorem grpAt_comm (V : HSp D) {v w : Pl D} (h : v ≠ w) {x y : GA D V} (hx : x ∈ grpAt V (· = w))
    (hy : y ∈ grpAt V (· = v)) : x * y = y * x :=
  (_root_.GlobalTheory.FinPl.localComponents D (· = w)).2 V |>.2.1 x hx y (congGrp_mono V (idAt_le_idOff h) hy)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A S : HSp D}

theorem gl_mem {p₀ : SplitPt D k} (β : Frame p₀ A n) (g : GL n k) : β.gl g ∈ grpAt A (· = p₀.v) :=
  ((_root_.GlobalTheory.FrameAt.frame_facts D k p₀ A n β).1 _).2 ⟨g, rfl⟩

theorem sAll_cons (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (i : ι) (l : List ι) :
    a.sAll q χ ε (i :: l) = sOp (a.α i) (a.P i) q (χ i) (ε i) ∘ a.sAll q χ ε l := rfl

theorem place (a : PairDat p A S n) (hinj : Function.Injective fun i => (p i).v) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι) :
    (∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧ (∀ g, c' g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧
      (∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act c φ) ∧
      ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ sOp (a.α i) (a.P i) q (resChar χ hχ q) ε (act c' φ) = φ) ∧
    Set.MapsTo (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} {φ | a.Ram φ} ∧
    Set.InjOn (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} := by
  obtain ⟨hbij, -, c, c', hc, hc'⟩ := _root_.GlobalTheory.FinPl.ramBijective_holds D k (p i) n q χ hχ _ rfl ε A (a.α i) (a.P i)
  have hC := mapDomain_mem _ (gl_mem (a.α i)) c
  have hC' := mapDomain_mem _ (gl_mem (a.α i)) c'
  have hT : ∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (a.α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  have other : ∀ C₀ : GA D A →₀ ℂ, (∀ g, C₀ g ≠ 0 → g ∈ grpAt A (· = (p i).v)) → ∀ j, j ≠ i → ∀ φ,
      RamAt (a.α j) (a.P j) φ → RamAt (a.α j) (a.P j) (act C₀ φ) := fun C₀ hC₀ j hj φ hφ =>
    ramAt_act _ _ C₀ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC₀ x hx) (gl_mem _ g)) hφ
  refine ⟨⟨_, _, hC, hC', hT, fun φ hφ => ?_⟩, fun φ hφ => ⟨?_, fun j => ?_⟩, hbij.injOn.mono fun φ hφ => hφ.2 i⟩
  · obtain ⟨h1, h2⟩ := hc' φ (hφ.2 i)
    rw [sum_rep_eq] at h1 h2
    refine ⟨⟨isContAut_act _ hφ.1, fun j => ?_⟩, h1⟩
    rcases eq_or_ne j i with rfl | hj
    · exact h2
    · exact other _ hC' j hj φ (hφ.2 j)
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]; exact other _ hC j hj φ (hφ.2 j)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl


open AllBij in
theorem allBijective_all : ∀ D : D7, AllBijective D := by
  intro D k _ _ _ _ ι p q χ hχ ε n _ _ A S a hinj I
  have hsub : ∀ i, grpAt A (· = (p i).v) ≤ grpAt A fun v => ∃ i, v = (p i).v :=
    fun i => congGrp_mono A (idAt_mono fun v hv => ⟨i, hv⟩)
  have key : ∀ I : List ι, Set.MapsTo (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      Set.InjOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ g, c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = act c φ) ∧
        ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (act c' φ) = φ := by
    intro I
    induction I with
    | nil =>
      have h1 : ∀ g, (Finsupp.single (1 : GA D A) (1 : ℂ)) g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v :=
        fun g h => by rw [(Finsupp.single_apply_ne_zero.1 h).1]; exact Subgroup.one_mem _
      refine ⟨fun φ h => h, fun φ _ ψ _ h => h, _, _, h1, h1, fun φ => (act_single_one φ).symm, fun φ h => ?_⟩
      rw [act_single_one]; exact ⟨h, rfl⟩
    | cons i l ih =>
      obtain ⟨⟨C, C', hC, hC', hT, hinv⟩, maps, inj⟩ := place a hinj q (χ i) (hχ i) (ε i) i
      obtain ⟨mapsl, injl, c, c', hc, hc', hl, hinvl⟩ := ih
      rw [sAll_cons]
      refine ⟨maps.comp mapsl, inj.comp injl mapsl, cmul C c, cmul c' C', cmul_mem (fun g h => hsub i (hC g h)) hc,
        cmul_mem hc' (fun g h => hsub i (hC' g h)), fun φ => ?_, fun φ hφ => ?_⟩
      · rw [act_cmul, ← hl, Function.comp_apply, hT]
      · rw [act_cmul]
        obtain ⟨h1, h2⟩ := hinv φ hφ
        obtain ⟨h3, h4⟩ := hinvl _ h1
        refine ⟨h3, ?_⟩
        rw [Function.comp_apply, h4, h2]
  obtain ⟨maps, inj, c, c', hc, hc', hT, hinv⟩ := key I
  exact ⟨⟨maps, inj, fun φ hφ => ⟨act c' φ, (hinv φ hφ).1, (hinv φ hφ).2⟩⟩, c, c',
    fun g h => h.elim (hc g) (hc' g), hT, hinv⟩

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rowColumnShape_of_windowData_width_ge_one : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  intro D C0 hC0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14⟩
  intro u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hC : 0 < C0 := lt_of_lt_of_le one_pos hC0
  have hpos : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 := by positivity
  have : (0 : ℝ) < (D.duS u : ℝ) := lt_of_lt_of_le hpos (h10 u).1
  exact_mod_cast this

end GlobalTheory.Core.Deg
end

