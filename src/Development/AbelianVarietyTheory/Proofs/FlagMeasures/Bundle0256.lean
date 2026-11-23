module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem standingHypotheses_of_glob0_nodes_Tr_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD →
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' →
      Glob0 D x eps CD Cg → Nodes D x eps →
      (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) →
      StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  intro eps CD he he52 hCD C' Cl Cg hCl hClD
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.Diag.PG.rankNums_first_half eps CD he he52 hCD C'
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.Diag.PG.rankNums_first_half eps CD he he52 hCD Cl
  obtain ⟨x3, h3⟩ := _root_.GlobalTheory.Diag.PG.rankNums_rootDisc eps CD he he52 hCD Cl hCl
  obtain ⟨x4, h4⟩ := _root_.GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes eps CD he he52 hCD Cl hCl
  obtain ⟨x5, h5⟩ := _root_.GlobalTheory.Diag.PG.gaps_exceed eps CD he he52 hCD Cl hCl
  refine ⟨max x1 (max x2 (max x3 (max x4 x5))), fun x hx D large₂ cT CT hL h8 G N hT => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hx4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have R := G.nums
  obtain ⟨a1, -, -, -, -, -, -, -⟩ := h1 x hx1 _ _ _ _ _ R
  obtain ⟨-, a2, a3, a4, a5, -, -, -⟩ := h2 x hx2 _ _ _ _ _ R
  obtain ⟨c1, c2, c3⟩ := h3 x hx3 _ _ _ _ _ R
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := h4 x hx4 _ _ _ _ _ R
  have e := h5 x hx5 _ _ _ _ _ R (D.R.r : ℝ) k_le_r r_le_two_k
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hb : large₂.sc.b = bx x eps := by
    show Real.exp large₂.sc.L = Real.exp (x ^ eps)
    rw [hL]
  have hrd := G.rd_lo
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hbj : ∀ τ j, 1 ≤ j → j ≤ D.R.m → Real.sqrt (bx x eps) ≤ bOne D τ j ∧ bOne D τ j ≤ bx x eps ^ 2 := by
    intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ j (by omega)]
    exact N.b_win τ ⟨j, by omega⟩
  have hrS : (D.R.rS : ℝ) = (D.R.m : ℝ) / 2 - 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have h' : D.R.rS + 1 = a := by unfold Ranks.rS; omega
    have e1 : (D.R.rS : ℝ) + 1 = a := by exact_mod_cast h'
    have e2 : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    linarith
  rw [hb] at hT
  unfold StandingHypotheses
  dsimp only
  rw [hb, hL]
  refine ⟨h8, a1, by exact_mod_cast R.mf, by exact_mod_cast R.fk, by rw [hrS]; exact a2, a3, a4, ?_, ?_, c2, c3,
    (G.g_win 0).1, (G.g_win 0).2, (G.g_win 1).1, (G.g_win 1).2, ?_, ?_, ?_, ?_, d7 hClD, ?_, ?_, hT, a5, hCl⟩
  · intro τ j h1 h2
    exact le_trans d2 (hbj τ j h1 h2).1
  · rw [hv, Real.log_div (by linarith) (by norm_num)]
    exact c1
  · intro τ j h1 h2
    rw [Real.rpow_two]
    exact ⟨le_trans d3 (hbj τ j h1 h2).1, (hbj τ j h1 h2).2⟩
  · intro τ
    have a := N.bm τ
    have e' : D.R.m = D.R.m - 1 + 1 := by omega
    have b := bOne_succ τ (D.R.m - 1) (by omega)
    rw [← e'] at b
    have b0 : bOne D τ 1 = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := bOne_succ τ 0 (by omega)
    rw [b, b0]
    exact a
  · intro u τ
    have e1 : uOne D u τ 1 = uFirst D τ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 k_pos, D.hcW_first u τ k_pos]
      rfl
    rw [e1]
    by_cases ht : Top D τ
    · exact le_trans (N.top τ ht).2.1 d6
    · have o := (G.off τ ht).2.1
      have v0 := (G.cloud τ ⟨0, by omega⟩).2
      have v0' : vFirst D τ ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) := v0
      linarith
  · rw [hv]; linarith
  · intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ (j + 1) (by omega), bOne_succ τ j (by omega)]
    have g := G.gap τ j (by omega)
    push_cast at g
    linarith [e.2.2.2]
  · intro τ i h
    by_cases c1 : i.1 + 1 < D.R.k - 1
    · rw [lamS_lo τ i (by omega), lamS_lo τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 (by omega),
        vOne_succ τ (i.1 + 1) c1]
      have g := D.s.cloud_gap D.u₀ τ i.1 c1
      simp only [D.hcW_v] at g
      have g' := congrArg (fun q : ℚ => (q : ℝ)) g
      push_cast at g'
      linarith [e.1]
    · by_cases c2 : i.1 < D.R.k - 1
      · rw [lamS_lo τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 c2]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = 0 + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ 0 (by omega)]
        have v0 := (G.cloud τ ⟨i.1, c2⟩).1
        have b0 := (N.b_win τ ⟨0, by omega⟩).1
        linarith [e.2.1]
      · have hi := i.isLt
        rw [lamS_hi τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = (i.1 - (D.R.k - 1) + 1) + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ (i.1 - (D.R.k - 1)) (by omega), bOne_succ τ (i.1 - (D.R.k - 1) + 1) (by omega)]
        have g := G.gap τ (i.1 - (D.R.k - 1)) (by omega)
        push_cast at g
        linarith [e.2.2.1]

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.EichlerUnip

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

noncomputable def eich (σ w : S.V) (t : E) : S.V →ₗ[E] S.V :=
  LinearMap.id - (S.hT σ).smulRight w + (S.hT w).smulRight σ - t • (S.hT w).smulRight w

theorem eich_apply (σ w : S.V) (t : E) (x : S.V) :
    eich S σ w t x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  simp only [eich, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, mul_smul]

theorem herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← LinearMap.isSymm_def.mp S.herm x y, starRingEnd_apply]

theorem eich_inv (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x : S.V) : eich S (-σ) w (star t) (eich S σ w t x) = x := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add (f := _), map_neg, map_smul,
    LinearMap.neg_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero]
  rw [← ht]
  module

theorem eich_isom (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x y : S.V) :
    S.hT (eich S σ w t x) (eich S σ w t y) = S.hT x y := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add (f := _), map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply,
    LinearMap.add_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero, starRingEnd_apply,
    star_mul']
  rw [herm S w x, herm S σ x, ← ht]
  ring

noncomputable def eichE (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (eich S σ w t) (eich S (-σ) w (star t))
    (LinearMap.ext fun x => by
      have := eich_inv S (-σ) w (star t) hw (by simp [hwσ]) (by simp [← ht, add_comm]) x
      simpa using this)
    (LinearMap.ext fun x => eich_inv S σ w t hw hwσ ht x)

theorem integral_of_unimodular {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, (o : E) = S.hT x y := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hΛ
  have h1 : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hΛ]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one] at h1
  obtain ⟨o, ho⟩ := h1 x hx
  exact ⟨o, ho⟩

theorem smul_mem_of {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : ∃ o : 𝓞 E, (o : E) = c) {x : S.V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  have h := Λ.smul_mem o hx
  rw [← algebraMap_smul E o x] at h
  exact h

theorem eich_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {σ w : S.V} {t : E}
    (hσ : σ ∈ Λ) (hw : w ∈ Λ) (ht : ∃ o : 𝓞 E, (o : E) = t) {x : S.V} (hx : x ∈ Λ) :
    eich S σ w t x ∈ Λ := by
  rw [eich_apply]
  obtain ⟨a, ha⟩ := integral_of_unimodular S hΛ hσ hx
  obtain ⟨b, hb⟩ := integral_of_unimodular S hΛ hw hx
  obtain ⟨o, ho⟩ := ht
  have hob : ∃ c : 𝓞 E, (c : E) = t * S.hT w x := ⟨o * b, by rw [← ho, ← hb]; rfl⟩
  exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem hx (smul_mem_of S ⟨a, ha⟩ hw)) (smul_mem_of S ⟨b, hb⟩ hσ))
    (smul_mem_of S hob hw)

theorem star_int {t : E} (ht : ∃ o : 𝓞 E, (o : E) = t) : ∃ o : 𝓞 E, (o : E) = star t := by
  obtain ⟨o, rfl⟩ := ht
  exact ⟨⟨star (o : E), (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem iso_X {r : ℕ} {T : E} (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) :
    S.hT x y = 0 := by
  have key : ∀ a, ∀ v ∈ Submodule.span E (Set.range F.fl.e), S.hT (F.fl.e a) v = 0 := by
    intro a v hv
    induction hv using Submodule.span_induction with
    | mem u hu => obtain ⟨b, rfl⟩ := hu; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  have key2 : ∀ u ∈ Submodule.span E (Set.range F.fl.e), S.hT u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨a, rfl⟩ := hu; exact key a y hy
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key2 x hx

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem exists_eichler (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) {r : ℕ} {T : E} (F : LFlag S r T)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (σ : S.V) (hσ : σ ∈ Lrep Λ F)
    (w : S.V) (hw : w ∈ XLam Λ F) :
    ∃ n ∈ NLam Λ F, ∃ t : E, (∀ x ∈ Xsp F, n x = x) ∧
      ∀ x, n x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  obtain ⟨hσΛ, hσX⟩ := Submodule.mem_inf.mp hσ
  obtain ⟨hwΛ, hwX⟩ := Submodule.mem_inf.mp hw
  have hσX' : σ ∈ orth S (Xsp F) := hσX
  have hwX' : w ∈ Xsp F := hwX
  have hww : S.hT w w = 0 := iso_X S F hwX' hwX'
  have hwσ : S.hT w σ = 0 := (mem_orth S).mp hσX' w hwX'
  have hσσ : star (S.hT σ σ) = S.hT σ σ := (herm S σ σ).symm
  obtain ⟨oσ, hoσ⟩ := integral_of_unimodular S hΛ hσΛ hσΛ
  have ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ := by
    rw [star_mul', hσσ]
    linear_combination (S.hT σ σ) * hθ
  have htI : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ := ⟨θ * oσ, by rw [← hoσ]; rfl⟩
  have hfix : ∀ x ∈ Xsp F, eich S σ w ((θ : E) * S.hT σ σ) x = x := by
    intro x hx
    have h1 : S.hT σ x = 0 := by rw [herm, (mem_orth S).mp hσX' x hx, star_zero]
    have h2 : S.hT w x = 0 := iso_X S F hwX' hx
    rw [eich_apply, h1, h2]
    simp
  refine ⟨eichE S σ w _ hww hwσ ht, ?_, _, hfix, fun x => eich_apply S σ w _ x⟩
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change ∀ x y, S.hT (eich S σ w _ x) (eich S σ w _ y) = S.hT x y
    exact fun x y => eich_isom S σ w _ hww hwσ ht x y
  · apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact eich_mem S hΛ hσΛ hwΛ htI hy
    · intro y hy
      refine ⟨(eichE S σ w _ hww hwσ ht).symm y, ?_, by simp⟩
      exact eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htI) hy
  · intro j x hx
    have hxX : x ∈ Xsp F := Submodule.span_mono (Set.image_subset_range _ _) hx
    change eich S σ w _ x - x ∈ _
    rw [hfix x hxX, sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have h2 : S.hT w x = 0 := (mem_orth S).mp hx w hwX'
    have : eich S σ w ((θ : E) * S.hT σ σ) x - x = -(S.hT σ x • w) := by
      rw [eich_apply, h2]
      module
    change eich S σ w _ x - x ∈ _
    rw [this]
    exact (Xsp F).neg_mem ((Xsp F).smul_mem _ hwX')

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eichler_mem_unipotent : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → ∀ σ ∈ Lrep Λ F, ∀ w ∈ XLam Λ F, ∃ n ∈ NLam Λ F, ∃ t : D.host.E, (∀ x ∈ Xsp F, n x = x) ∧ ∀ x, n x = x - (hS D).hT σ x • w + (hS D).hT w x • σ - (t * (hS D).hT w x) • w := by
  intro D T F Λ hΛ σ hσ w hw
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  refine exists_eichler (hS D) θ ?_ F Λ hΛ σ hσ w hw
  have h := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hθ
  simp only [map_add (f := _), map_one, GlobalTheory.InertSign.sgO_coe] at h
  rw [GlobalTheory.NormSum.AdLattice.star_eq_conj D]
  exact h

end GlobalTheory.EichlerUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBesselCoefficientCompactLe
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem lint_Afun_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ K hK
  classical
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨-, hrep, -, -, hHaar, hSchur, -, hDecay, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hμS, -⟩ := hSide'
  obtain ⟨hclG, -, -, hclS, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hUni : IsUnimod (Sset k r z) μS := ((GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1) hμS
  obtain ⟨ν, hν⟩ := exists_isQuotMeas_Sset k r z μG μS hz hT hHaar hμS
  obtain ⟨C₀, hC₀, hC⟩ := _root_.GlobalTheory.SgInf.lint_compact_le_quot k r (Sset k r z) μG μS ν K hclS hHaar hμS hUni hν hK
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w :=
    (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := fun u (hu : u ∈ DD σ w) => _root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide
    (DD σ w : Set H) (fun g hg x hx => hstab g hg x hx) hDecay u hu v hv
  have hPi := (GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ).2.1
  have hD3 := fun u (hu : u ∈ DD σ w) =>
    _root_.GlobalTheory.SgInf.normIdentity_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  set ψ := psiGen k r z c with hψ
  set bc : ℂ := ⟪ξ, be ψ π μS σ v v ξ⟫_ℂ with hbc
  refine ⟨C₀.toReal * bc.re / d, fun u hu => ?_⟩
  set A : Mt k r → Wp := fun x => Afun ψ π μS σ u v ξ (Matrix.of x) with hA
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GM : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hGM
  have hGMc : IsClosed GM := hclG.2.1.preimage hof
  have hAc : ContinuousOn A GM := by
    have h1 : ContinuousOn (fun x : Mat k r => Afun ψ π μS σ u v ξ x) (GG k r) :=
      (hD1 u hu).2.2.2.clm_apply continuousOn_const
    exact h1.comp hof.continuousOn (fun x hx => hx)
  have hae : ∀ᵐ x ∂μG, x ∈ GM := by
    rw [ae_iff]; exact hHaar.2.2.1
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable A (μG.restrict GM) :=
      hAc.aestronglyMeasurable hGMc.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1.restrict
  set F : Mt k r → ENNReal := GM.indicator (fun x => (‖A x‖₊ : ENNReal) ^ 2) with hF
  have hFm : Measurable F := by
    have h1 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal) ^ 2) GM := by
      have h0 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal)) GM :=
        (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hAc
      exact (ENNReal.continuous_pow 2).comp_continuousOn h0
    have h2 := ContinuousOn.measurable_piecewise h1
      (continuousOn_const (c := (0 : ENNReal)) (s := GMᶜ)) hGMc.measurableSet
    have h3 : F = GM.piecewise (fun x => (‖A x‖₊ : ENNReal) ^ 2) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ GM <;> simp [hF, hx]
    rw [h3]; exact h2
  have hFinv : ∀ s ∈ Sset k r z, ∀ x, F (lmulM s x) = F x := by
    intro s hs x
    have hsG : s ∈ GG k r := hclS.1 hs
    have hmem : lmulM s x ∈ GM ↔ x ∈ GM := by
      constructor
      · intro h
        have h1 : s⁻¹ * (s * (Matrix.of x : Mat k r)) ∈ GG k r :=
          hclG.2.2.2.1 _ (hclG.2.2.2.2 _ hsG) _ h
        have h2 : s⁻¹ * (s * (Matrix.of x : Mat k r)) = Matrix.of x := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hsG), Matrix.one_mul]
        rw [h2] at h1; exact h1
      · intro h; exact hclG.2.2.2.1 _ hsG _ h
    by_cases hx : x ∈ GM
    · have hx' := hmem.2 hx
      rw [hF, Set.indicator_of_mem hx', Set.indicator_of_mem hx]
      have hAeq : A (lmulM s x) = PiS ψ π s (A x) := by
        show be ψ π μS σ (σ (s * Matrix.of x) u) v ξ =
          PiS ψ π s (be ψ π μS σ (σ (Matrix.of x) u) v ξ)
        have hm : σ (s * Matrix.of x) = (σ s).comp (σ (Matrix.of x)) := hrep.1.2 s hsG _ hx
        have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
        have he := ((hD1 _ hxu).2.1 s hs).1
        rw [hm]
        show be ψ π μS σ (σ s (σ (Matrix.of x) u)) v ξ = _
        rw [he]; rfl
      have hn : ‖PiS ψ π s (A x)‖₊ = ‖A x‖₊ := Subtype.ext (hPi.2.1 s hs _)
      rw [hAeq, hn]
    · have hx' : lmulM s x ∉ GM := fun h => hx (hmem.1 h)
      rw [hF, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  obtain ⟨-, -, hL2, hnorm, hb0, hbim⟩ := hD3 u hu
  have hint : Integrable (fun x => ‖A x‖ ^ 2) ν := hL2.integrable_norm_pow (by norm_num)
  have hval : ∫ x, ‖A x‖ ^ 2 ∂ν = ‖u‖ ^ 2 * bc.re / d := by
    have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h2 : bc = (bc.re : ℂ) := by
      apply Complex.ext <;> simp [hbim]
    have h3 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h4 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖u‖ ^ 2 * bc.re / d : ℝ) : ℂ) := by
      rw [← h1]
      refine hnorm.trans ?_
      rw [h3]
      push_cast
      rw [← h2]
    exact_mod_cast h4
  have hlin : ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν = ENNReal.ofReal (‖u‖ ^ 2 * bc.re / d) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ofReal_norm_eq_enorm]
  calc ∫⁻ x in K, (‖A x‖₊ : ENNReal) ^ 2 ∂μG = ∫⁻ x in K, F x ∂μG := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        rw [hF, Set.indicator_of_mem hx]
    _ ≤ C₀ * ∫⁻ x, F x ∂ν := hC F hFm hFinv
    _ ≤ C₀ * ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν := by
        refine mul_le_mul_right ?_ _
        exact lintegral_mono fun x => Set.indicator_le_self _ _ x
    _ = ENNReal.ofReal (C₀.toReal * bc.re / d * ‖u‖ ^ 2) := by
        rw [hlin]
        have hC₁ : C₀ = ENNReal.ofReal C₀.toReal := (ENNReal.ofReal_toReal hC₀.ne).symm
        conv_lhs => rw [hC₁]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        congr 1; ring

end GlobalTheory.SgInf
end

